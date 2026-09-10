import Leanactors.Fair
import Leanactors.Examples.SupervisorProof
/-!
# Leanactors.Examples.SupervisorLive

**Liveness of the supervisor.** `SupervisorProof.restart_in_flight` is a
safety fact: whenever the current child is dead, either its exit signal is
pending or its `EXIT` message is already in the supervisor's mailbox. This
file adds the fairness assumptions that turn "in flight" into "arrives":

`restart_eventually`: along any run `ρ` of the supervisor system from
`init` in which the `signal` step and the `run 0` step are weakly fair, if
at time `t` the current child is dead then at some `t' ≥ t` the supervisor
has a live child again.

No fairness of `down` or of the timers is needed (the supervisor has no
monitors and arms no timers), and `NoKillTo 0` is not an assumption: it is
an invariant from `init`, as in `SupervisorProof`.

The proof is two `LeadsTo` stages, each by `SysRun.rank_leads_to`:

* **Stage A** (`sigPending_leadsTo`): a pending signal `(0, c, r)` leads to
  a live child or to `EXIT c r` in the supervisor's mailbox. The signal
  queue is FIFO and the pending signal need not be its head, so the rank
  is the *position* of the first signal addressed to `0` from `c`
  (`rankSig`, a `List.findIdx`). Every step only appends to the queue or
  pops its head, so the rank never increases, and a `signal` step strictly
  decreases it (or delivers the signal, which is the goal).
* **Stage B** (`msgPending_leadsTo`): `EXIT c r` in the mailbox leads to a
  live child. The rank is the position of the first `EXIT c _` in the
  supervisor's mailbox (`rankMsg`). Steps by other actors, signal
  deliveries and timers only append to that mailbox; a `run 0` step pops
  its head, which either is the `EXIT` (and the supervisor spawns a live
  child) or is not (the supervisor's state does not change and the rank
  drops by one).

The generic facts these need (a `runE` by `p` only appends to any other
live mailbox and only appends to `signals`; `signalE` pops the head and
appends; `downE`/`timerE` only append to mailboxes) are proved here in
`Leanactors.Sys` for any `σ μ`, as is `SysRun.rank_leads_to_of_step`, a
form of `rank_leads_to` whose single step hypothesis is stated for the
labelled step and returns `Q b ∨ (P b ∧ bounds)`.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors

/-! ## Two `findIdx` facts -/

theorem List.findIdx_append_of_mem {α : Type} {l₁ l₂ : List α} {p : α → Bool}
    (h : ∃ x ∈ l₁, p x = true) : (l₁ ++ l₂).findIdx p = l₁.findIdx p := by
  induction l₁ with
  | nil => obtain ⟨x, hx, _⟩ := h; cases hx
  | cons a l ih =>
    simp only [List.cons_append, List.findIdx_cons]
    cases hpa : p a with
    | true => rfl
    | false =>
      simp only [cond_false]
      congr 1
      apply ih
      obtain ⟨x, hx, hpx⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hpa] at hpx; cases hpx
      · exact ⟨x, hx, hpx⟩

theorem List.findIdx_cons_of_false {α : Type} {a : α} {l : List α} {p : α → Bool}
    (h : p a = false) : (a :: l).findIdx p = l.findIdx p + 1 := by
  simp [List.findIdx_cons, h]

/-! ## Generic `Sys` plumbing: mailboxes and signals only grow -/

variable {σ μ : Type}

namespace Config

theorem mboxOf_remove_ne (c : Config σ μ) {p q : Pid} (h : q ≠ p) :
    (c.remove p).mboxOf q = c.mboxOf q := by
  unfold mboxOf; rw [get_remove_ne _ h]

end Config

namespace Sys

open Config

/-- Below the fresh counter, one effect only appends to a mailbox. -/
theorem mboxOf_applyEffect_append (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ)
    {q : Pid} (hq : q < s.next) :
    ∃ new, (applyEffect p (s, d) e).1.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) := by
  have hne : q ≠ s.next := Nat.ne_of_lt hq
  cases e with
  | send to m => exact mboxOf_deliver s.cfg to q m
  | spawn init | spawnLink init | spawnMonitor init =>
    exact ⟨[], by simp [applyEffect, mboxOf_set, hne]⟩
  | link q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | monitor q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | sendAfter to m => exact ⟨[], by simp [applyEffect]⟩
  | signal q' r => exact ⟨[], by simp [applyEffect]⟩
  | exit r => exact ⟨[], by simp [applyEffect]⟩

theorem mboxOf_foldl_applyEffect_append (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) {q : Pid} (hq : q < s.next) :
    ∃ new, (effs.foldl (applyEffect p) (s, d)).1.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) := by
  induction effs generalizing s d with
  | nil => exact ⟨[], by simp⟩
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h1 := mboxOf_applyEffect_append p s d e hq
    have hn := (applyEffect_grows p s d e).next
    revert h1 hn
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h1 hn
    obtain ⟨n1, h1⟩ := h1
    obtain ⟨n2, h2⟩ := ih s1 d1 (Nat.lt_of_lt_of_le hq hn)
    refine ⟨n1 ++ n2, ?_⟩
    rw [h2, h1, Option.map_map]
    congr 1
    funext l
    simp [Function.comp, List.append_assoc]

theorem mboxOf_applyEffects_append (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) {q : Pid}
    (hq : q < s.next) :
    ∃ new, (applyEffects p s effs).1.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) :=
  mboxOf_foldl_applyEffect_append p effs s none hq

/-- A `runE` by `p` only appends to the mailbox of any other pid below the counter. -/
theorem mboxOf_runE_append {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') {q : Pid} (hq : q ≠ p) (hlt : q < s.next) :
    ∃ new, s'.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  obtain ⟨new, hnew⟩ := mboxOf_applyEffects_append p
    { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } (beh p s.next st m).2 (q := q) hlt
  simp only [mboxOf_set, if_neg hq] at hnew
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨new, hnew⟩
  · exact ⟨new, by
      show (Sys.cfg _).mboxOf q = _
      simp only [terminate]
      rw [mboxOf_remove_ne _ hq]; exact hnew⟩

/-- One effect only appends to `signals`. -/
theorem signals_applyEffect_append (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) :
    ∃ new, (applyEffect p (s, d) e).1.signals = s.signals ++ new := by
  cases e with
  | link q' =>
    simp only [applyEffect]
    split
    · exact ⟨[], by simp⟩
    · exact ⟨_, rfl⟩
  | monitor q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | signal q' r => exact ⟨_, rfl⟩
  | _ => exact ⟨[], by simp [applyEffect]⟩

theorem signals_foldl_applyEffect_append (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) :
    ∃ new, (effs.foldl (applyEffect p) (s, d)).1.signals = s.signals ++ new := by
  induction effs generalizing s d with
  | nil => exact ⟨[], by simp⟩
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h1 := signals_applyEffect_append p s d e
    revert h1
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h1
    obtain ⟨n1, h1⟩ := h1
    obtain ⟨n2, h2⟩ := ih s1 d1
    exact ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc]⟩

theorem signals_applyEffects_append (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) :
    ∃ new, (applyEffects p s effs).1.signals = s.signals ++ new :=
  signals_foldl_applyEffect_append p effs s none

/-- A `runE` only appends to `signals`. -/
theorem runE_signals_append {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') : ∃ new, s'.signals = s.signals ++ new := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  obtain ⟨new, hnew⟩ := signals_applyEffects_append p
    { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } (beh p s.next st m).2
  simp only at hnew
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨new, hnew⟩
  · exact ⟨_, by rw [terminate_signals, hnew, List.append_assoc]⟩

/-- A DOWN delivery only appends to any mailbox. -/
theorem mboxOf_downE_append {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s')
    (q : Pid) : ∃ new, s'.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) := by
  obtain ⟨w, t, r, rest, _, hc⟩ := downE_cases h
  rcases hc with ⟨codec, _, _, rfl⟩ | rfl
  · exact mboxOf_deliver _ _ _ _
  · exact ⟨[], by simp⟩

/-- A timer firing only appends to any mailbox. -/
theorem mboxOf_timerE_append {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') (q : Pid) :
    ∃ new, s'.cfg.mboxOf q = (s.cfg.mboxOf q).map (· ++ new) := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  exact mboxOf_deliver _ _ _ _

end Sys

/-! ## `rank_leads_to` from one labelled step lemma -/

namespace SysRun

variable {beh : EBehavior σ μ} {sig : Signals σ μ}

/-- `rank_leads_to` when one lemma covers every labelled step from a
`P ∧ ¬Q` state: it reaches `Q`, or stays in `P` without increasing the
rank, strictly decreasing it when the step is the fair choice `c`. -/
theorem rank_leads_to_of_step (ρ : SysRun beh sig) (c : SysChoice) (f : Sys σ μ → Nat)
    (hfair : ρ.WeakFair c) {P Q : Sys σ μ → Prop}
    (hstep : ∀ {ch a b}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig ch a b → P a → ¬ Q a →
      Q b ∨ (P b ∧ f b ≤ f a ∧ (ch = c → f b < f a)))
    (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c) :
    LeadsTo ρ.st P Q := by
  have h : LeadsTo ρ.st (fun s => P s ∧ ¬ Q s) Q := by
    apply ρ.rank_leads_to c f hfair
    · intro a b hr hs ⟨hp, hq⟩ _
      obtain ⟨ch, hl⟩ := hs.exists_sysStepL
      rcases hstep hr hl hp hq with hqb | ⟨hpb, _⟩
      · exact Or.inr hqb
      · by_cases hqb : Q b
        · exact Or.inr hqb
        · exact Or.inl ⟨hpb, hqb⟩
    · intro a b hr hs ⟨hp, hq⟩ _ ⟨_, hqb⟩
      obtain ⟨ch, hl⟩ := hs.exists_sysStepL
      rcases hstep hr hl hp hq with h | ⟨_, h, _⟩
      · exact absurd h hqb
      · exact h
    · intro a hr ⟨hp, hq⟩ _
      exact hen hr hp hq
    · intro a b hr hl ⟨hp, hq⟩ _ ⟨_, hqb⟩
      rcases hstep hr hl hp hq with h | ⟨_, _, h⟩
      · exact absurd h hqb
      · exact h rfl
  intro t hp
  by_cases hq : Q (ρ.st t)
  · exact Eventually.now hq
  · exact h t ⟨hp, hq⟩

end SysRun

/-! ## The supervisor -/

namespace Examples.Supervisor

open Leanactors Config Sys

/-- The supervisor has a live child. -/
def Live (s : Sys St Msg) : Prop :=
  ∃ c k, s.cfg.stateOf 0 = some (.sup (some c) k) ∧ ((s.cfg.get c).isSome = true)

/-- The supervisor's current child is `c`. -/
def SupChild (c : Pid) (s : Sys St Msg) : Prop := ∃ k, s.cfg.stateOf 0 = some (.sup (some c) k)

/-- The current child is `c` and its exit signal is pending. -/
def SigPending (c : Pid) (s : Sys St Msg) : Prop := SupChild c s ∧ ∃ r, (0, c, r) ∈ s.signals

/-- The current child is `c` and its `EXIT` is in the supervisor's mailbox. -/
def MsgPending (c : Pid) (s : Sys St Msg) : Prop :=
  SupChild c s ∧ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ ∃ r, (.EXIT c r : Msg) ∈ mb

/-- A signal addressed to the supervisor from `c`. -/
def isSig (c : Pid) (x : Pid × Pid × Reason) : Bool := decide (x.1 = 0 ∧ x.2.1 = c)

/-- The `EXIT` of `c`, whatever the reason. -/
def isExit (c : Pid) : Msg → Bool
  | .EXIT who _ => decide (who = c)
  | _ => false

/-- Stage A rank: how many signals are queued ahead of the first one from `c` to the supervisor. -/
def rankSig (c : Pid) (s : Sys St Msg) : Nat := s.signals.findIdx (isSig c)

/-- Stage B rank: how many messages are queued ahead of the first `EXIT c _` in the supervisor's mailbox. -/
def rankMsg (c : Pid) (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf 0 with
  | some mb => mb.findIdx (isExit c)
  | none => 0

theorem isSig_self (c : Pid) (r : Reason) : isSig c (0, c, r) = true := by simp [isSig]

theorem isExit_self (c : Pid) (r : Reason) : isExit c (.EXIT c r) = true := by simp [isExit]

theorem isExit_false {c : Pid} {m : Msg} (h : ∀ r, m ≠ .EXIT c r) : isExit c m = false := by
  cases m with
  | EXIT who r =>
    simp only [isExit, decide_eq_false_iff_not]
    intro hw; exact h r (by rw [hw])
  | _ => rfl

/-! ### The invariant along a run -/

/-- `Inv` together with `NoKillTo 0`, from `init` (the induction of `reach_inv`). -/
theorem reach_good {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s ∧ s.NoKillTo 0 :=
  hr.inv (I := fun s => Inv s ∧ s.NoKillTo 0)
    (fun h ⟨hi, hk⟩ => ⟨Inv.step h hi hk, noKillTo_step h hk⟩) ⟨init_inv, init_noKillTo⟩

theorem SupChild.get {c : Pid} {s : Sys St Msg} (h : SupChild c s) :
    ∃ k mb, s.cfg.get 0 = some ⟨.sup (some c) k, mb⟩ := by
  obtain ⟨k, hk⟩ := h
  unfold stateOf at hk
  cases hget : s.cfg.get 0 with
  | none => rw [hget] at hk; cases hk
  | some a =>
    rw [hget] at hk
    obtain ⟨st, mb⟩ := a
    simp at hk
    exact ⟨k, mb, by rw [hk]⟩

theorem SupChild.mboxOf {c : Pid} {s : Sys St Msg} (h : SupChild c s) :
    ∃ mb, s.cfg.mboxOf 0 = some mb := by
  obtain ⟨k, mb, hget⟩ := h.get
  exact ⟨mb, by simp [Config.mboxOf, hget]⟩

/-! ### The supervisor's own steps -/

/-- A `run 0` step while the child is `c`: the popped message is `EXIT c _`
and the supervisor spawns a fresh child, or it is not and the step only
pops the message. -/
theorem sup_run_cases {a b : Sys St Msg} {c : Pid} {k : Nat}
    (hc : a.cfg.stateOf 0 = some (.sup (some c) k)) (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.sup (some c) k, m :: rest⟩ ∧
      ((∃ r, m = .EXIT c r ∧
        b = { a with cfg := (a.cfg.set 0 ⟨.sup (some a.next) (k + 1), rest⟩).set a.next ⟨.worker 0, []⟩,
                     next := a.next + 1, links := (0, a.next) :: a.links }) ∨
       ((∀ r, m ≠ .EXIT c r) ∧ b = { a with cfg := a.cfg.set 0 ⟨.sup (some c) k, rest⟩ })) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · cases m with
    | EXIT who r =>
      by_cases hw : who = c
      · subst hw
        left
        refine ⟨r, rfl, ?_⟩
        simp only [beh, if_true, applyEffects, List.foldl, applyEffect]
      · right
        refine ⟨fun r' hr' => hw (by cases hr'; rfl), ?_⟩
        simp only [beh, hw, if_false, applyEffects, List.foldl]
    | _ =>
      right
      refine ⟨(fun _ h => nomatch h), ?_⟩
      simp only [beh, applyEffects, List.foldl]
  · exact absurd (applyEffects_snd_some _ _ _ hr) (sup_no_exit _ _ _ _ _ _)

/-- After the spawn, the supervisor has a live child. -/
theorem Live.spawn (a : Sys St Msg) (k : Nat) (rest : List Msg) (hn : 0 < a.next) :
    Live { a with cfg := (a.cfg.set 0 ⟨.sup (some a.next) k, rest⟩).set a.next ⟨.worker 0, []⟩,
                  next := a.next + 1, links := (0, a.next) :: a.links } := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hn
  exact ⟨a.next, k, by simp [stateOf_set, Ne.symm hn0], by simp [isSome_set]⟩

/-- A signal step in a good system: the supervisor's state is untouched,
the head signal is popped (and more may be appended), and the supervisor's
mailbox gains exactly the `EXIT` if the head was addressed to it, nothing
otherwise. -/
theorem sup_signal_cases {a b : Sys St Msg} (hi : Inv a) (hk : a.NoKillTo 0)
    (h : signalE sig a = some b) :
    ∃ q src r rest, a.signals = (q, src, r) :: rest ∧
      b.cfg.stateOf 0 = a.cfg.stateOf 0 ∧ (∃ new, b.signals = rest ++ new) ∧
      ((q = 0 ∧ b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ [.EXIT src r])) ∨
       (q ≠ 0 ∧ b.cfg.mboxOf 0 = a.cfg.mboxOf 0)) := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  refine ⟨q, src, r, rest, hsg, ?_⟩
  by_cases hq : q = 0
  · subst hq
    rcases hc with ⟨hd, _⟩ | ⟨act, hget, _, _, rfl⟩ | ⟨act, hget, htr, _, _⟩ | ⟨act, hget, htr, _, _⟩
      | ⟨_, _, rfl, _⟩
    · obtain ⟨_, _, hsup⟩ := hi.sup_alive
      simp [stateOf, hd] at hsup
    · refine ⟨stateOf_deliver _ _ _ _, ⟨[], by simp⟩, Or.inl ⟨rfl, ?_⟩⟩
      show (a.cfg.deliver 0 (sig.exitMsg src r)).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl]; rfl
    · rw [sup_traps hi hget] at htr; cases htr
    · rw [sup_traps hi hget] at htr; cases htr
    · exact absurd (by rw [hsg]; exact List.mem_cons_self) (hk src)
  · rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact ⟨rfl, ⟨[], by simp⟩, Or.inr ⟨hq, rfl⟩⟩
    · refine ⟨stateOf_deliver _ _ _ _, ⟨[], by simp⟩, Or.inr ⟨hq, ?_⟩⟩
      show (a.cfg.deliver q (sig.exitMsg src r)).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_neg (Ne.symm hq)]; simp
    · exact ⟨rfl, ⟨[], by simp⟩, Or.inr ⟨hq, rfl⟩⟩
    · exact ⟨terminate_stateOf_ne _ _ _ (Ne.symm hq), ⟨_, terminate_signals _ _ _⟩,
        Or.inr ⟨hq, by show (Sys.cfg _).mboxOf 0 = _; simp only [terminate]; exact mboxOf_remove_ne _ (Ne.symm hq)⟩⟩
    · exact ⟨terminate_stateOf_ne _ _ _ (Ne.symm hq), ⟨_, terminate_signals _ _ _⟩,
        Or.inr ⟨hq, by show (Sys.cfg _).mboxOf 0 = _; simp only [terminate]; exact mboxOf_remove_ne _ (Ne.symm hq)⟩⟩

/-! ### Stage A: the pending signal is delivered -/

theorem rankSig_append {c : Pid} {l new : List (Pid × Pid × Reason)} {r : Reason}
    (h : (0, c, r) ∈ l) : (l ++ new).findIdx (isSig c) = l.findIdx (isSig c) :=
  List.findIdx_append_of_mem ⟨_, h, isSig_self c r⟩

/-- One labelled step from a `SigPending c` state. -/
theorem sigPending_step {c : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Inv a ∧ a.NoKillTo 0)
    (h : SysStepL beh sig ch a b) (hp : SigPending c a) :
    (Live b ∨ MsgPending c b) ∨
      (SigPending c b ∧ rankSig c b ≤ rankSig c a ∧ (ch = .signal → rankSig c b < rankSig c a)) := by
  obtain ⟨hi, hk⟩ := hg
  obtain ⟨⟨k, hc⟩, r, hs⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := sup_run_cases hc hrun
      rcases hcase with ⟨r', _, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl (Or.inl (Live.spawn a _ rest hi.next_pos))
      · exact Or.inr ⟨⟨⟨k, by simp [stateOf_set]⟩, r, hs⟩, Nat.le_refl _, fun h => nomatch h⟩
    · obtain ⟨new, hnew⟩ := runE_signals_append hrun
      refine Or.inr ⟨⟨⟨k, ?_⟩, r, by rw [hnew]; exact List.mem_append_left _ hs⟩, ?_, fun h => nomatch h⟩
      · rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hc
      · unfold rankSig; rw [hnew, rankSig_append hs]; exact Nat.le_refl _
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, ⟨new, hnew⟩, hmb⟩ := sup_signal_cases hi hk hsig
    by_cases hhead : q = 0 ∧ src = c
    · obtain ⟨hq0, hsrc⟩ := hhead
      subst q; subst src
      rcases hmb with ⟨_, hmb⟩ | ⟨hne, _⟩
      · obtain ⟨mb, hmb'⟩ := SupChild.mboxOf (⟨k, hc⟩ : SupChild c a)
        refine Or.inl (Or.inr ⟨⟨k, by rw [hst]; exact hc⟩, mb ++ [.EXIT c r'], ?_, r', ?_⟩)
        · rw [hmb, hmb']; rfl
        · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd rfl hne
    · have hrest : (0, c, r) ∈ rest := by
        rw [hsg] at hs
        rcases List.mem_cons.mp hs with h | h
        · exact absurd ⟨(congrArg Prod.fst h).symm, (congrArg (·.2.1) h).symm⟩ hhead
        · exact h
      have hno : isSig c (q, src, r') = false := by
        simp only [isSig, decide_eq_false_iff_not]; exact hhead
      have hlt : rankSig c b < rankSig c a := by
        unfold rankSig
        rw [hnew, rankSig_append hrest, hsg, List.findIdx_cons_of_false hno]
        exact Nat.lt_succ_self _
      exact Or.inr ⟨⟨⟨k, by rw [hst]; exact hc⟩, r, by rw [hnew]; exact List.mem_append_left _ hrest⟩,
        Nat.le_of_lt hlt, fun _ => hlt⟩
  | down _ _ hdown =>
    refine Or.inr ⟨⟨⟨k, by rw [downE_stateOf hdown]; exact hc⟩, r, by rw [downE_signals hdown]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankSig; rw [downE_signals hdown]; exact Nat.le_refl _
  | timer _ i _ htimer =>
    refine Or.inr ⟨⟨⟨k, by rw [timerE_stateOf htimer]; exact hc⟩, r, by rw [timerE_signals htimer]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankSig; rw [timerE_signals htimer]; exact Nat.le_refl _

/-- **Stage A.** With a fair `signal` step, a pending exit signal of the
current child leads to a live child or to its `EXIT` in the mailbox. -/
theorem sigPending_leadsTo (ρ : SysRun beh sig) (h0 : ρ.st 0 = init) (hfair : ρ.WeakFair .signal)
    (c : Pid) : LeadsTo ρ.st (SigPending c) (fun s => Live s ∨ MsgPending c s) := by
  apply ρ.rank_leads_to_of_step .signal (rankSig c) hfair
  · intro ch a b hr hl hp _
    exact sigPending_step (reach_good (by rwa [h0] at hr)) hl hp
  · intro a _ ⟨_, r, hs⟩ _
    show a.signals ≠ []
    intro hnil; rw [hnil] at hs; cases hs

/-! ### Stage B: the `EXIT` message is processed -/

theorem rankMsg_append {c : Pid} {mb new : List Msg} {r : Reason} (h : (.EXIT c r : Msg) ∈ mb) :
    (mb ++ new).findIdx (isExit c) = mb.findIdx (isExit c) :=
  List.findIdx_append_of_mem ⟨_, h, isExit_self c r⟩

theorem rankMsg_of_mboxOf {c : Pid} {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf 0 = some mb) :
    rankMsg c s = mb.findIdx (isExit c) := by
  unfold rankMsg; rw [h]

/-- The mailbox of the supervisor only grew: `MsgPending` and the rank are kept. -/
theorem msgPending_grow {c : Pid} {a b : Sys St Msg} {k : Nat}
    (hc : b.cfg.stateOf 0 = some (.sup (some c) k))
    {mb : List Msg} (hmb : a.cfg.mboxOf 0 = some mb) {r : Reason} (hr : (.EXIT c r : Msg) ∈ mb)
    {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new)) :
    MsgPending c b ∧ rankMsg c b ≤ rankMsg c a := by
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  refine ⟨⟨⟨k, hc⟩, mb ++ new, hnew, r, List.mem_append_left _ hr⟩, ?_⟩
  rw [rankMsg_of_mboxOf hnew, rankMsg_of_mboxOf hmb, rankMsg_append hr]
  exact Nat.le_refl _

/-- One labelled step from a `MsgPending c` state. -/
theorem msgPending_step {c : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Inv a ∧ a.NoKillTo 0)
    (h : SysStepL beh sig ch a b) (hp : MsgPending c a) :
    Live b ∨ (MsgPending c b ∧ rankMsg c b ≤ rankMsg c a ∧ (ch = .run 0 → rankMsg c b < rankMsg c a)) := by
  obtain ⟨hi, hk⟩ := hg
  obtain ⟨⟨k, hc⟩, mb, hmb, r, hr⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := sup_run_cases hc hrun
      have hmb' : mb = m :: rest := by
        simp [Config.mboxOf, hget] at hmb; exact hmb.symm
      subst hmb'
      rcases hcase with ⟨r', _, rfl⟩ | ⟨hne, rfl⟩
      · exact Or.inl (Live.spawn a _ rest hi.next_pos)
      · have hrest : (.EXIT c r : Msg) ∈ rest := by
          rcases List.mem_cons.mp hr with h | h
          · exact absurd h.symm (hne r)
          · exact h
        have hmbb : ({ a with cfg := a.cfg.set 0 ⟨.sup (some c) k, rest⟩ } : Sys St Msg).cfg.mboxOf 0 = some rest := by
          simp [mboxOf_set]
        have hlt : rankMsg c { a with cfg := a.cfg.set 0 ⟨.sup (some c) k, rest⟩ } < rankMsg c a := by
          rw [rankMsg_of_mboxOf hmbb, rankMsg_of_mboxOf hmb, List.findIdx_cons_of_false (isExit_false hne)]
          exact Nat.lt_succ_self _
        exact Or.inr ⟨⟨⟨k, by simp [stateOf_set]⟩, rest, hmbb, r, hrest⟩, Nat.le_of_lt hlt, fun _ => hlt⟩
    · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp0) hi.next_pos
      have hc' : b.cfg.stateOf 0 = some (.sup (some c) k) := by
        rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hc
      obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => absurd (SysChoice.run.inj h) hp0⟩
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, _, hmbc⟩ := sup_signal_cases hi hk hsig
    have hc' : b.cfg.stateOf 0 = some (.sup (some c) k) := by rw [hst]; exact hc
    rcases hmbc with ⟨_, hnew⟩ | ⟨_, hnew⟩
    · obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
    · obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr (new := []) (by rw [hnew, hmb]; simp)
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | down _ _ hdown =>
    obtain ⟨new, hnew⟩ := mboxOf_downE_append hdown 0
    obtain ⟨h1, h2⟩ := msgPending_grow (by rw [downE_stateOf hdown]; exact hc) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
    obtain ⟨h1, h2⟩ := msgPending_grow (by rw [timerE_stateOf htimer]; exact hc) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage B.** With a fair `run 0` step, the child's `EXIT` in the
supervisor's mailbox leads to a live child. -/
theorem msgPending_leadsTo (ρ : SysRun beh sig) (h0 : ρ.st 0 = init) (hfair : ρ.WeakFair (.run 0))
    (c : Pid) : LeadsTo ρ.st (MsgPending c) Live := by
  apply ρ.rank_leads_to_of_step (.run 0) (rankMsg c) hfair
  · intro ch a b hr hl hp _
    exact msgPending_step (reach_good (by rwa [h0] at hr)) hl hp
  · intro a _ ⟨hsc, mb, hmb, r, hr⟩ _
    obtain ⟨k, mb', hget⟩ := hsc.get
    have : mb = mb' := by simp [Config.mboxOf, hget] at hmb; exact hmb.symm
    subst this
    cases mb with
    | nil => cases hr
    | cons m rest => exact ⟨_, m, rest, hget⟩

/-! ### The theorem -/

/-- **A dead child is eventually replaced.** Along any run from `init` in
which the `signal` step and the `run 0` step are weakly fair: if at time
`t` the supervisor's current child `c` is dead, then at some `t' ≥ t` the
supervisor's current child is alive. Nothing is assumed about `down`,
timers, the other pids, or who is killed: `NoKillTo 0` is an invariant. -/
theorem restart_eventually (ρ : SysRun beh sig) (h0 : ρ.st 0 = init)
    (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t c k, (ρ.st t).cfg.stateOf 0 = some (.sup (some c) k) → ((ρ.st t).cfg.get c).isSome = false →
      ∃ t' ≥ t, ∃ c' k', (ρ.st t').cfg.stateOf 0 = some (.sup (some c') k') ∧
        ((ρ.st t').cfg.get c').isSome = true := by
  intro t c k hc hdead
  have hr : SysReach beh sig init (ρ.st t) := by have h := ρ.reach t; rwa [h0] at h
  have hB := msgPending_leadsTo ρ h0 hrun c
  have hA := (sigPending_leadsTo ρ h0 hsig c).trans ((LeadsTo.refl ρ.st Live).or hB)
  rcases restart_in_flight hr hc hdead with ⟨r, hs⟩ | ⟨r, hm⟩
  · exact hA t ⟨⟨k, hc⟩, r, hs⟩
  · refine hB t ⟨⟨k, hc⟩, ?_⟩
    obtain ⟨_, mb, hget⟩ := SupChild.get (⟨k, hc⟩ : SupChild c (ρ.st t))
    refine ⟨mb, by simp [Config.mboxOf, hget], r, ?_⟩
    unfold mcount at hm
    rw [hget] at hm
    exact List.count_pos_iff.mp hm

end Examples.Supervisor

end Leanactors
