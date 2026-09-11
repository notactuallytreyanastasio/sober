import Leanactors.Fair
import Leanactors.Examples.SupervisorLive
import Leanactors.Examples.TaskProof
/-!
# Leanactors.Examples.TaskLive

**Liveness of the task.** `TaskProof.job_never_lost` is a safety fact:
while the caller waits on a dead worker `w`, `w`'s DOWN is queued or the
reply or the DOWN message is already in the caller's mailbox. This file
adds the fairness that turns "queued" into "consumed":

* `job_eventually_settles_dead` (closed `SysRun`, unconditional): from any
  `Good` system, under weak fairness of the `down` step and of `run 0`, if
  at time `t` the caller waits on `w` and `w` is dead, then at some
  `t' ≥ t` the caller has no pending job.
* `job_eventually_settles` (open `SysRunE`, conditional): the same premise
  without "`w` is dead". A live worker acts only when the environment
  sends it `compute` or `crash`, and a `SysRun` is closed, so this is
  stated along a `SysRunE beh sig Sys.Deliver` (new in `Fair.lean`: a run
  in which the environment may deliver any message at any time) and
  assumes, besides `down` and `run 0`, weak fairness of `run w` and
  `ρ.EnvFair (Alive w) (Kick w)`: *if the caller keeps waiting on a live,
  monitored `w` from some time on, the environment eventually delivers
  `compute` or `crash` to `w`*. Nothing else is assumed of the
  environment: it may send anything to anyone in between.

`Good` is `Inv` (from `TaskProof`), `Fresh` (pids at or above the counter
are dead, so a live pid is below it and the frame lemmas apply) and
`Shape` (every pid other than the caller is a `worker`, and the pending
pid is never the caller itself); all three are kept by every step and
every delivery, so every system the environment can drive the task to
from `init` is `Good` (`reachEnv_good`).

Four `LeadsTo` stages, each on one fair choice:

* **Stage 1** (`alive_leadsTo`, `stable_until_env` on the kick): the
  caller waits on a live monitored `w` ⟶ `w` has a kick in its mailbox
  (`Armed`), or `w`'s DOWN is queued, or the caller has settled.
* **Stage 2** (`armed_leadsTo`, rank = position of the first kick in `w`'s
  mailbox, fair `run w`): `Armed` ⟶ DOWN queued or settled. `run w` pops
  the head: a kick makes the worker exit (`compute` also sends the reply),
  and the caller's monitor turns the exit into a queued DOWN; anything
  else is ignored and the rank drops.
* **Stage 3** (`downPending_leadsTo`, rank = position of the first
  `(0, w, _)` in the FIFO `downs`, fair `down`): DOWN queued ⟶ a settling
  message (`reply _` or `DOWN w _`) in the caller's mailbox, or settled.
* **Stage 4** (`msgPending_leadsTo`, rank = position of the first settling
  message in the caller's mailbox, fair `run 0`): ⟶ settled. Every other
  step only appends to that mailbox; `run 0` pops the head, which settles
  the caller or is ignored (a `go`, a kick, another pid's DOWN).

`job_never_lost` places a dead worker in stage 3 or 4, so the closed
theorem needs no environment and follows from the open one through
`SysRun.toE`. The non-vacuity witnesses are at the end:
`dead_worker_reachable` / `live_worker_reachable` (the premises are
reachable from `init`) and `deadRun` / `liveRun`, explicit runs from
those systems that satisfy every fairness assumption and settle.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors

variable {σ μ : Type}

/-! ## Generic `Sys` plumbing: the DOWN queue only grows -/

namespace Sys

/-- One effect only appends to `downs`. -/
theorem downs_applyEffect_append (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) :
    ∃ new, (applyEffect p (s, d) e).1.downs = s.downs ++ new := by
  cases e with
  | link q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | monitor q' =>
    simp only [applyEffect]
    split
    · exact ⟨[], by simp⟩
    · exact ⟨_, rfl⟩
  | _ => exact ⟨[], by simp [applyEffect]⟩

theorem downs_foldl_applyEffect_append (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) :
    ∃ new, (effs.foldl (applyEffect p) (s, d)).1.downs = s.downs ++ new := by
  induction effs generalizing s d with
  | nil => exact ⟨[], by simp⟩
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h1 := downs_applyEffect_append p s d e
    revert h1
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h1
    obtain ⟨n1, h1⟩ := h1
    obtain ⟨n2, h2⟩ := ih s1 d1
    exact ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc]⟩

theorem downs_applyEffects_append (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) :
    ∃ new, (applyEffects p s effs).1.downs = s.downs ++ new :=
  downs_foldl_applyEffect_append p effs s none

/-- A `runE` only appends to `downs`. -/
theorem runE_downs_append {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') : ∃ new, s'.downs = s.downs ++ new := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  obtain ⟨new, hnew⟩ := downs_applyEffects_append p
    { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } (beh p s.next st m).2
  simp only at hnew
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨new, hnew⟩
  · exact ⟨_, by rw [terminate_downs, hnew, List.append_assoc]⟩

theorem timerE_downs {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') :
    s'.downs = s.downs := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  rfl

end Sys

/-! ## `rank_leads_to` from one labelled step lemma, open runs -/

namespace SysRunE

variable {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}

/-- `rank_leads_to_sys` when one lemma covers every system step from a
`P ∧ ¬Q` state and one every environment step (see
`SysRun.rank_leads_to_of_step`). -/
theorem rank_leads_to_of_step (ρ : SysRunE beh sig env) (c : SysChoice) (f : Sys σ μ → Nat)
    (hfair : ρ.WeakFair c) {P Q : Sys σ μ → Prop}
    (hstep : ∀ {ch a b}, SysReachE beh sig env (ρ.st 0) a → SysStepL beh sig ch a b → P a → ¬ Q a →
      Q b ∨ (P b ∧ f b ≤ f a ∧ (ch = c → f b < f a)))
    (henv : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → P a → ¬ Q a →
      Q b ∨ (P b ∧ f b ≤ f a))
    (hen : ∀ {a}, SysReachE beh sig env (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c) :
    LeadsTo ρ.st P Q := by
  have h : LeadsTo ρ.st (fun s => P s ∧ ¬ Q s) Q := by
    apply ρ.rank_leads_to_sys c f hfair
    · intro a b hr hs ⟨hp, hq⟩ _
      obtain ⟨ch, hl⟩ := hs.exists_sysStepL
      rcases hstep hr hl hp hq with hqb | ⟨hpb, _⟩
      · exact Or.inr hqb
      · by_cases hqb : Q b
        · exact Or.inr hqb
        · exact Or.inl ⟨hpb, hqb⟩
    · intro a b hr he ⟨hp, hq⟩ _
      rcases henv hr he hp hq with hqb | ⟨hpb, _⟩
      · exact Or.inr hqb
      · by_cases hqb : Q b
        · exact Or.inr hqb
        · exact Or.inl ⟨hpb, hqb⟩
    · intro ch a b hr hs ⟨hp, hq⟩ _ ⟨_, hqb⟩
      cases hs with
      | sys _ _ _ hl =>
        rcases hstep hr hl hp hq with h | ⟨_, h, _⟩
        · exact absurd h hqb
        · exact h
      | env _ _ he =>
        rcases henv hr he hp hq with h | ⟨_, h⟩
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

end SysRunE

/-! ## The task -/

namespace Examples.Task

open Leanactors Config Sys

/-! ### Predicates and ranks -/

/-- The caller is waiting on `w`. -/
def Pending (w : Pid) (s : Sys St Msg) : Prop :=
  ∃ r, s.cfg.stateOf 0 = some (.caller (some w) r)

/-- The caller has no pending job. -/
def Settled (s : Sys St Msg) : Prop := ∃ r, s.cfg.stateOf 0 = some (.caller none r)

/-- A message that settles the caller waiting on `w`: any reply, or `w`'s DOWN. -/
def isSettle (w : Pid) : Msg → Bool
  | .reply _ => true
  | .DOWN who _ => decide (who = w)
  | _ => false

/-- A message that makes a worker act: `compute` or `crash`. -/
def isKick : Msg → Bool
  | .compute => true
  | .crash => true
  | _ => false

/-- A queued DOWN of `w` addressed to the caller. -/
def isDown (w : Pid) (x : Pid × Pid × Reason) : Bool := decide (x.1 = 0 ∧ x.2.1 = w)

/-- The caller waits on `w` and a settling message is in its mailbox. -/
def MsgPending (w : Pid) (s : Sys St Msg) : Prop :=
  Pending w s ∧ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ ∃ m ∈ mb, isSettle w m = true

/-- The caller waits on `w` and `w`'s DOWN is queued. -/
def DownPending (w : Pid) (s : Sys St Msg) : Prop :=
  Pending w s ∧ ∃ rs, (0, w, rs) ∈ s.downs

/-- The caller waits on `w`, which is alive and monitored. -/
def Alive (w : Pid) (s : Sys St Msg) : Prop :=
  Pending w s ∧ (s.cfg.get w).isSome = true ∧ (0, w) ∈ s.monitors

/-- `Alive`, and `w` has a kick in its mailbox. -/
def Armed (w : Pid) (s : Sys St Msg) : Prop :=
  Alive w s ∧ ∃ mb, s.cfg.mboxOf w = some mb ∧ ∃ m ∈ mb, isKick m = true

/-- The environment kicks `w`: it delivers `compute` or `crash` to it. -/
def Kick (w : Pid) (a b : Sys St Msg) : Prop :=
  b = { a with cfg := a.cfg.deliver w .compute } ∨ b = { a with cfg := a.cfg.deliver w .crash }

/-- Stage 3 rank: DOWNs queued ahead of the first `(0, w, _)`. -/
def rankDown (w : Pid) (s : Sys St Msg) : Nat := s.downs.findIdx (isDown w)

/-- Stage 4 rank: messages ahead of the first settling one in the caller's mailbox. -/
def rankMsg (w : Pid) (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf 0 with
  | some mb => mb.findIdx (isSettle w)
  | none => 0

/-- Stage 2 rank: messages ahead of the first kick in `w`'s mailbox. -/
def rankKick (w : Pid) (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf w with
  | some mb => mb.findIdx isKick
  | none => 0

theorem isDown_self (w : Pid) (rs : Reason) : isDown w (0, w, rs) = true := by simp [isDown]

theorem isSettle_reply (w : Pid) (v : Nat) : isSettle w (.reply v) = true := rfl

theorem isSettle_down (w : Pid) (rs : Reason) : isSettle w (.DOWN w rs) = true := by simp [isSettle]

theorem rankMsg_of_mboxOf {w : Pid} {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf 0 = some mb) :
    rankMsg w s = mb.findIdx (isSettle w) := by
  unfold rankMsg; rw [h]

theorem rankKick_of_mboxOf {w : Pid} {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf w = some mb) :
    rankKick w s = mb.findIdx isKick := by
  unfold rankKick; rw [h]

theorem Pending.get {w : Pid} {s : Sys St Msg} (h : Pending w s) :
    ∃ r mb, s.cfg.get 0 = some ⟨.caller (some w) r, mb⟩ := by
  obtain ⟨r, hr⟩ := h
  unfold stateOf at hr
  cases hget : s.cfg.get 0 with
  | none => rw [hget] at hr; cases hr
  | some a =>
    rw [hget] at hr
    obtain ⟨st, mb⟩ := a
    simp at hr
    exact ⟨r, mb, by rw [hr]⟩

theorem Pending.mboxOf {w : Pid} {s : Sys St Msg} (h : Pending w s) :
    ∃ mb, s.cfg.mboxOf 0 = some mb := by
  obtain ⟨r, mb, hget⟩ := h.get
  exact ⟨mb, by simp [Config.mboxOf, hget]⟩

theorem Pending.of_stateOf_eq {w : Pid} {a b : Sys St Msg} (h : b.cfg.stateOf 0 = a.cfg.stateOf 0)
    (hp : Pending w a) : Pending w b := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, by rw [h]; exact hr⟩

theorem mboxOf_of_isSome {s : Sys St Msg} {w : Pid} (h : (s.cfg.get w).isSome = true) :
    ∃ mb, s.cfg.mboxOf w = some mb := by
  cases hget : s.cfg.get w with
  | none => rw [hget] at h; cases h
  | some a => exact ⟨a.mailbox, by simp [Config.mboxOf, hget]⟩

/-! ### The invariant along a run -/

/-- What the liveness argument needs beyond `Inv`: every pid other than the
caller is a worker (so a kick makes it exit), and the pending pid is never
the caller itself. -/
structure Shape (s : Sys St Msg) : Prop where
  workers : ∀ p x, p ≠ 0 → s.cfg.stateOf p = some x → ∃ q n, x = .worker q n
  pending_ne : ∀ w r, s.cfg.stateOf 0 = some (.caller (some w) r) → w ≠ 0

def Good (s : Sys St Msg) : Prop := Inv s ∧ s.Fresh ∧ Shape s

/-- `Inv` says `signals = []`, so no signal step is ever enabled. -/
theorem no_signal {a b : Sys St Msg} (hi : Inv a) (h : signalE sig a = some b) : False := by
  obtain ⟨_, _, _, _, hsg, _⟩ := signalE_cases h
  rw [hi.signals_nil] at hsg
  cases hsg

/-- A worker keeps its state on every message. -/
theorem worker_beh_fst (me fresh q n : Pid) (m : Msg) : (beh me fresh (.worker q n) m).1 = .worker q n := by
  cases m <;> rfl

/-- A worker never spawns. -/
theorem worker_beh_init (me fresh q n : Pid) (m : Msg) :
    ∀ e ∈ (beh me fresh (.worker q n) m).2, e.init? = none := by
  cases m <;> simp [beh, Effect.init?]

/-- The system after the caller's spawn step (`Inv.caller_spawn`). -/
def spawnSys (a : Sys St Msg) (r : Nat) (rest : List Msg) : Sys St Msg :=
  { a with cfg := (a.cfg.set 0 ⟨.caller (some a.next) r, rest⟩).set a.next ⟨.worker 0 0, []⟩,
           next := a.next + 1, monitors := (0, a.next) :: a.monitors }

/-- A `run 0` step while the caller is idle: on `go` it spawns, on anything
else it stays idle. -/
theorem caller_run_idle {a b : Sys St Msg} {r : Nat} (hc : a.cfg.stateOf 0 = some (.caller none r))
    (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.caller none r, m :: rest⟩ ∧
      ((m = .go ∧ b = spawnSys a r rest) ∨
       (∃ r', b = { a with cfg := a.cfg.set 0 ⟨.caller none r', rest⟩ })) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · cases m with
    | go =>
      left
      refine ⟨rfl, ?_⟩
      simp only [beh, applyEffects, List.foldl, applyEffect, get_set_self, Option.isSome_some, if_true]
      rfl
    | reply v => right; exact ⟨r + 1, by simp only [beh, applyEffects, List.foldl]⟩
    | DOWN who rs => right; exact ⟨r, by simp only [beh, applyEffects, List.foldl]⟩
    | compute => right; exact ⟨r, by simp only [beh, applyEffects, List.foldl]⟩
    | crash => right; exact ⟨r, by simp only [beh, applyEffects, List.foldl]⟩
  · exact absurd (applyEffects_snd_some _ _ _ hr) (caller_no_exit _ _ _ _ _ _)

/-- A `run 0` step while the caller waits on `w`: the popped message
settles it, or is ignored. -/
theorem caller_run_pending {a b : Sys St Msg} {w : Pid} {r : Nat}
    (hc : a.cfg.stateOf 0 = some (.caller (some w) r)) (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.caller (some w) r, m :: rest⟩ ∧
      ((isSettle w m = true ∧ ∃ r', b = { a with cfg := a.cfg.set 0 ⟨.caller none r', rest⟩ }) ∨
       (isSettle w m = false ∧ b = { a with cfg := a.cfg.set 0 ⟨.caller (some w) r, rest⟩ })) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · cases m with
    | go => right; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
    | reply v => left; exact ⟨rfl, r + 1, by simp only [beh, applyEffects, List.foldl]⟩
    | DOWN who rs =>
      by_cases hw : who = w
      · subst hw
        left
        exact ⟨isSettle_down _ _, r, by simp only [beh, if_true, applyEffects, List.foldl]⟩
      · right
        exact ⟨by simp [isSettle, hw], by simp only [beh, hw, if_false, applyEffects, List.foldl]⟩
    | compute => right; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
    | crash => right; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
  · exact absurd (applyEffects_snd_some _ _ _ hr) (caller_no_exit _ _ _ _ _ _)

/-- A `run w` step of a worker: a kick makes it exit (`compute` also
replies to its parent), anything else is ignored. -/
theorem worker_run {a b : Sys St Msg} {w q n : Pid} (hw : a.cfg.stateOf w = some (.worker q n))
    (h : runE beh a w = some b) :
    ∃ m rest, a.cfg.get w = some ⟨.worker q n, m :: rest⟩ ∧
      ((isKick m = false ∧ b = { a with cfg := a.cfg.set w ⟨.worker q n, rest⟩ }) ∨
       (m = .compute ∧
         b = ({ a with cfg := (a.cfg.set w ⟨.worker q n, rest⟩).deliver q (.reply (n + 1)) }).terminate w .normal) ∨
       (m = .crash ∧ b = ({ a with cfg := a.cfg.set w ⟨.worker q n, rest⟩ }).terminate w .error)) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hw
  subst hw
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  cases m with
  | compute =>
    rcases hs' with ⟨hn, _⟩ | ⟨reason, hr, rfl⟩
    · simp [beh, applyEffects, List.foldl, applyEffect] at hn
    · simp [beh, applyEffects, List.foldl, applyEffect] at hr
      subst hr
      right; left
      exact ⟨rfl, rfl⟩
  | crash =>
    rcases hs' with ⟨hn, _⟩ | ⟨reason, hr, rfl⟩
    · simp [beh, applyEffects, List.foldl, applyEffect] at hn
    · simp [beh, applyEffects, List.foldl, applyEffect] at hr
      subst hr
      right; right
      exact ⟨rfl, rfl⟩
  | go =>
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · left; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
    · simp [beh, applyEffects, List.foldl] at hr
  | reply v =>
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · left; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
    · simp [beh, applyEffects, List.foldl] at hr
  | DOWN who rs =>
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · left; exact ⟨rfl, by simp only [beh, applyEffects, List.foldl]⟩
    · simp [beh, applyEffects, List.foldl] at hr

theorem spawnSys_stateOf_zero (a : Sys St Msg) (r : Nat) (rest : List Msg) (hn : 0 < a.next) :
    (spawnSys a r rest).cfg.stateOf 0 = some (.caller (some a.next) r) := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hn
  simp [spawnSys, stateOf_set, Ne.symm hn0]

theorem spawnSys_stateOf_ne (a : Sys St Msg) (r : Nat) (rest : List Msg) {q : Pid} (hq : q ≠ 0) :
    (spawnSys a r rest).cfg.stateOf q =
      if q = a.next then some (.worker 0 0) else a.cfg.stateOf q := by
  simp [spawnSys, stateOf_set, hq]

theorem Shape.step {a b : Sys St Msg} (hi : Inv a) (h : SysStep beh sig a b) (hs : Shape a) :
    Shape b := by
  cases h with
  | run p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨w₀, r₀, hcal⟩ := hi.caller_alive
      cases w₀ with
      | none =>
        obtain ⟨m, rest, hget, hcase⟩ := caller_run_idle hcal hrun
        rcases hcase with ⟨_, rfl⟩ | ⟨r', rfl⟩
        · refine ⟨fun q x hq hx => ?_, fun w r hc => ?_⟩
          · rw [spawnSys_stateOf_ne _ _ _ hq] at hx
            split at hx
            · exact ⟨0, 0, (Option.some.inj hx).symm⟩
            · exact hs.workers q x hq hx
          · rw [spawnSys_stateOf_zero _ _ _ hi.next_pos] at hc
            simp at hc
            rw [← hc.1]
            exact Nat.ne_of_gt hi.next_pos
        · refine ⟨fun q x hq hx => ?_, fun w r hc => ?_⟩
          · simp only [stateOf_set, hq, if_false] at hx
            exact hs.workers q x hq hx
          · simp [stateOf_set] at hc
      | some w₀ =>
        obtain ⟨m, rest, hget, hcase⟩ := caller_run_pending hcal hrun
        rcases hcase with ⟨_, r', rfl⟩ | ⟨_, rfl⟩
        · refine ⟨fun q x hq hx => ?_, fun w r hc => ?_⟩
          · simp only [stateOf_set, hq, if_false] at hx
            exact hs.workers q x hq hx
          · simp [stateOf_set] at hc
        · refine ⟨fun q x hq hx => ?_, fun w r hc => ?_⟩
          · simp only [stateOf_set, hq, if_false] at hx
            exact hs.workers q x hq hx
          · simp [stateOf_set] at hc
            rw [← hc.1]
            exact hs.pending_ne w₀ r₀ hcal
    · have h0 : b.cfg.stateOf 0 = a.cfg.stateOf 0 := runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos
      refine ⟨fun q x hq hx => ?_, fun w r hc => hs.pending_ne w r (by rw [← h0]; exact hc)⟩
      rcases runE_stateOf_spawn_cases hrun q with h | h | ⟨st, m, rest, hget, rfl, h⟩ | ⟨st, m, rest, hget, e, he, h⟩
      · rw [h] at hx; exact hs.workers q x hq hx
      · rw [h] at hx; cases hx
      · obtain ⟨q', n, rfl⟩ := hs.workers q st hq (by simp [stateOf, hget])
        rw [h, worker_beh_fst] at hx
        exact ⟨q', n, (Option.some.inj hx).symm⟩
      · obtain ⟨q', n, rfl⟩ := hs.workers p st hp0 (by simp [stateOf, hget])
        rw [worker_beh_init _ _ _ _ _ e he, hx] at h
        cases h
  | signal _ hsig => exact absurd hsig (no_signal hi)
  | down _ hdown =>
    exact ⟨fun q x hq hx => hs.workers q x hq (by rw [← downE_stateOf hdown]; exact hx),
      fun w r hc => hs.pending_ne w r (by rw [← downE_stateOf hdown]; exact hc)⟩
  | timer i _ htimer =>
    exact ⟨fun q x hq hx => hs.workers q x hq (by rw [← timerE_stateOf htimer]; exact hx),
      fun w r hc => hs.pending_ne w r (by rw [← timerE_stateOf htimer]; exact hc)⟩

theorem Shape.deliver {a : Sys St Msg} (p : Pid) (m : Msg) (hs : Shape a) :
    Shape { a with cfg := a.cfg.deliver p m } :=
  ⟨fun q x hq hx => hs.workers q x hq (by rw [← stateOf_deliver a.cfg p q m]; exact hx),
   fun w r hc => hs.pending_ne w r (by rw [← stateOf_deliver a.cfg p 0 m]; exact hc)⟩

theorem Good.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hg : Good a) : Good b :=
  ⟨Inv.step h hg.1, h.fresh hg.2.1, hg.2.2.step hg.1 h⟩

theorem Good.deliver {a : Sys St Msg} (p : Pid) (m : Msg) (hg : Good a) :
    Good { a with cfg := a.cfg.deliver p m } :=
  ⟨hg.1.grows (grows_deliver a p m) hg.1.links_nil hg.1.signals_nil, fresh_deliver hg.2.1 p m,
   hg.2.2.deliver p m⟩

theorem init_fresh : Fresh init := by
  intro q hq
  have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  simp [init, Config.get, hq0]

theorem init_shape : Shape init := by
  refine ⟨fun q x hq hx => ?_, fun w r hc => ?_⟩
  · simp [init, stateOf, Config.get, hq] at hx
  · simp [init, stateOf, Config.get] at hc

theorem Good.init : Good init := ⟨init_inv, init_fresh, init_shape⟩

/-- `Good` is kept along every open run with deliveries. -/
theorem reach_good {s₀ s : Sys St Msg} (hg : Good s₀) (hr : SysReachE beh sig Sys.Deliver s₀ s) :
    Good s :=
  hr.inv (fun h hg => hg.step h) (fun he hg => by cases he with | deliver p m => exact hg.deliver p m) hg

/-- Every system the environment can drive the task to from `init` is `Good`. -/
theorem reachEnv_good {s : Sys St Msg} (hr : SysReachEnv beh sig init s) : Good s :=
  hr.inv (fun h hg => hg.step h) (fun p m hg => hg.deliver p m) Good.init

theorem Pending.ne_zero {w : Pid} {s : Sys St Msg} (hg : Good s) (h : Pending w s) : w ≠ 0 := by
  obtain ⟨r, hr⟩ := h
  exact hg.2.2.pending_ne w r hr

theorem Alive.worker {w : Pid} {s : Sys St Msg} (hg : Good s) (h : Alive w s) :
    ∃ q n, s.cfg.stateOf w = some (.worker q n) := by
  obtain ⟨hp, hal, _⟩ := h
  cases hget : s.cfg.get w with
  | none => rw [hget] at hal; cases hal
  | some act =>
    obtain ⟨q, n, hqn⟩ := hg.2.2.workers w act.state (hp.ne_zero hg) (by simp [stateOf, hget])
    exact ⟨q, n, by simp [stateOf, hget, hqn]⟩

/-! ### Steps that only deliver -/

/-- `MsgPending` and its rank survive a step that only appends to the caller's mailbox. -/
theorem msgPending_grow {w : Pid} {a b : Sys St Msg} (hc : b.cfg.stateOf 0 = a.cfg.stateOf 0)
    (hp : MsgPending w a) {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new)) :
    MsgPending w b ∧ rankMsg w b ≤ rankMsg w a := by
  obtain ⟨hpd, mb, hmb, m', hm', hs⟩ := hp
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  refine ⟨⟨hpd.of_stateOf_eq hc, mb ++ new, hnew, m', List.mem_append_left _ hm', hs⟩, ?_⟩
  rw [rankMsg_of_mboxOf hnew, rankMsg_of_mboxOf hmb, List.findIdx_append_of_mem ⟨m', hm', hs⟩]
  exact Nat.le_refl _

theorem msgPending_deliver {w : Pid} {a b : Sys St Msg} (hp : MsgPending w a) {p : Pid} {m : Msg}
    (hcfg : b.cfg = a.cfg.deliver p m) : MsgPending w b ∧ rankMsg w b ≤ rankMsg w a := by
  obtain ⟨new, hnew⟩ := mboxOf_deliver a.cfg p 0 m
  exact msgPending_grow (by rw [hcfg]; exact stateOf_deliver _ _ _ _) hp (by rw [hcfg]; exact hnew)

/-- `DownPending` and its rank survive a step that only appends to `downs`. -/
theorem downPending_grow {w : Pid} {a b : Sys St Msg} (hc : b.cfg.stateOf 0 = a.cfg.stateOf 0)
    (hp : DownPending w a) {new : List (Pid × Pid × Reason)} (hnew : b.downs = a.downs ++ new) :
    DownPending w b ∧ rankDown w b ≤ rankDown w a := by
  obtain ⟨hpd, rs, hd⟩ := hp
  refine ⟨⟨hpd.of_stateOf_eq hc, rs, by rw [hnew]; exact List.mem_append_left _ hd⟩, ?_⟩
  unfold rankDown
  rw [hnew, List.findIdx_append_of_mem ⟨_, hd, isDown_self w rs⟩]
  exact Nat.le_refl _

/-- `Alive` survives a step that only delivers and keeps the monitors. -/
theorem alive_deliver {w : Pid} {a b : Sys St Msg} (hp : Alive w a) {p : Pid} {m : Msg}
    (hcfg : b.cfg = a.cfg.deliver p m) (hmon : b.monitors = a.monitors) : Alive w b := by
  obtain ⟨hpd, hal, hmon'⟩ := hp
  refine ⟨hpd.of_stateOf_eq (by rw [hcfg]; exact stateOf_deliver _ _ _ _), ?_, by rw [hmon]; exact hmon'⟩
  rw [hcfg, isSome_deliver]; exact hal

/-- `Armed` and its rank survive a step that only delivers and keeps the monitors. -/
theorem armed_deliver {w : Pid} {a b : Sys St Msg} (hp : Armed w a) {p : Pid} {m : Msg}
    (hcfg : b.cfg = a.cfg.deliver p m) (hmon : b.monitors = a.monitors) :
    Armed w b ∧ rankKick w b ≤ rankKick w a := by
  obtain ⟨hal, mb, hmb, m', hm', hk⟩ := hp
  obtain ⟨new, hnew⟩ := mboxOf_deliver a.cfg p w m
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  have hnew' : b.cfg.mboxOf w = some (mb ++ new) := by rw [hcfg]; exact hnew
  refine ⟨⟨alive_deliver hal hcfg hmon, mb ++ new, hnew', m', List.mem_append_left _ hm', hk⟩, ?_⟩
  rw [rankKick_of_mboxOf hnew', rankKick_of_mboxOf hmb, List.findIdx_append_of_mem ⟨m', hm', hk⟩]
  exact Nat.le_refl _

/-- A kick delivered to a live `w` arms it. -/
theorem armed_of_kick {w : Pid} {a b : Sys St Msg} (hp : Alive w a) (hk : Kick w a b) : Armed w b := by
  obtain ⟨mb, hmb⟩ := mboxOf_of_isSome hp.2.1
  rcases hk with rfl | rfl
  · refine ⟨alive_deliver hp rfl rfl, mb ++ [.compute], ?_, .compute, List.mem_append_right _ List.mem_cons_self, rfl⟩
    show (a.cfg.deliver w .compute).mboxOf w = _
    rw [mboxOf_deliver_eq, if_pos rfl, hmb]; rfl
  · refine ⟨alive_deliver hp rfl rfl, mb ++ [.crash], ?_, .crash, List.mem_append_right _ List.mem_cons_self, rfl⟩
    show (a.cfg.deliver w .crash).mboxOf w = _
    rw [mboxOf_deliver_eq, if_pos rfl, hmb]; rfl

/-! ### Stage 4: the settling message is consumed -/

/-- One labelled step from a `MsgPending w` state. -/
theorem msgPending_step {w : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : MsgPending w a) :
    Settled b ∨ (MsgPending w b ∧ rankMsg w b ≤ rankMsg w a ∧ (ch = .run 0 → rankMsg w b < rankMsg w a)) := by
  have hi := hg.1
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨⟨r, hc⟩, mb, hmb, m', hm', hs⟩ := hp
      obtain ⟨m, rest, hget, hcase⟩ := caller_run_pending hc hrun
      have hmb' : mb = m :: rest := by
        simp [Config.mboxOf, hget] at hmb; exact hmb.symm
      subst hmb'
      rcases hcase with ⟨_, r', rfl⟩ | ⟨hns, rfl⟩
      · exact Or.inl ⟨r', by simp [stateOf_set]⟩
      · have hrest : m' ∈ rest := by
          rcases List.mem_cons.mp hm' with h | h
          · subst h; rw [hns] at hs; cases hs
          · exact h
        have hmbb : ({ a with cfg := a.cfg.set 0 ⟨.caller (some w) r, rest⟩ } : Sys St Msg).cfg.mboxOf 0 = some rest := by
          simp [mboxOf_set]
        have hlt : rankMsg w { a with cfg := a.cfg.set 0 ⟨.caller (some w) r, rest⟩ } < rankMsg w a := by
          rw [rankMsg_of_mboxOf hmbb, rankMsg_of_mboxOf hmb, List.findIdx_cons_of_false hns]
          exact Nat.lt_succ_self _
        exact Or.inr ⟨⟨⟨r, by simp [stateOf_set]⟩, rest, hmbb, m', hrest, hs⟩, Nat.le_of_lt hlt, fun _ => hlt⟩
    · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp0) hi.next_pos
      obtain ⟨h1, h2⟩ := msgPending_grow (runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos) hp hnew
      exact Or.inr ⟨h1, h2, fun h => absurd (SysChoice.run.inj h) hp0⟩
  | signal _ _ hsig => exact absurd hsig (no_signal hi)
  | down _ _ hdown =>
    obtain ⟨new, hnew⟩ := mboxOf_downE_append hdown 0
    obtain ⟨h1, h2⟩ := msgPending_grow (downE_stateOf hdown 0) hp hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
    obtain ⟨h1, h2⟩ := msgPending_grow (timerE_stateOf htimer 0) hp hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage 4.** With a fair `run 0`, a settling message in the caller's
mailbox leads to the caller settling. -/
theorem msgPending_leadsTo (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0))
    (hfair : ρ.WeakFair (.run 0)) (w : Pid) : LeadsTo ρ.st (MsgPending w) Settled := by
  apply ρ.rank_leads_to_of_step (.run 0) (rankMsg w) hfair
  · intro ch a b hr hl hp _
    exact msgPending_step (reach_good h0 hr) hl hp
  · intro a b _ he hp _
    cases he with
    | deliver p m => exact Or.inr (msgPending_deliver hp rfl)
  · intro a _ ⟨hpd, mb, hmb, m', hm', _⟩ _
    refine (SysEnabled_run_iff _ _).mpr ⟨mb, hmb, ?_⟩
    intro hnil; rw [hnil] at hm'; cases hm'

/-! ### Stage 3: the queued DOWN is delivered -/

/-- One labelled step from a `DownPending w` state. -/
theorem downPending_step {w : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : DownPending w a) :
    (MsgPending w b ∨ Settled b) ∨
      (DownPending w b ∧ rankDown w b ≤ rankDown w a ∧ (ch = .down → rankDown w b < rankDown w a)) := by
  have hi := hg.1
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨⟨r, hc⟩, rs, hd⟩ := hp
      obtain ⟨m, rest, hget, hcase⟩ := caller_run_pending hc hrun
      rcases hcase with ⟨_, r', rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl (Or.inr ⟨r', by simp [stateOf_set]⟩)
      · exact Or.inr ⟨⟨⟨r, by simp [stateOf_set]⟩, rs, hd⟩, Nat.le_refl _, fun h => nomatch h⟩
    · obtain ⟨new, hnew⟩ := runE_downs_append hrun
      obtain ⟨h1, h2⟩ := downPending_grow (runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos) hp hnew
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | signal _ _ hsig => exact absurd hsig (no_signal hi)
  | down _ _ hdown =>
    obtain ⟨⟨r, hc⟩, rs, hd⟩ := hp
    obtain ⟨w', t', rs', rest, hdw, rfl⟩ := downE_of_codec rfl hdown
    by_cases hhead : w' = 0 ∧ t' = w
    · obtain ⟨hw0, hsrc⟩ := hhead
      subst w'; subst t'
      obtain ⟨mb, hmb⟩ := Pending.mboxOf (w := w) (s := a) ⟨r, hc⟩
      refine Or.inl (Or.inl ⟨⟨r, by rw [stateOf_deliver]; exact hc⟩, mb ++ [.DOWN w rs'], ?_, .DOWN w rs',
        List.mem_append_right _ List.mem_cons_self, isSettle_down w rs'⟩)
      show (a.cfg.deliver 0 (.DOWN w rs')).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl, hmb]; rfl
    · have hrest : (0, w, rs) ∈ rest := by
        rw [hdw] at hd
        rcases List.mem_cons.mp hd with h | h
        · exact absurd ⟨(congrArg Prod.fst h).symm, (congrArg (·.2.1) h).symm⟩ hhead
        · exact h
      have hno : isDown w (w', t', rs') = false := by
        simp only [isDown, decide_eq_false_iff_not]; exact hhead
      have hlt : rest.findIdx (isDown w) < rankDown w a := by
        unfold rankDown
        rw [hdw, List.findIdx_cons_of_false hno]
        exact Nat.lt_succ_self _
      exact Or.inr ⟨⟨⟨r, by rw [stateOf_deliver]; exact hc⟩, rs, hrest⟩, Nat.le_of_lt hlt, fun _ => hlt⟩
  | timer _ i _ htimer =>
    obtain ⟨h1, h2⟩ := downPending_grow (timerE_stateOf htimer 0) hp (new := []) (by rw [timerE_downs htimer]; simp)
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage 3.** With a fair `down` step, a queued DOWN of the pending
worker leads to a settling message in the caller's mailbox, or to the
caller settling. -/
theorem downPending_leadsTo (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0))
    (hfair : ρ.WeakFair .down) (w : Pid) :
    LeadsTo ρ.st (DownPending w) (fun s => MsgPending w s ∨ Settled s) := by
  apply ρ.rank_leads_to_of_step .down (rankDown w) hfair
  · intro ch a b hr hl hp _
    exact downPending_step (reach_good h0 hr) hl hp
  · intro a b _ he hp _
    cases he with
    | deliver p m => exact Or.inr (downPending_grow (stateOf_deliver _ _ _ _) hp (new := []) (by simp))
  · intro a _ ⟨_, rs, hd⟩ _
    show a.downs ≠ []
    intro hnil; rw [hnil] at hd; cases hd

/-! ### Stage 2: the armed worker runs -/

/-- One labelled step from an `Armed w` state. -/
theorem armed_step {w : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : Armed w a) :
    (DownPending w b ∨ Settled b) ∨
      (Armed w b ∧ rankKick w b ≤ rankKick w a ∧ (ch = .run w → rankKick w b < rankKick w a)) := by
  have hi := hg.1
  have hw0 : w ≠ 0 := hp.1.1.ne_zero hg
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨⟨⟨r, hc⟩, hal, hmon⟩, mb, hmb, m', hm', hk⟩ := hp
      obtain ⟨m, rest, hget, hcase⟩ := caller_run_pending hc hrun
      rcases hcase with ⟨_, r', rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl (Or.inr ⟨r', by simp [stateOf_set]⟩)
      · have hmbw : ({ a with cfg := a.cfg.set 0 ⟨.caller (some w) r, rest⟩ } : Sys St Msg).cfg.mboxOf w = some mb := by
          simp [mboxOf_set, hw0]; exact hmb
        refine Or.inr ⟨⟨⟨⟨r, by simp [stateOf_set]⟩, by simp [isSome_set, hw0]; exact hal, hmon⟩, mb, hmbw, m', hm', hk⟩, ?_,
          fun h => absurd (SysChoice.run.inj h).symm hw0⟩
        rw [rankKick_of_mboxOf hmbw, rankKick_of_mboxOf hmb]
        exact Nat.le_refl _
    · by_cases hpw : p = w
      · subst hpw
        obtain ⟨q, n, hws⟩ := hp.1.worker hg
        obtain ⟨⟨⟨r, hc⟩, hal, hmon⟩, mb, hmb, m', hm', hk⟩ := hp
        obtain ⟨m, rest, hget, hcase⟩ := worker_run hws hrun
        have hmb' : mb = m :: rest := by
          simp [Config.mboxOf, hget] at hmb; exact hmb.symm
        subst hmb'
        rcases hcase with ⟨hnk, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · have hrest : m' ∈ rest := by
            rcases List.mem_cons.mp hm' with h | h
            · subst h; rw [hnk] at hk; cases hk
            · exact h
          have hmbb : ({ a with cfg := a.cfg.set p ⟨.worker q n, rest⟩ } : Sys St Msg).cfg.mboxOf p = some rest := by
            simp [mboxOf_set]
          have hlt : rankKick p { a with cfg := a.cfg.set p ⟨.worker q n, rest⟩ } < rankKick p a := by
            rw [rankKick_of_mboxOf hmbb, rankKick_of_mboxOf hmb, List.findIdx_cons_of_false hnk]
            exact Nat.lt_succ_self _
          exact Or.inr ⟨⟨⟨⟨r, by simp [stateOf_set, Ne.symm hw0]; exact hc⟩, by simp [isSome_set], hmon⟩, rest, hmbb, m', hrest, hk⟩,
            Nat.le_of_lt hlt, fun _ => hlt⟩
        · refine Or.inl (Or.inl ⟨⟨r, ?_⟩, .normal, terminate_down_of_monitor _ _ _ hmon⟩)
          rw [terminate_stateOf_ne _ _ _ (Ne.symm hw0)]
          show ((a.cfg.set p ⟨.worker q n, rest⟩).deliver q (.reply (n + 1))).stateOf 0 = _
          rw [stateOf_deliver]; simp [stateOf_set, Ne.symm hw0]; exact hc
        · refine Or.inl (Or.inl ⟨⟨r, ?_⟩, .error, terminate_down_of_monitor _ _ _ hmon⟩)
          rw [terminate_stateOf_ne _ _ _ (Ne.symm hw0)]
          show (a.cfg.set p ⟨.worker q n, rest⟩).stateOf 0 = _
          simp [stateOf_set, Ne.symm hw0]; exact hc
      · obtain ⟨⟨⟨r, hc⟩, hal, hmon⟩, mb, hmb, m', hm', hk⟩ := hp
        have hfr := runE_frame hrun
        obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hpw) (hg.2.1.lt_next hal)
        rw [hmb] at hnew
        simp only [Option.map_some] at hnew
        refine Or.inr ⟨⟨⟨⟨r, by rw [hfr.stateOf 0 (Ne.symm hp0) hi.next_pos]; exact hc⟩, hfr.alive w (Ne.symm hpw) hal,
          hfr.monitors (0, w) hmon (Ne.symm hp0) (Ne.symm hpw)⟩, mb ++ new, hnew, m', List.mem_append_left _ hm', hk⟩, ?_,
          fun h => absurd (SysChoice.run.inj h) hpw⟩
        rw [rankKick_of_mboxOf hnew, rankKick_of_mboxOf hmb, List.findIdx_append_of_mem ⟨m', hm', hk⟩]
        exact Nat.le_refl _
  | signal _ _ hsig => exact absurd hsig (no_signal hi)
  | down _ _ hdown =>
    obtain ⟨w', t', rs', rest, hdw, rfl⟩ := downE_of_codec rfl hdown
    obtain ⟨h1, h2⟩ := armed_deliver hp (b := { a with cfg := a.cfg.deliver w' (.DOWN t' rs') })
      (p := w') (m := .DOWN t' rs') rfl rfl
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨to, m, _, rfl⟩ := timerE_cases htimer
    obtain ⟨h1, h2⟩ := armed_deliver hp (b := { a with cfg := a.cfg.deliver to m })
      (p := to) (m := m) rfl rfl
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage 2.** With a fair `run w`, an armed worker leads to its DOWN
being queued, or to the caller settling. -/
theorem armed_leadsTo (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0)) (w : Pid)
    (hfair : ρ.WeakFair (.run w)) :
    LeadsTo ρ.st (Armed w) (fun s => DownPending w s ∨ Settled s) := by
  apply ρ.rank_leads_to_of_step (.run w) (rankKick w) hfair
  · intro ch a b hr hl hp _
    exact armed_step (reach_good h0 hr) hl hp
  · intro a b _ he hp _
    cases he with
    | deliver p m => exact Or.inr (armed_deliver hp rfl rfl)
  · intro a _ ⟨_, mb, hmb, m', hm', _⟩ _
    refine (SysEnabled_run_iff _ _).mpr ⟨mb, hmb, ?_⟩
    intro hnil; rw [hnil] at hm'; cases hm'

/-! ### Stage 1: the environment kicks the live worker -/

/-- One system step from an `Alive w` state. -/
theorem alive_step {w : Pid} {a b : Sys St Msg} (hg : Good a) (h : SysStep beh sig a b)
    (hp : Alive w a) : Alive w b ∨ DownPending w b ∨ Settled b := by
  have hi := hg.1
  have hw0 : w ≠ 0 := hp.1.ne_zero hg
  cases h with
  | run p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨⟨r, hc⟩, hal, hmon⟩ := hp
      obtain ⟨m, rest, hget, hcase⟩ := caller_run_pending hc hrun
      rcases hcase with ⟨_, r', rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (Or.inr ⟨r', by simp [stateOf_set]⟩)
      · exact Or.inl ⟨⟨r, by simp [stateOf_set]⟩, by simp [isSome_set, hw0]; exact hal, hmon⟩
    · by_cases hpw : p = w
      · subst hpw
        obtain ⟨q, n, hws⟩ := hp.worker hg
        obtain ⟨⟨r, hc⟩, hal, hmon⟩ := hp
        obtain ⟨m, rest, hget, hcase⟩ := worker_run hws hrun
        rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact Or.inl ⟨⟨r, by simp [stateOf_set, Ne.symm hw0]; exact hc⟩, by simp [isSome_set], hmon⟩
        · refine Or.inr (Or.inl ⟨⟨r, ?_⟩, .normal, terminate_down_of_monitor _ _ _ hmon⟩)
          rw [terminate_stateOf_ne _ _ _ (Ne.symm hw0)]
          show ((a.cfg.set p ⟨.worker q n, rest⟩).deliver q (.reply (n + 1))).stateOf 0 = _
          rw [stateOf_deliver]; simp [stateOf_set, Ne.symm hw0]; exact hc
        · refine Or.inr (Or.inl ⟨⟨r, ?_⟩, .error, terminate_down_of_monitor _ _ _ hmon⟩)
          rw [terminate_stateOf_ne _ _ _ (Ne.symm hw0)]
          show (a.cfg.set p ⟨.worker q n, rest⟩).stateOf 0 = _
          simp [stateOf_set, Ne.symm hw0]; exact hc
      · obtain ⟨⟨r, hc⟩, hal, hmon⟩ := hp
        have hfr := runE_frame hrun
        exact Or.inl ⟨⟨r, by rw [hfr.stateOf 0 (Ne.symm hp0) hi.next_pos]; exact hc⟩,
          hfr.alive w (Ne.symm hpw) hal, hfr.monitors (0, w) hmon (Ne.symm hp0) (Ne.symm hpw)⟩
  | signal _ hsig => exact absurd hsig (no_signal hi)
  | down _ hdown =>
    obtain ⟨w', t', rs', rest, hdw, rfl⟩ := downE_of_codec rfl hdown
    exact Or.inl (alive_deliver hp (p := w') (m := .DOWN t' rs') rfl rfl)
  | timer i _ htimer =>
    obtain ⟨to, m, _, rfl⟩ := timerE_cases htimer
    exact Or.inl (alive_deliver hp (p := to) (m := m) rfl rfl)

/-- **Stage 1.** If the environment is fair to the pending worker
(`EnvFair (Alive w) (Kick w)`: while the caller keeps waiting on a live
monitored `w`, `w` is eventually kicked), a live pending worker leads to an
armed one, or to its DOWN being queued, or to the caller settling. -/
theorem alive_leadsTo (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0)) (w : Pid)
    (henv : ρ.EnvFair (Alive w) (Kick w)) :
    LeadsTo ρ.st (Alive w) (fun s => Armed w s ∨ DownPending w s ∨ Settled s) := by
  apply ρ.stable_until_env henv
  · intro a b hr hs hp _
    rcases alive_step (reach_good h0 hr) hs hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · intro a b _ he hp _
    cases he with
    | deliver p m => exact Or.inl (alive_deliver hp rfl rfl)
  · intro a _ hp _
    exact hp
  · intro a b _ _ hk hp _
    exact Or.inl (armed_of_kick hp hk)

/-! ### The theorems -/

/-- A message with a positive count is in the mailbox. -/
theorem msgPending_of_mcount {w : Pid} {s : Sys St Msg} {r : Nat}
    (hc : s.cfg.stateOf 0 = some (.caller (some w) r)) {m : Msg} (hm : 0 < s.cfg.mcount 0 m)
    (hs : isSettle w m = true) : MsgPending w s := by
  obtain ⟨_, mb, hget⟩ := Pending.get (w := w) (s := s) ⟨r, hc⟩
  refine ⟨⟨r, hc⟩, mb, by simp [Config.mboxOf, hget], m, ?_, hs⟩
  unfold mcount at hm
  rw [hget] at hm
  exact List.count_pos_iff.mp hm

/-- **A job whose worker is dead eventually settles** (open run). Along any
run with deliveries from a `Good` system in which the `down` step and
`run 0` are weakly fair: if at time `t` the caller waits on a dead `w`,
then at some `t' ≥ t` it has no pending job. -/
theorem job_eventually_settles_dead_env (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0))
    (hdown : ρ.WeakFair .down) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w r, (ρ.st t).cfg.stateOf 0 = some (.caller (some w) r) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ r', (ρ.st t').cfg.stateOf 0 = some (.caller none r') := by
  intro t w r hc hdead
  have hg : Good (ρ.st t) := reach_good h0 (ρ.reach t)
  have h4 := msgPending_leadsTo ρ h0 hrun w
  have h3 := (downPending_leadsTo ρ h0 hdown w).trans (h4.or (LeadsTo.refl ρ.st Settled))
  rcases hg.1.pending_ok w r hc with ⟨hal, _⟩ | ⟨rs, hd⟩ | ⟨v, hv⟩ | ⟨rs, hv⟩
  · rw [hdead] at hal; cases hal
  · exact h3 t ⟨⟨r, hc⟩, rs, hd⟩
  · exact h4 t (msgPending_of_mcount hc hv (isSettle_reply w v))
  · exact h4 t (msgPending_of_mcount hc hv (isSettle_down w rs))

/-- **A job whose worker is dead eventually settles** (closed run, the
unconditional theorem). Along any `SysRun` from a `Good` system in which
the `down` step and `run 0` are weakly fair: if at time `t` the caller
waits on a dead `w`, then at some `t' ≥ t` it has no pending job. Nothing
is assumed of the other pids, of the timers, or of the environment. -/
theorem job_eventually_settles_dead (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (hdown : ρ.WeakFair .down) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w r, (ρ.st t).cfg.stateOf 0 = some (.caller (some w) r) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ r', (ρ.st t').cfg.stateOf 0 = some (.caller none r') :=
  job_eventually_settles_dead_env (ρ.toE Sys.Deliver) h0 (SysRun.toE_weakFair _ hdown)
    (SysRun.toE_weakFair _ hrun)

/-- **A pending job eventually settles** (open run, conditional on the
environment). Along any run with deliveries from a `Good` system in which
the `down` step and `run 0` are weakly fair: if at time `t` the caller
waits on `w`, and `run w` is weakly fair, and the environment eventually
kicks `w` whenever the caller keeps waiting on it alive and monitored
(`EnvFair (Alive w) (Kick w)`), then at some `t' ≥ t` the caller has no
pending job. The last two assumptions are exactly what a live worker
needs: a worker acts only on `compute` or `crash`, which only the
environment sends. -/
theorem job_eventually_settles (ρ : SysRunE beh sig Sys.Deliver) (h0 : Good (ρ.st 0))
    (hdown : ρ.WeakFair .down) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w r, (ρ.st t).cfg.stateOf 0 = some (.caller (some w) r) →
      ρ.WeakFair (.run w) → ρ.EnvFair (Alive w) (Kick w) →
      ∃ t' ≥ t, ∃ r', (ρ.st t').cfg.stateOf 0 = some (.caller none r') := by
  intro t w r hc hrunw henv
  have hg : Good (ρ.st t) := reach_good h0 (ρ.reach t)
  have h4 := msgPending_leadsTo ρ h0 hrun w
  have h3 := (downPending_leadsTo ρ h0 hdown w).trans (h4.or (LeadsTo.refl ρ.st Settled))
  have h2 := (armed_leadsTo ρ h0 w hrunw).trans (h3.or (LeadsTo.refl ρ.st Settled))
  have h1 := (alive_leadsTo ρ h0 w henv).trans (h2.or (h3.or (LeadsTo.refl ρ.st Settled)))
  rcases hg.1.pending_ok w r hc with ⟨hal, hmon⟩ | ⟨rs, hd⟩ | ⟨v, hv⟩ | ⟨rs, hv⟩
  · exact h1 t ⟨⟨r, hc⟩, hal, hmon⟩
  · exact h3 t ⟨⟨r, hc⟩, rs, hd⟩
  · exact h4 t (msgPending_of_mcount hc hv (isSettle_reply w v))
  · exact h4 t (msgPending_of_mcount hc hv (isSettle_down w rs))

/-- The same from any system the environment can drive the task to from
`init`. -/
theorem job_eventually_settles_env (ρ : SysRunE beh sig Sys.Deliver)
    (h0 : SysReachEnv beh sig init (ρ.st 0)) (hdown : ρ.WeakFair .down) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w r, (ρ.st t).cfg.stateOf 0 = some (.caller (some w) r) →
      ρ.WeakFair (.run w) → ρ.EnvFair (Alive w) (Kick w) →
      ∃ t' ≥ t, ∃ r', (ρ.st t').cfg.stateOf 0 = some (.caller none r') :=
  job_eventually_settles ρ (reachEnv_good h0) hdown hrun

theorem job_eventually_settles_dead_reachEnv (ρ : SysRun beh sig)
    (h0 : SysReachEnv beh sig init (ρ.st 0)) (hdown : ρ.WeakFair .down) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w r, (ρ.st t).cfg.stateOf 0 = some (.caller (some w) r) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ r', (ρ.st t').cfg.stateOf 0 = some (.caller none r') :=
  job_eventually_settles_dead ρ (reachEnv_good h0) hdown hrun

/-! ### Non-vacuity -/

/-- The caller after `go`: waiting on worker 1, which is alive and idle. -/
def sLive : Sys St Msg := runSys beh sig init [.run 0]

/-- `sLive` after the environment sent worker 1 `:crash` and it ran: the
worker is dead and its DOWN is queued. -/
def sDead : Sys St Msg := runSys beh sig { sLive with cfg := sLive.cfg.deliver 1 .crash } [.run 1]

/-- The premise of the closed theorem is reachable: run 0, let the
environment send `:crash` to the worker, run 1. -/
theorem dead_worker_reachable : ∃ s, SysReachEnv beh sig init s ∧
    ∃ w r, s.cfg.stateOf 0 = some (.caller (some w) r) ∧ (s.cfg.get w).isSome = false :=
  ⟨sDead, .step (.run _ 0 _ rfl) (.env 1 .crash (.step (.run _ 1 _ rfl) (.refl _))), 1, 0, rfl, rfl⟩

/-- The premise of the open theorem is reachable with a live worker: run 0. -/
theorem live_worker_reachable : ∃ s, SysReachEnv beh sig init s ∧
    ∃ w r, s.cfg.stateOf 0 = some (.caller (some w) r) ∧ (s.cfg.get w).isSome = true :=
  ⟨sLive, .step (.run _ 0 _ rfl) (.refl _), 1, 0, rfl, rfl⟩

/-- A closed run from `sDead`: deliver the DOWN, run the caller, idle. -/
def deadSt : Nat → Sys St Msg
  | 0 => sDead
  | 1 => runSys beh sig sDead [.down]
  | _ => runSys beh sig sDead [.down, .run 0]

def deadCh : Nat → Option SysChoice
  | 0 => some .down
  | 1 => some (.run 0)
  | _ => none

def deadRun : SysRun beh sig where
  st := deadSt
  ch := deadCh
  step := fun t => match t with
    | 0 => .step _ _ _ (.down _ _ rfl)
    | 1 => .step _ _ _ (.run _ 0 _ rfl)
    | _ + 2 => .idle _

/-- `deadRun` satisfies every hypothesis of `job_eventually_settles_dead`
(its start is environment-reachable, hence `Good`; `down` and `run 0` are
weakly fair, being disabled from time 2 on) and its premise at time 0, and
the caller has settled at time 2. -/
theorem deadRun_witness :
    SysReachEnv beh sig init (deadRun.st 0) ∧ deadRun.WeakFair .down ∧ deadRun.WeakFair (.run 0) ∧
    (deadRun.st 0).cfg.stateOf 0 = some (.caller (some 1) 0) ∧ ((deadRun.st 0).cfg.get 1).isSome = false ∧
    (deadRun.st 2).cfg.stateOf 0 = some (.caller none 0) := by
  refine ⟨.step (.run _ 0 _ rfl) (.env 1 .crash (.step (.run _ 1 _ rfl) (.refl _))), ?_, ?_, rfl, rfl, rfl⟩
  · left
    intro t
    refine ⟨t + 2, by omega, ?_⟩
    show ¬ ((deadSt (t + 2)).downs ≠ [])
    intro h; exact h rfl
  · left
    intro t
    refine ⟨t + 2, by omega, ?_⟩
    rintro ⟨st, m, rest, h⟩
    have h' : (deadRun.st (t + 2)).cfg.get 0 = some ⟨.caller none 0, []⟩ := rfl
    rw [h'] at h
    cases h

/-- An open run from `sLive`: the environment sends `:compute`, the worker
runs (replies and exits), the DOWN is delivered, the caller runs twice
(the reply settles it, the DOWN is ignored), idle. -/
def liveSt : Nat → Sys St Msg
  | 0 => sLive
  | 1 => { sLive with cfg := sLive.cfg.deliver 1 .compute }
  | 2 => runSys beh sig { sLive with cfg := sLive.cfg.deliver 1 .compute } [.run 1]
  | 3 => runSys beh sig { sLive with cfg := sLive.cfg.deliver 1 .compute } [.run 1, .down]
  | 4 => runSys beh sig { sLive with cfg := sLive.cfg.deliver 1 .compute } [.run 1, .down, .run 0]
  | _ => runSys beh sig { sLive with cfg := sLive.cfg.deliver 1 .compute } [.run 1, .down, .run 0, .run 0]

def liveCh : Nat → Option SysChoiceE
  | 0 => some .env
  | 1 => some (.sys (.run 1))
  | 2 => some (.sys .down)
  | 3 => some (.sys (.run 0))
  | 4 => some (.sys (.run 0))
  | _ => none

def liveRun : SysRunE beh sig Sys.Deliver where
  st := liveSt
  ch := liveCh
  step := fun t => match t with
    | 0 => .step _ _ _ (.env _ _ (.deliver _ 1 Leanactors.Gen.Task.Msg.compute))
    | 1 => .step _ _ _ (.sys _ _ _ (.run _ 1 _ rfl))
    | 2 => .step _ _ _ (.sys _ _ _ (.down _ _ rfl))
    | 3 => .step _ _ _ (.sys _ _ _ (.run _ 0 _ rfl))
    | 4 => .step _ _ _ (.sys _ _ _ (.run _ 0 _ rfl))
    | _ + 5 => .idle _

/-- `liveRun` satisfies every hypothesis of `job_eventually_settles` for
`w = 1` (start environment-reachable; `down`, `run 0` and `run 1` weakly
fair, all disabled from time 5 on; `EnvFair (Alive 1) (Kick 1)` because
worker 1 is dead from time 2 on, so its premise never holds) and its
premise at time 0, and the caller has settled at time 5 with one reply
counted. -/
theorem liveRun_witness :
    SysReachEnv beh sig init (liveRun.st 0) ∧ liveRun.WeakFair .down ∧ liveRun.WeakFair (.run 0) ∧
    liveRun.WeakFair (.run 1) ∧ liveRun.EnvFair (Alive 1) (Kick 1) ∧
    (liveRun.st 0).cfg.stateOf 0 = some (.caller (some 1) 0) ∧ ((liveRun.st 0).cfg.get 1).isSome = true ∧
    (liveRun.st 5).cfg.stateOf 0 = some (.caller none 1) := by
  refine ⟨.step (.run _ 0 _ rfl) (.refl _), ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · left
    intro t
    refine ⟨t + 5, by omega, ?_⟩
    show ¬ ((liveSt (t + 5)).downs ≠ [])
    intro h; exact h rfl
  · left
    intro t
    refine ⟨t + 5, by omega, ?_⟩
    rintro ⟨st, m, rest, h⟩
    have h' : (liveRun.st (t + 5)).cfg.get 0 = some ⟨.caller none 1, []⟩ := rfl
    rw [h'] at h
    cases h
  · left
    intro t
    refine ⟨t + 5, by omega, ?_⟩
    rintro ⟨st, m, rest, h⟩
    have h' : (liveRun.st (t + 5)).cfg.get 1 = none := rfl
    rw [h'] at h
    cases h
  · intro t h
    have h1 := (h (t + 5) (by omega)).2.1
    have h2 : ((liveRun.st (t + 5)).cfg.get 1).isSome = false := rfl
    rw [h2] at h1
    cases h1

end Examples.Task

end Leanactors
