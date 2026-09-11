import Leanactors.Fair
import Leanactors.Examples.TtlProof
import Leanactors.Examples.SupervisorLive
/-!
# Leanactors.Examples.TtlLive

**Liveness of the TTL cache.** `TtlProof` says what the cache never
holds. This file says what must happen to what it holds: a value does not
sit in the cache forever.

The cache (pid 0) is a `receive ... after` loop with a generation counter
`g`. Whenever it is at generation `g` the timer `(0, after_run g)` is in
flight: still pending in `timers`, or already fired into the cache's
mailbox (`Armed`, half of `Good`). Every message the cache processes moves
it to generation `g + 1` and re-arms; the timer of the current generation
runs the after body, which clears the value and also re-arms at `g + 1`; a
stale timer is consumed and ignored; `put 0` kills the cache.

`gen_advances_or_clears`: along any run from a `Good` system in which the
oldest pending timer (`timer 0`) and the cache (`run 0`) are weakly fair,
if the cache holds `some v` at generation `g` at time `t`, then at some
`t' ≥ t` it still holds `some v` at `g` and its `run 0` step at `t'`
leaves generation `g` in one of exactly three ways:

* the after-timer of generation `g` ran and the value is cleared:
  `.cache none (g + 1)`;
* a message (`put`, `get`, or a deferred one) was processed and the
  timeout re-armed: `.cache (some x) (g + 1)`;
* `put 0` killed the cache.

Nothing else can happen: no other step changes the cache's state (nobody
links, monitors or signals in this program, so `signals` stays empty and
`down` steps only pop). `gen_changes_or_clears` restates it as "the
generation changes, or the value is cleared, or the cache is dead";
`gen_advances` is the plain corollary that the cache does not stay at
generation `g`; `gen_advances_or_clears_timers` takes `∀ i, WeakFair
(.timer i)` instead (the watchdog's premise; `timer 0` is its instance);
and `value_eventually_expires` is the one asked for: if no message is processed at generation `g` (the cache
never reaches `.cache (some _) (g + 1)` and never dies), the value clears.
The corollary "if the generation never changes then the value clears" is
*not* the honest one: the after body itself moves to `g + 1`, so a fair
run never keeps the generation, and that statement would be vacuous.

**Fairness assumed.** `WeakFair (.timer 0)`: if some timer is pending
from a point on, the oldest pending one eventually fires (so
`∀ i, WeakFair (.timer i)` is more than enough). `WeakFair (.run 0)`: a
cache with mail is eventually run. Timers are untimed, so a stale timer
may fire before the live one; the argument does not care in which order,
only that the live one is not starved. Nothing about `signal`, `down` or
the reader is assumed.

**The proof** is two `LeadsTo` stages by `SysRun.rank_leads_to_of_step`
(from `SupervisorLive`), both toward "the cache no longer holds `v` at
`g`":

* **Stage A** (`timerPending_leadsTo`): the timer `(0, after_run g)` is
  pending, ranked by its position in `timers`. Every step appends to
  `timers` or erases one entry: erasing an entry ahead of ours drops the
  rank, erasing ours delivers it (Stage B's premise), and `timer 0` does
  one of those two.
* **Stage B** (`msgPending_leadsTo`): `after_run g` is in the cache's
  mailbox, ranked by its position. Other steps only append; `run 0` pops
  the head, which is a stale timer (rank drops, state unchanged) or leaves
  generation `g` (the goal).

`exists_last` then picks the first time the cache leaves generation `g`,
and `cache_run_cases` classifies that `run 0` step.

**Non-vacuity.** `Good` needs none of the safety invariant `Inv` (the
environment may deliver anything, `reachEnv_good`), so every system the
environment can drive the cache to is a valid start. `premise_reachable`
exhibits `.cache (some 5) 1` two steps from `init`, and `wit` is an
explicit infinite run from a reachable such system (`W (some 5) 1 []
[(0, after_run 1)]`) that alternates `timer 0` and `run 0` forever: it is
weakly fair for both choices, non-idle, satisfies the premise of every
theorem here at time 0, expires the value at time 2, and never processes
a message, so `value_eventually_expires` is not vacuous either
(`fair_run_exists`, `wit_quiet`).
-/

set_option linter.unusedSimpArgs false

namespace Leanactors

variable {σ μ : Type}

/-! ## The first time a predicate on times stops holding -/

/-- Between a time where `P` holds and a later one where it does not, there
is a last time it holds. -/
theorem exists_last {P : Nat → Prop} {t t' : Nat} (htt : t ≤ t') (hp : P t) (hq : ¬ P t') :
    ∃ u, t ≤ u ∧ u < t' ∧ P u ∧ ¬ P (u + 1) := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.le_zero.mp htt
    subst this; exact absurd hp hq
  | succ t' ih =>
    by_cases hpt : P t'
    · have hle : t ≤ t' := by
        rcases Nat.lt_or_eq_of_le htt with hlt | heq
        · exact Nat.le_of_lt_succ hlt
        · subst heq; exact absurd hp hq
      exact ⟨t', hle, Nat.lt_succ_self _, hpt, hq⟩
    · have hle : t ≤ t' := by
        rcases Nat.lt_or_eq_of_le htt with hlt | heq
        · exact Nat.le_of_lt_succ hlt
        · subst heq; exact absurd hp hq
      obtain ⟨u, h1, h2, h3, h4⟩ := ih hle hpt
      exact ⟨u, h1, Nat.lt_succ_of_lt h2, h3, h4⟩

/-! ## A labelled step or an idle step, with the choice -/

theorem SysStepI.casesL {beh : EBehavior σ μ} {sig : Signals σ μ} {oc : Option SysChoice}
    {a b : Sys σ μ} (h : SysStepI beh sig oc a b) :
    (∃ c, oc = some c ∧ SysStepL beh sig c a b) ∨ (oc = none ∧ b = a) := by
  cases h with
  | step c _ _ hl => exact Or.inl ⟨c, rfl, hl⟩
  | idle _ => exact Or.inr ⟨rfl, rfl⟩

/-! ## The TTL cache -/

namespace Examples.Ttl

open Leanactors Config Sys

/-- The cache (pid 0) holds `v` at generation `g`. -/
def At (v : Option Nat) (g : Nat) (s : Sys St Msg) : Prop := s.cfg.stateOf 0 = some (.cache v g)

/-- Generation `g`'s timer is in flight: still pending, or already fired
into the cache's mailbox. -/
def Armed (g : Nat) (s : Sys St Msg) : Prop :=
  (0, Gen.Ttl.Msg.after_run g) ∈ s.timers ∨ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ Gen.Ttl.Msg.after_run g ∈ mb

/-- What the liveness argument needs of a start system. None of it is the
safety invariant `Inv`: liveness of the timeout does not care what the
cache holds. -/
structure Good (s : Sys St Msg) : Prop where
  next_pos : 0 < s.next
  /-- Nobody links, so nobody ever signals. -/
  links : s.links = []
  signals : s.signals = []
  /-- Pid 0 is the cache, if it is alive. -/
  cache : ∀ st, s.cfg.stateOf 0 = some st → ∃ v g, st = .cache v g
  /-- At generation `g`, the timer of generation `g` is in flight. -/
  armed : ∀ v g, At v g s → Armed g s

theorem At.get {v : Option Nat} {g : Nat} {s : Sys St Msg} (h : At v g s) :
    ∃ mb, s.cfg.get 0 = some ⟨.cache v g, mb⟩ := by
  unfold At stateOf at h
  cases hget : s.cfg.get 0 with
  | none => rw [hget] at h; cases h
  | some a =>
    rw [hget] at h
    obtain ⟨st, mb⟩ := a
    simp at h
    exact ⟨mb, by rw [h]⟩

theorem At.mboxOf {v : Option Nat} {g : Nat} {s : Sys St Msg} (h : At v g s) :
    ∃ mb, s.cfg.mboxOf 0 = some mb := by
  obtain ⟨mb, hget⟩ := h.get
  exact ⟨mb, by simp [Config.mboxOf, hget]⟩

theorem at_set (a : Sys St Msg) (v : Option Nat) (g : Nat) (rest : List Msg) :
    At v g { a with cfg := a.cfg.set 0 ⟨.cache v g, rest⟩ } := by
  show (a.cfg.set 0 _).stateOf 0 = _
  rw [stateOf_set, if_pos rfl]

/-- Leaving generation `g`, alive or dead, is not `At v g`. -/
theorem not_at_of_gen {v : Option Nat} {g : Nat} {s : Sys St Msg} {v' : Option Nat}
    (h : s.cfg.stateOf 0 = some (.cache v' (g + 1))) : ¬ At v g s := by
  intro hat
  unfold At at hat
  rw [h] at hat
  simp at hat

theorem not_at_of_none {v : Option Nat} {g : Nat} {s : Sys St Msg}
    (h : s.cfg.stateOf 0 = none) : ¬ At v g s := by
  intro hat
  unfold At at hat
  rw [h] at hat
  cases hat

/-- The mailbox grew and the timers grew: the timer stays in flight. -/
theorem Armed.grow {g : Nat} {a b : Sys St Msg} (ha : Armed g a)
    {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new))
    {tnew : List (Pid × Msg)} (ht : b.timers = a.timers ++ tnew) : Armed g b := by
  rcases ha with ht' | ⟨mb, hmb, hm⟩
  · exact Or.inl (by rw [ht]; exact List.mem_append_left _ ht')
  · exact Or.inr ⟨mb ++ new, by rw [hnew, hmb]; rfl, List.mem_append_left _ hm⟩

/-! ### The cache's own step -/

/-- No clause of `beh` links, spawns with a link, or signals. -/
theorem beh_isolated (me fresh : Pid) (st : St) (m : Msg) :
    ∀ e ∈ (beh me fresh st m).2, e.isolated = true := by
  intro e he
  cases st with
  | cache v g =>
    cases m with
    | put x =>
      cases x with
      | zero => simp only [beh, List.mem_singleton] at he; subst he; rfl
      | succ n => simp only [beh, List.mem_singleton] at he; subst he; rfl
    | get r =>
      simp only [beh, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    | after_run g' =>
      by_cases hg : g' = g
      · simp only [beh, if_pos hg, List.mem_singleton] at he; subst he; rfl
      · simp only [beh, if_neg hg, List.not_mem_nil] at he
    | ask =>
      simp only [beh, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    | value w =>
      simp only [beh, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
  | reader n =>
    cases m with
    | ask => simp only [beh, List.mem_singleton] at he; subst he; rfl
    | value w => simp only [beh, List.not_mem_nil] at he
    | put x => simp only [beh, List.mem_singleton] at he; subst he; rfl
    | get r => simp only [beh, List.mem_singleton] at he; subst he; rfl
    | after_run g' => simp only [beh, List.mem_singleton] at he; subst he; rfl

/-- A step keeps `links` and `signals` empty. -/
theorem run_links_signals {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b)
    (hl : a.links = []) (hs : a.signals = []) : b.links = [] ∧ b.signals = [] := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  have hiso := applyEffects_links_signals_of_isolated p
    { a with cfg := a.cfg.set p ⟨(beh p a.next st m).1, rest⟩ } (beh_isolated p a.next st m)
  simp only at hiso
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨hiso.1.trans hl, hiso.2.trans hs⟩
  · exact ⟨terminate_links_of_links_nil _ _ _ (hiso.1.trans hl),
      (terminate_signals_of_links_nil _ _ _ (hiso.1.trans hl)).trans (hiso.2.trans hs)⟩

/-- A `run 0` step from `.cache v g`: the popped message is a stale timer
(state unchanged, nothing armed), the live timer (value cleared, next
generation armed), `put 0` (dead), or any other message (processed, next
generation armed, the value kept or replaced by a `put`). -/
theorem cache_run_cases {a b : Sys St Msg} {v : Option Nat} {g : Nat}
    (hc : a.cfg.stateOf 0 = some (.cache v g)) (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.cache v g, m :: rest⟩ ∧
      ((∃ g', m = .after_run g' ∧ g' ≠ g ∧ b = { a with cfg := a.cfg.set 0 ⟨.cache v g, rest⟩ }) ∨
       (m = .after_run g ∧ b.cfg.stateOf 0 = some (.cache none (g + 1)) ∧
          b.timers = a.timers ++ [(0, .after_run (g + 1))]) ∨
       (m = .put 0 ∧ b.cfg.stateOf 0 = none) ∨
       ((∀ g', m ≠ .after_run g') ∧ m ≠ .put 0 ∧ ∃ v', (v' = v ∨ ∃ x, v' = some x) ∧
          b.cfg.stateOf 0 = some (.cache v' (g + 1)) ∧
          b.timers = a.timers ++ [(0, .after_run (g + 1))])) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  cases m with
  | put x =>
    cases x with
    | zero =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨h1, _⟩ | ⟨_, _, rfl⟩
      · cases h1
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, terminate_stateOf_self _ _ _⟩))
    | succ n =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · refine Or.inr (Or.inr (Or.inr ⟨(fun _ h => nomatch h), (fun h => nomatch h), some (n + 1),
          Or.inr ⟨_, rfl⟩, ?_, rfl⟩))
        show (a.cfg.set 0 _).stateOf 0 = _
        rw [stateOf_set, if_pos rfl]
      · cases hr
  | get r =>
    simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
    · refine Or.inr (Or.inr (Or.inr ⟨(fun _ h => nomatch h), (fun h => nomatch h), v, Or.inl rfl, ?_, rfl⟩))
      show ((a.cfg.set 0 _).deliver r _).stateOf 0 = _
      rw [stateOf_deliver, stateOf_set, if_pos rfl]
    · cases hr
  | after_run g' =>
    by_cases hg : g' = g
    · subst hg
      simp only [beh, if_true, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · refine Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)
        show (a.cfg.set 0 _).stateOf 0 = _
        rw [stateOf_set, if_pos rfl]
      · cases hr
    · simp only [beh, if_neg hg, applyEffects, List.foldl] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact Or.inl ⟨g', rfl, hg, rfl⟩
      · cases hr
  | ask =>
    simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
    · refine Or.inr (Or.inr (Or.inr ⟨(fun _ h => nomatch h), (fun h => nomatch h), v, Or.inl rfl, ?_, rfl⟩))
      show ((a.cfg.set 0 _).deliver 0 _).stateOf 0 = _
      rw [stateOf_deliver, stateOf_set, if_pos rfl]
    · cases hr
  | value w =>
    simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
    · refine Or.inr (Or.inr (Or.inr ⟨(fun _ h => nomatch h), (fun h => nomatch h), v, Or.inl rfl, ?_, rfl⟩))
      show ((a.cfg.set 0 _).deliver 0 _).stateOf 0 = _
      rw [stateOf_deliver, stateOf_set, if_pos rfl]
    · cases hr

/-- This program declares no DOWN codec: a `down` step only pops the queue. -/
theorem ttl_downE {a b : Sys St Msg} (h : downE sig a = some b) : ∃ rest, b = { a with downs := rest } := by
  obtain ⟨w, t, r, rest, _, hc⟩ := downE_cases h
  rcases hc with ⟨codec, hcodec, _, _⟩ | rfl
  · exact absurd hcodec (by simp [Gen.Ttl.sig])
  · exact ⟨rest, rfl⟩

/-- With no signal pending there is no signal step. -/
theorem no_signal_step {a b : Sys St Msg} (hs : a.signals = []) (h : signalE sig a = some b) : False := by
  simp [signalE, hs] at h

/-! ### `Good` along a run and under the environment -/

theorem Good.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hg : Good a) : Good b := by
  cases h with
  | run p _ hrun =>
    obtain ⟨hl, hs⟩ := run_links_signals hrun hg.links hg.signals
    have hn : 0 < b.next := Nat.lt_of_lt_of_le hg.next_pos (runE_next hrun)
    by_cases hp : p = 0
    · subst hp
      obtain ⟨st, m, rest, hget, _⟩ := runE_cases hrun
      obtain ⟨v, g, rfl⟩ := hg.cache st (by simp [stateOf, hget])
      obtain ⟨m', rest', hget', hcase⟩ := cache_run_cases (v := v) (g := g) (by simp [stateOf, hget]) hrun
      rcases hcase with ⟨g', rfl, hne, rfl⟩ | ⟨_, hst, ht⟩ | ⟨_, hst⟩ | ⟨_, _, v', _, hst, ht⟩
      · refine ⟨hn, hl, hs, ?_, ?_⟩
        · intro st' hst'
          rw [stateOf_set, if_pos rfl] at hst'
          exact ⟨v, g, (Option.some.inj hst').symm⟩
        · intro v₁ g₁ hat
          unfold At at hat
          rw [stateOf_set, if_pos rfl] at hat
          simp only [Option.some.injEq, Gen.Ttl.St.cache.injEq] at hat
          obtain ⟨rfl, rfl⟩ := hat
          rcases hg.armed v g (by simp [At, stateOf, hget']) with ht | ⟨mb, hmb, hm⟩
          · exact Or.inl ht
          · have hmb' : mb = .after_run g' :: rest' := by
              simp [Config.mboxOf, hget'] at hmb; exact hmb.symm
            subst hmb'
            refine Or.inr ⟨rest', by simp [mboxOf_set], ?_⟩
            rcases List.mem_cons.mp hm with h | h
            · exact absurd (Gen.Ttl.Msg.after_run.inj h).symm hne
            · exact h
      · refine ⟨hn, hl, hs, ?_, ?_⟩
        · intro st' hst'
          rw [hst] at hst'
          exact ⟨none, g + 1, (Option.some.inj hst').symm⟩
        · intro v₁ g₁ hat
          unfold At at hat
          rw [hst] at hat
          simp only [Option.some.injEq, Gen.Ttl.St.cache.injEq] at hat
          obtain ⟨rfl, rfl⟩ := hat
          exact Or.inl (by rw [ht]; exact List.mem_append_right _ List.mem_cons_self)
      · refine ⟨hn, hl, hs, ?_, ?_⟩
        · intro st' hst'
          rw [hst] at hst'
          cases hst'
        · intro v₁ g₁ hat
          unfold At at hat
          rw [hst] at hat
          cases hat
      · refine ⟨hn, hl, hs, ?_, ?_⟩
        · intro st' hst'
          rw [hst] at hst'
          exact ⟨v', g + 1, (Option.some.inj hst').symm⟩
        · intro v₁ g₁ hat
          unfold At at hat
          rw [hst] at hat
          simp only [Option.some.injEq, Gen.Ttl.St.cache.injEq] at hat
          obtain ⟨rfl, rfl⟩ := hat
          exact Or.inl (by rw [ht]; exact List.mem_append_right _ List.mem_cons_self)
    · refine ⟨hn, hl, hs, ?_, ?_⟩
      · intro st' hst'
        rw [runE_stateOf_of_ne hrun (Ne.symm hp) hg.next_pos] at hst'
        exact hg.cache st' hst'
      · intro v g hat
        have hat' : At v g a := by
          unfold At at hat ⊢
          rwa [runE_stateOf_of_ne hrun (Ne.symm hp) hg.next_pos] at hat
        obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp) hg.next_pos
        obtain ⟨tnew, htnew⟩ := runE_timers_append hrun
        exact (hg.armed v g hat').grow hnew htnew
  | signal _ hsig => exact (no_signal_step hg.signals hsig).elim
  | down _ hdown =>
    obtain ⟨rest, rfl⟩ := ttl_downE hdown
    exact ⟨hg.next_pos, hg.links, hg.signals, hg.cache, hg.armed⟩
  | timer i _ htimer =>
    obtain ⟨to, m, hm, rfl⟩ := timerE_cases htimer
    refine ⟨hg.next_pos, hg.links, hg.signals, ?_, ?_⟩
    · intro st hst
      rw [stateOf_deliver] at hst
      exact hg.cache st hst
    · intro v g hat
      have hat' : At v g a := by
        unfold At at hat ⊢
        rwa [stateOf_deliver] at hat
      rcases hg.armed v g hat' with ht | ⟨mb, hmb, hmem⟩
      · by_cases hx : (to, m) = (0, .after_run g)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
          obtain ⟨mb, hmb⟩ := hat'.mboxOf
          refine Or.inr ⟨mb ++ [.after_run g], ?_, List.mem_append_right _ List.mem_cons_self⟩
          show (a.cfg.deliver 0 (.after_run g)).mboxOf 0 = _
          rw [mboxOf_deliver_eq, if_pos rfl, hmb]; rfl
        · exact Or.inl (List.mem_eraseIdx_of_ne ht hm (Ne.symm hx))
      · obtain ⟨new, hnew⟩ := mboxOf_deliver a.cfg to 0 m
        exact Or.inr ⟨mb ++ new, by show (a.cfg.deliver to m).mboxOf 0 = _; rw [hnew, hmb]; rfl,
          List.mem_append_left _ hmem⟩

/-- An environment delivery keeps `Good`: anything to anyone, since `Good`
does not include `Inv`. -/
theorem Good.deliver {a : Sys St Msg} (p : Pid) (m : Msg) (hg : Good a) :
    Good { a with cfg := a.cfg.deliver p m } := by
  refine ⟨hg.next_pos, hg.links, hg.signals, ?_, ?_⟩
  · intro st hst
    rw [stateOf_deliver] at hst
    exact hg.cache st hst
  · intro v g hat
    have hat' : At v g a := by
      unfold At at hat ⊢
      rwa [stateOf_deliver] at hat
    obtain ⟨new, hnew⟩ := mboxOf_deliver a.cfg p 0 m
    exact (hg.armed v g hat').grow hnew (tnew := []) (by simp)

theorem Good.init : Good Examples.Ttl.init := by
  refine ⟨Nat.succ_pos 1, rfl, rfl, ?_, ?_⟩
  · intro st h
    simp [Examples.Ttl.init, stateOf, Config.get] at h
    exact ⟨none, 0, h.symm⟩
  · intro v g h
    simp [Examples.Ttl.init, At, stateOf, Config.get] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl List.mem_cons_self

theorem reach_good {s₀ s : Sys St Msg} (hg : Good s₀) (hr : SysReach beh sig s₀ s) : Good s :=
  hr.inv (fun h hg => hg.step h) hg

/-- Every system the environment can drive the cache to from `init` is `Good`. -/
theorem reachEnv_good {s : Sys St Msg} (hr : SysReachEnv beh sig init s) : Good s :=
  hr.inv (fun h hg => hg.step h) (fun p m hg => hg.deliver p m) Good.init

/-! ### Stage A: the pending timer fires -/

/-- The cache holds `v` at `g` and generation `g`'s timer is pending. -/
def TimerPending (v : Option Nat) (g : Nat) (s : Sys St Msg) : Prop :=
  At v g s ∧ (0, Gen.Ttl.Msg.after_run g) ∈ s.timers

/-- The cache holds `v` at `g` and generation `g`'s timer is in its mailbox. -/
def MsgPending (v : Option Nat) (g : Nat) (s : Sys St Msg) : Prop :=
  At v g s ∧ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ Gen.Ttl.Msg.after_run g ∈ mb

def isTimer (g : Nat) (x : Pid × Msg) : Bool := decide (x = (0, .after_run g))

def isAfter (g : Nat) (m : Msg) : Bool := decide (m = .after_run g)

/-- Stage A rank: how many timers are queued ahead of generation `g`'s. -/
def rankT (g : Nat) (s : Sys St Msg) : Nat := s.timers.findIdx (isTimer g)

/-- Stage B rank: how many messages are queued ahead of `after_run g` in the cache's mailbox. -/
def rankM (g : Nat) (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf 0 with
  | some mb => mb.findIdx (isAfter g)
  | none => 0

theorem isTimer_self (g : Nat) : isTimer g (0, .after_run g) = true := by simp [isTimer]

theorem isTimer_false {g : Nat} {x : Pid × Msg} (h : x ≠ (0, .after_run g)) : isTimer g x = false := by
  simp [isTimer, h]

theorem isAfter_self (g : Nat) : isAfter g (.after_run g) = true := by simp [isAfter]

theorem isAfter_false {g : Nat} {m : Msg} (h : m ≠ .after_run g) : isAfter g m = false := by
  simp [isAfter, h]

/-- One labelled step from a `TimerPending v g` state. -/
theorem timerPending_step {v : Option Nat} {g : Nat} {ch : SysChoice} {a b : Sys St Msg}
    (hg : Good a) (h : SysStepL beh sig ch a b) (hp : TimerPending v g a) :
    (MsgPending v g b ∨ ¬ At v g b) ∨
      (TimerPending v g b ∧ rankT g b ≤ rankT g a ∧ (ch = .timer 0 → rankT g b < rankT g a)) := by
  obtain ⟨hat, ht⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := cache_run_cases hat hrun
      rcases hcase with ⟨g', rfl, hne, rfl⟩ | ⟨_, hst, _⟩ | ⟨_, hst⟩ | ⟨_, _, v', _, hst, _⟩
      · exact Or.inr ⟨⟨at_set a v g rest, ht⟩, Nat.le_refl _, fun h => nomatch h⟩
      · exact Or.inl (Or.inr (not_at_of_gen hst))
      · exact Or.inl (Or.inr (not_at_of_none hst))
      · exact Or.inl (Or.inr (not_at_of_gen hst))
    · obtain ⟨new, hnew⟩ := runE_timers_append hrun
      have hat' : At v g b := by
        unfold At at hat ⊢
        rwa [runE_stateOf_of_ne hrun (Ne.symm hp0) hg.next_pos]
      refine Or.inr ⟨⟨hat', by rw [hnew]; exact List.mem_append_left _ ht⟩, ?_, fun h => nomatch h⟩
      unfold rankT
      rw [hnew, List.findIdx_append_of_mem ⟨_, ht, isTimer_self g⟩]
      exact Nat.le_refl _
  | signal _ _ hsig => exact (no_signal_step hg.signals hsig).elim
  | down _ _ hdown =>
    obtain ⟨rest, rfl⟩ := ttl_downE hdown
    exact Or.inr ⟨⟨hat, ht⟩, Nat.le_refl _, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨to, m, hm, rfl⟩ := timerE_cases htimer
    have hat' : At v g { a with cfg := a.cfg.deliver to m, timers := a.timers.eraseIdx i } := by
      show (a.cfg.deliver to m).stateOf 0 = _
      rw [stateOf_deliver]; exact hat
    by_cases hx : (to, m) = (0, .after_run g)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      obtain ⟨mb, hmb⟩ := hat.mboxOf
      refine Or.inl (Or.inl ⟨hat', mb ++ [.after_run g], ?_,
        List.mem_append_right _ List.mem_cons_self⟩)
      show (a.cfg.deliver 0 (.after_run g)).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl, hmb]; rfl
    · have hf : isTimer g (to, m) = false := isTimer_false hx
      refine Or.inr ⟨⟨hat', List.mem_eraseIdx_of_ne ht hm (Ne.symm hx)⟩, ?_, ?_⟩
      · show (a.timers.eraseIdx i).findIdx (isTimer g) ≤ a.timers.findIdx (isTimer g)
        exact List.findIdx_eraseIdx_le hm hf
      · intro hi
        have hi0 : i = 0 := SysChoice.timer.inj hi
        subst hi0
        show (a.timers.eraseIdx 0).findIdx (isTimer g) < a.timers.findIdx (isTimer g)
        exact List.findIdx_eraseIdx_zero hm hf

/-- **Stage A.** With the oldest timer fair, a pending timer of the current
generation leads to that timer in the mailbox, or to the cache leaving
`.cache v g`. -/
theorem timerPending_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (hfair : ρ.WeakFair (.timer 0)) (v : Option Nat) (g : Nat) :
    LeadsTo ρ.st (TimerPending v g) (fun s => MsgPending v g s ∨ ¬ At v g s) := by
  apply ρ.rank_leads_to_of_step (.timer 0) (rankT g) hfair
  · intro ch a b hr hl hp _
    exact timerPending_step (reach_good h0 hr) hl hp
  · intro a _ ⟨_, ht⟩ _
    show 0 < a.timers.length
    exact List.length_pos_of_mem ht

/-! ### Stage B: the timer message is processed -/

theorem rankM_of_mboxOf {g : Nat} {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf 0 = some mb) :
    rankM g s = mb.findIdx (isAfter g) := by
  unfold rankM; rw [h]

/-- The cache's mailbox only grew: `MsgPending` and the rank are kept. -/
theorem msgPending_grow {v : Option Nat} {g : Nat} {a b : Sys St Msg} (hat : At v g b)
    {mb : List Msg} (hmb : a.cfg.mboxOf 0 = some mb) (hmem : Gen.Ttl.Msg.after_run g ∈ mb)
    {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new)) :
    MsgPending v g b ∧ rankM g b ≤ rankM g a := by
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  refine ⟨⟨hat, mb ++ new, hnew, List.mem_append_left _ hmem⟩, ?_⟩
  rw [rankM_of_mboxOf hnew, rankM_of_mboxOf hmb, List.findIdx_append_of_mem ⟨_, hmem, isAfter_self g⟩]
  exact Nat.le_refl _

/-- One labelled step from a `MsgPending v g` state. -/
theorem msgPending_step {v : Option Nat} {g : Nat} {ch : SysChoice} {a b : Sys St Msg}
    (hg : Good a) (h : SysStepL beh sig ch a b) (hp : MsgPending v g a) :
    ¬ At v g b ∨ (MsgPending v g b ∧ rankM g b ≤ rankM g a ∧ (ch = .run 0 → rankM g b < rankM g a)) := by
  obtain ⟨hat, mb, hmb, hmem⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := cache_run_cases hat hrun
      have hmb' : mb = m :: rest := by
        simp [Config.mboxOf, hget] at hmb; exact hmb.symm
      subst hmb'
      rcases hcase with ⟨g', rfl, hne, rfl⟩ | ⟨_, hst, _⟩ | ⟨_, hst⟩ | ⟨_, _, v', _, hst, _⟩
      · have hrest : Gen.Ttl.Msg.after_run g ∈ rest := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd (Gen.Ttl.Msg.after_run.inj h).symm hne
          · exact h
        have hmbb : ({ a with cfg := a.cfg.set 0 ⟨.cache v g, rest⟩ } : Sys St Msg).cfg.mboxOf 0 = some rest := by
          simp [mboxOf_set]
        have hlt : rankM g { a with cfg := a.cfg.set 0 ⟨.cache v g, rest⟩ } < rankM g a := by
          rw [rankM_of_mboxOf hmbb, rankM_of_mboxOf hmb,
            List.findIdx_cons_of_false (isAfter_false (fun h => hne (Gen.Ttl.Msg.after_run.inj h)))]
          exact Nat.lt_succ_self _
        exact Or.inr ⟨⟨at_set a v g rest, rest, hmbb, hrest⟩, Nat.le_of_lt hlt, fun _ => hlt⟩
      · exact Or.inl (not_at_of_gen hst)
      · exact Or.inl (not_at_of_none hst)
      · exact Or.inl (not_at_of_gen hst)
    · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp0) hg.next_pos
      have hat' : At v g b := by
        unfold At at hat ⊢
        rwa [runE_stateOf_of_ne hrun (Ne.symm hp0) hg.next_pos]
      obtain ⟨h1, h2⟩ := msgPending_grow hat' hmb hmem hnew
      exact Or.inr ⟨h1, h2, fun h => absurd (SysChoice.run.inj h) hp0⟩
  | signal _ _ hsig => exact (no_signal_step hg.signals hsig).elim
  | down _ _ hdown =>
    obtain ⟨rest, rfl⟩ := ttl_downE hdown
    exact Or.inr ⟨⟨hat, mb, hmb, hmem⟩, Nat.le_refl _, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
    have hat' : At v g b := by
      unfold At at hat ⊢
      rwa [timerE_stateOf htimer]
    obtain ⟨h1, h2⟩ := msgPending_grow hat' hmb hmem hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage B.** With `run 0` fair, the current generation's timer in the
mailbox leads to the cache leaving `.cache v g`. -/
theorem msgPending_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (hfair : ρ.WeakFair (.run 0)) (v : Option Nat) (g : Nat) :
    LeadsTo ρ.st (MsgPending v g) (fun s => ¬ At v g s) := by
  apply ρ.rank_leads_to_of_step (.run 0) (rankM g) hfair
  · intro ch a b hr hl hp _
    exact msgPending_step (reach_good h0 hr) hl hp
  · intro a _ ⟨hat, mb, hmb, hmem⟩ _
    obtain ⟨mb', hget⟩ := hat.get
    have : mb = mb' := by simp [Config.mboxOf, hget] at hmb; exact hmb.symm
    subst this
    cases mb with
    | nil => cases hmem
    | cons m rest => exact ⟨_, m, rest, hget⟩

/-- Holding `v` at generation `g` leads to not holding `v` at `g`. -/
theorem at_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) (v : Option Nat) (g : Nat) :
    LeadsTo ρ.st (At v g) (fun s => ¬ At v g s) := by
  intro t hat
  have hg := reach_good h0 (ρ.reach t)
  have hB := msgPending_leadsTo ρ h0 hrun v g
  have hA := (timerPending_leadsTo ρ h0 htimer v g).trans (hB.or (LeadsTo.refl ρ.st _))
  rcases hg.armed v g hat with htm | ⟨mb, hmb, hmem⟩
  · exact hA t ⟨hat, htm⟩
  · exact hB t ⟨hat, mb, hmb, hmem⟩

/-! ### The theorem -/

/-- **A held value does not stay at its generation.** Along any run from a
`Good` system in which the oldest pending timer (`timer 0`) and the cache
(`run 0`) are weakly fair: if at time `t` the cache holds `some v` at
generation `g`, then at some `t' ≥ t` it still does, the step taken at
`t'` is `run 0`, and that step leaves generation `g` in one of exactly
three ways: the generation-`g` timer ran and the value is cleared
(`.cache none (g + 1)`); a message was processed and the timeout re-armed
(`.cache (some x) (g + 1)`, `x` the new or the kept value); or `put 0`
killed the cache. Nothing about `signal`, `down` or the reader is
assumed. -/
theorem gen_advances_or_clears (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t v g, (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g) →
      ∃ t' ≥ t, (ρ.st t').cfg.stateOf 0 = some (.cache (some v) g) ∧ ρ.ch t' = some (.run 0) ∧
        ((ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache none (g + 1)) ∨
         (∃ x, (ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache (some x) (g + 1))) ∨
         (ρ.st (t' + 1)).cfg.stateOf 0 = none) := by
  intro t v g hat
  obtain ⟨t₁, ht₁, hnot⟩ := at_leadsTo ρ h0 htimer hrun (some v) g t hat
  obtain ⟨u, htu, _, hu, hu1⟩ := exists_last (P := fun n => At (some v) g (ρ.st n)) ht₁ hat hnot
  have hg := reach_good h0 (ρ.reach u)
  refine ⟨u, htu, hu, ?_⟩
  rcases (ρ.step u).casesL with ⟨c, hc, hl⟩ | ⟨_, heq⟩
  · cases hl with
    | run _ p _ hrun =>
      by_cases hp0 : p = 0
      · subst hp0
        refine ⟨hc, ?_⟩
        obtain ⟨m, rest, hget, hcase⟩ := cache_run_cases hu hrun
        rcases hcase with ⟨g', rfl, hne, hb⟩ | ⟨_, hst, _⟩ | ⟨_, hst⟩ | ⟨_, _, v', hv', hst, _⟩
        · exfalso
          apply hu1
          show (ρ.st (u + 1)).cfg.stateOf 0 = _
          rw [hb]
          exact at_set _ _ _ _
        · exact Or.inl hst
        · exact Or.inr (Or.inr hst)
        · rcases hv' with rfl | ⟨x, rfl⟩
          · exact Or.inr (Or.inl ⟨v, hst⟩)
          · exact Or.inr (Or.inl ⟨x, hst⟩)
      · exfalso
        apply hu1
        show (ρ.st (u + 1)).cfg.stateOf 0 = _
        rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hg.next_pos]
        exact hu
    | signal _ _ hsig => exact (no_signal_step hg.signals hsig).elim
    | down _ _ hdown =>
      exfalso
      apply hu1
      show (ρ.st (u + 1)).cfg.stateOf 0 = _
      rw [downE_stateOf hdown]
      exact hu
    | timer _ i _ htimer =>
      exfalso
      apply hu1
      show (ρ.st (u + 1)).cfg.stateOf 0 = _
      rw [timerE_stateOf htimer]
      exact hu
  · exfalso
    apply hu1
    show (ρ.st (u + 1)).cfg.stateOf 0 = _
    rw [heq]
    exact hu

/-- The cache does not stay at generation `g`: eventually it is at another
generation or dead. -/
theorem gen_advances (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t v g, (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g) →
      ∃ t' ≥ t, ∀ v', (ρ.st t').cfg.stateOf 0 ≠ some (.cache v' g) := by
  intro t v g hat
  obtain ⟨t', htt, _, _, hout⟩ := gen_advances_or_clears ρ h0 htimer hrun t v g hat
  refine ⟨t' + 1, Nat.le_succ_of_le htt, fun v' h => ?_⟩
  rcases hout with h1 | ⟨x, h1⟩ | h1 <;> rw [h1] at h <;> simp at h

/-- The same in the shape "the generation changes or the value is
cleared", with the third case honesty requires: `put 0` kills the cache,
after which it is at no generation at all. -/
theorem gen_changes_or_clears (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t v g, (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g) →
      ∃ t' ≥ t, (∃ v' g', (ρ.st t').cfg.stateOf 0 = some (.cache v' g') ∧ g' ≠ g) ∨
        (∃ g', (ρ.st t').cfg.stateOf 0 = some (.cache none g')) ∨
        (ρ.st t').cfg.stateOf 0 = none := by
  intro t v g hat
  obtain ⟨t', htt, _, _, hout⟩ := gen_advances_or_clears ρ h0 htimer hrun t v g hat
  refine ⟨t' + 1, Nat.le_succ_of_le htt, ?_⟩
  rcases hout with h1 | ⟨x, h1⟩ | h1
  · exact Or.inr (Or.inl ⟨g + 1, h1⟩)
  · exact Or.inl ⟨some x, g + 1, h1, Nat.succ_ne_self g⟩
  · exact Or.inr (Or.inr h1)

/-- **The value expires** if nothing else happens to it: if from `t` on
the cache never processes a message at generation `g` (it never reaches
`.cache (some _) (g + 1)`) and never dies, then it is eventually
`.cache none (g + 1)`. (The premise "the generation never changes" would
be the wrong one: the after body itself moves to `g + 1`, so no fair run
satisfies it.) -/
theorem value_eventually_expires (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) (t : Nat) (v g : Nat)
    (hat : (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g))
    (hquiet : ∀ t' ≥ t, (∀ x, (ρ.st t').cfg.stateOf 0 ≠ some (.cache (some x) (g + 1))) ∧
      (ρ.st t').cfg.stateOf 0 ≠ none) :
    ∃ t' ≥ t, (ρ.st t').cfg.stateOf 0 = some (.cache none (g + 1)) := by
  obtain ⟨t', htt, _, _, hout⟩ := gen_advances_or_clears ρ h0 htimer hrun t v g hat
  refine ⟨t' + 1, Nat.le_succ_of_le htt, ?_⟩
  rcases hout with h1 | ⟨x, h1⟩ | h1
  · exact h1
  · exact absurd h1 ((hquiet (t' + 1) (Nat.le_succ_of_le htt)).1 x)
  · exact absurd h1 (hquiet (t' + 1) (Nat.le_succ_of_le htt)).2

/-- The same from any system the environment can drive the cache to from
`init` (a `put` has been delivered and processed, say). A closed run from
`init` itself never holds a value, so no `init` form is stated. -/
theorem gen_advances_or_clears_env (ρ : SysRun beh sig) (h0 : SysReachEnv beh sig init (ρ.st 0))
    (htimer : ρ.WeakFair (.timer 0)) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t v g, (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g) →
      ∃ t' ≥ t, (ρ.st t').cfg.stateOf 0 = some (.cache (some v) g) ∧ ρ.ch t' = some (.run 0) ∧
        ((ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache none (g + 1)) ∨
         (∃ x, (ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache (some x) (g + 1))) ∨
         (ρ.st (t' + 1)).cfg.stateOf 0 = none) :=
  gen_advances_or_clears ρ (reachEnv_good h0) htimer hrun

/-- Under weak fairness of every timer index, as the watchdog states it:
`WeakFair (.timer 0)` is the instance `i = 0`. -/
theorem gen_advances_or_clears_timers (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimers : ∀ i, ρ.WeakFair (.timer i)) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t v g, (ρ.st t).cfg.stateOf 0 = some (.cache (some v) g) →
      ∃ t' ≥ t, (ρ.st t').cfg.stateOf 0 = some (.cache (some v) g) ∧ ρ.ch t' = some (.run 0) ∧
        ((ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache none (g + 1)) ∨
         (∃ x, (ρ.st (t' + 1)).cfg.stateOf 0 = some (.cache (some x) (g + 1))) ∨
         (ρ.st (t' + 1)).cfg.stateOf 0 = none) :=
  gen_advances_or_clears ρ h0 (htimers 0) hrun

/-! ### Non-vacuity: a reachable premise and a fair run -/

/-- The cache at `.cache v g` with mailbox `mb`, the reader idle at pid 1,
pending timers `tm`. `init` is `W none 0 [] [(0, after_run 0)]`. -/
def W (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.cache v g, mb⟩
                     else if p = 1 then some ⟨.reader 0, []⟩ else none⟩
    next := 2, links := [], signals := [], timers := tm }

theorem init_eq_W : init = W none 0 [] [(0, .after_run 0)] := rfl

theorem W_get0 (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) :
    (W v g mb tm).cfg.get 0 = some ⟨.cache v g, mb⟩ := rfl

theorem W_set0 (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg))
    (v' : Option Nat) (g' : Nat) (mb' : List Msg) :
    (W v g mb tm).cfg.set 0 ⟨.cache v' g', mb'⟩ = (W v' g' mb' tm).cfg := by
  unfold W Config.set
  congr 1
  funext q
  by_cases hq : q = 0 <;> simp [hq]

theorem W_deliver0 (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) (m : Msg) :
    ({ W v g mb tm with cfg := (W v g mb tm).cfg.deliver 0 m } : Sys St Msg) = W v g (mb ++ [m]) tm := by
  have h : (W v g mb tm).cfg.deliver 0 m = (W v g mb tm).cfg.set 0 ⟨.cache v g, mb ++ [m]⟩ := by
    show Config.deliver _ 0 m = _
    unfold Config.deliver
    rfl
  rw [h, W_set0]
  rfl

theorem W_timer0 (v : Option Nat) (g : Nat) (mb : List Msg) (m : Msg) (tm : List (Pid × Msg)) :
    timerE (W v g mb ((0, m) :: tm)) 0 = some (W v g (mb ++ [m]) tm) := by
  have hd : (W v g mb ((0, m) :: tm)).cfg.deliver 0 m = (W v g (mb ++ [m]) ((0, m) :: tm)).cfg := by
    have h : (W v g mb ((0, m) :: tm)).cfg.deliver 0 m =
        (W v g mb ((0, m) :: tm)).cfg.set 0 ⟨.cache v g, mb ++ [m]⟩ := by
      show Config.deliver _ 0 m = _
      unfold Config.deliver
      rfl
    rw [h, W_set0]
  unfold timerE
  show some ({ W v g mb ((0, m) :: tm) with cfg := (W v g mb ((0, m) :: tm)).cfg.deliver 0 m, timers := (W v g mb ((0, m) :: tm)).timers.eraseIdx 0 } : Sys St Msg) = _
  rw [hd]
  rfl

theorem W_run_after (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) :
    runE beh (W v g (.after_run g :: mb) tm) 0 = some (W none (g + 1) mb (tm ++ [(0, .after_run (g + 1))])) := by
  unfold runE
  rw [W_get0]
  simp only [beh, if_true, applyEffects, List.foldl, applyEffect]
  rw [W_set0]
  rfl

theorem W_run_stale (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) {g' : Nat}
    (hg : g' ≠ g) :
    runE beh (W v g (.after_run g' :: mb) tm) 0 = some (W v g mb tm) := by
  unfold runE
  rw [W_get0]
  simp only [beh, if_neg hg, applyEffects, List.foldl]
  rw [W_set0]
  rfl

theorem W_run_put (v : Option Nat) (g : Nat) (mb : List Msg) (tm : List (Pid × Msg)) (n : Nat) :
    runE beh (W v g (.put (n + 1) :: mb) tm) 0 =
      some (W (some (n + 1)) (g + 1) mb (tm ++ [(0, .after_run (g + 1))])) := by
  unfold runE
  rw [W_get0]
  simp only [beh, applyEffects, List.foldl, applyEffect]
  rw [W_set0]
  rfl

/-- `.cache (some 5) 1` with only its own timer pending is reachable: the
environment delivers `put 5`, the cache runs it (generation 1), the stale
generation-0 timer fires and the cache ignores it. -/
theorem s0_reachable : SysReachEnv beh sig init (W (some 5) 1 [] [(0, .after_run 1)]) := by
  rw [init_eq_W]
  refine .env 0 (.put 5) ?_
  rw [W_deliver0]
  refine .step (.run _ 0 _ (W_run_put none 0 [] [(0, .after_run 0)] 4)) ?_
  refine .step (.timer _ 0 _ (W_timer0 (some 5) 1 [] (.after_run 0) [(0, .after_run 1)])) ?_
  refine .step (.run _ 0 _ (W_run_stale (some 5) 1 [] [(0, .after_run 1)] (by decide))) ?_
  exact .refl _

/-- The premise of `gen_advances_or_clears_env` is reachable. -/
theorem premise_reachable : ∃ s, SysReachEnv beh sig init s ∧ s.cfg.stateOf 0 = some (.cache (some 5) 1) :=
  ⟨_, s0_reachable, rfl⟩

/-- The value along the witness run: `some 5` until the first expiry, then nothing. -/
def wval : Nat → Option Nat
  | 0 => some 5
  | _ + 1 => none

/-- The witness run: at even times the timer of the current generation is
pending, at odd times it is in the mailbox; `timer 0` and `run 0` alternate
forever. -/
def wst (n : Nat) : Sys St Msg :=
  if n % 2 = 0 then W (wval (n / 2)) (n / 2 + 1) [] [(0, .after_run (n / 2 + 1))]
  else W (wval (n / 2)) (n / 2 + 1) [.after_run (n / 2 + 1)] []

def wch (n : Nat) : Option SysChoice := if n % 2 = 0 then some (.timer 0) else some (.run 0)

theorem wstep (n : Nat) : SysStepI beh sig (wch n) (wst n) (wst (n + 1)) := by
  by_cases hn : n % 2 = 0
  · have h1 : (n + 1) % 2 = 1 := by omega
    have h2 : (n + 1) / 2 = n / 2 := by omega
    have hch : wch n = some (.timer 0) := by simp [wch, hn]
    have hs : wst n = W (wval (n / 2)) (n / 2 + 1) [] [(0, .after_run (n / 2 + 1))] := by
      simp [wst, hn]
    have hs' : wst (n + 1) = W (wval (n / 2)) (n / 2 + 1) [.after_run (n / 2 + 1)] [] := by
      simp [wst, h1, h2]
    rw [hch, hs, hs']
    exact .step _ _ _ (.timer _ 0 _ (W_timer0 _ _ _ _ _))
  · have h1 : (n + 1) % 2 = 0 := by omega
    have h2 : (n + 1) / 2 = n / 2 + 1 := by omega
    have hch : wch n = some (.run 0) := by simp [wch, hn]
    have hs : wst n = W (wval (n / 2)) (n / 2 + 1) [.after_run (n / 2 + 1)] [] := by
      simp [wst, hn]
    have hs' : wst (n + 1) = W none (n / 2 + 1 + 1) [] [(0, .after_run (n / 2 + 1 + 1))] := by
      simp [wst, h1, h2, wval]
    rw [hch, hs, hs']
    exact .step _ _ _ (.run _ 0 _ (W_run_after _ _ _ _))

def wit : SysRun beh sig := ⟨wst, wch, wstep⟩

theorem wit_fair_timer : wit.WeakFair (.timer 0) :=
  Or.inr fun t => ⟨t + t % 2, Nat.le_add_right _ _, by
    have h : (t + t % 2) % 2 = 0 := by omega
    show wch (t + t % 2) = _
    simp [wch, h]⟩

theorem wit_fair_run : wit.WeakFair (.run 0) :=
  Or.inr fun t => ⟨t + 1 - t % 2, by omega, by
    have h : (t + 1 - t % 2) % 2 = 1 := by omega
    show wch (t + 1 - t % 2) = _
    simp [wch, h]⟩

/-- Along the witness run the cache is always alive at generation
`t / 2 + 1`, and holds `none` from generation 2 on. -/
theorem wit_stateOf (t : Nat) :
    (wit.st t).cfg.stateOf 0 = some (.cache (wval (t / 2)) (t / 2 + 1)) := by
  show (wst t).cfg.stateOf 0 = _
  unfold wst
  split <;> rfl

theorem wit_quiet (t : Nat) :
    (∀ x, (wit.st t).cfg.stateOf 0 ≠ some (.cache (some x) 2)) ∧ (wit.st t).cfg.stateOf 0 ≠ none := by
  rw [wit_stateOf]
  refine ⟨fun x h => ?_, fun h => nomatch h⟩
  simp only [Option.some.injEq, Gen.Ttl.St.cache.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : t / 2 = 1 := by omega
  rw [h3] at h1
  cases h1

/-- **A fair run exists** from a reachable system that satisfies the
premise: `wit` starts at `.cache (some 5) 1` (reachable, `s0_reachable`),
is weakly fair for `timer 0` and for `run 0`, takes a real step at every
time, and has expired the value by time 2. -/
theorem fair_run_exists : ∃ ρ : SysRun beh sig, SysReachEnv beh sig init (ρ.st 0) ∧
    ρ.WeakFair (.timer 0) ∧ ρ.WeakFair (.run 0) ∧
    (ρ.st 0).cfg.stateOf 0 = some (.cache (some 5) 1) ∧ (∀ t, ρ.ch t ≠ none) ∧
    (ρ.st 2).cfg.stateOf 0 = some (.cache none 2) :=
  ⟨wit, s0_reachable, wit_fair_timer, wit_fair_run, rfl,
    fun t => by show wch t ≠ none; unfold wch; split <;> exact (fun h => nomatch h), rfl⟩

/-- Along `wit` the value `some 5` at generation 1 is cleared at time 2:
the conclusion of `gen_changes_or_clears` is witnessed by its second case. -/
theorem wit_clears : ∃ t' ≥ 0, (∃ v' g', (wit.st t').cfg.stateOf 0 = some (.cache v' g') ∧ g' ≠ 1) ∨
    (∃ g', (wit.st t').cfg.stateOf 0 = some (.cache none g')) ∨ (wit.st t').cfg.stateOf 0 = none :=
  ⟨2, Nat.zero_le 2, Or.inr (Or.inl ⟨2, rfl⟩)⟩

/-- The corollary's premise is satisfiable: along `wit` no message is ever
processed and the cache never dies, and the conclusion is witnessed. -/
theorem wit_expires : ∃ t' ≥ 0, (wit.st t').cfg.stateOf 0 = some (.cache none (1 + 1)) :=
  value_eventually_expires wit (reachEnv_good s0_reachable) wit_fair_timer wit_fair_run 0 5 1 rfl
    (fun t _ => wit_quiet t)

end Examples.Ttl

end Leanactors
