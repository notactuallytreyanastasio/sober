import Leanactors.SysProps
import Leanactors.Examples.Ttl
/-!
# Leanactors.Examples.TtlProof

The cache never holds 0 and no `value (some 0)` is ever in flight, in
every configuration reachable from `init` under any scheduler and any
order of timer firings.

`Inv` is stated for every pid, not only the cache at 0 and the reader at
1, so no case needs to know who is alive: every actor in a cache state
holds something other than 0, no mailbox contains `value (some 0)`, and no
pending timer carries one. Nobody spawns, links, monitors or traps, so the
only steps that look at a message are the actors' own clauses (`Inv.run`,
by the concrete effect list of each clause, with the case split on the
popped state and message); signal, DOWN and timer steps are deliveries or
deaths, which the `SysProps` case lemmas unpack. The generation counter
plays no part in safety: a stale `after_run` is consumed and ignored
(`stale_ignored`), a live one only clears the value, and neither can put
a 0 anywhere.
-/

namespace Leanactors.Examples.Ttl

open Leanactors Config Sys

structure Inv (s : Sys St Msg) : Prop where
  /-- No cache, wherever it lives, holds 0. -/
  cache_ok : ∀ p v g, s.cfg.stateOf p = some (.cache v g) → v ≠ some 0
  /-- No mailbox holds a `value (some 0)`. -/
  no_zero : ∀ p, s.cfg.mcount p (.value (some 0)) = 0
  /-- No pending timer carries one either. -/
  timers_ok : ∀ x ∈ s.timers, x.2 ≠ .value (some 0)

/-! ### The semantics of the generation, in one line -/

/-- An `after_run` of any generation but the current one does nothing. -/
theorem stale_ignored (me fresh : Pid) (v : Option Nat) {g g' : Nat} (hg : g' ≠ g) :
    beh me fresh (.cache v g) (.after_run g') = (.cache v g, []) := by
  simp [beh, hg]

/-! ### Building blocks -/

/-- The message an actor with an empty count pops is not a `value (some 0)`. -/
theorem Inv.popped_ne {a : Sys St Msg} (hi : Inv a) {p : Pid} {st : St} {m : Msg}
    {rest : List Msg} (hget : a.cfg.get p = some ⟨st, m :: rest⟩) : m ≠ .value (some 0) := by
  intro hm
  have h := hi.no_zero p
  rw [mcount_of_get hget, if_pos hm] at h
  omega

theorem Inv.rest_count {a : Sys St Msg} (hi : Inv a) {p : Pid} {st : St} {m : Msg}
    {rest : List Msg} (hget : a.cfg.get p = some ⟨st, m :: rest⟩) :
    rest.count (.value (some 0)) = 0 := by
  have h := hi.no_zero p
  rw [mcount_of_get hget] at h
  omega

/-- Popping `p`'s message and moving to a state that is not a 0-holding cache. -/
theorem Inv.set {a : Sys St Msg} (hi : Inv a) {p : Pid} {st : St} {m : Msg} {rest : List Msg}
    (hget : a.cfg.get p = some ⟨st, m :: rest⟩) {st' : St}
    (hst : ∀ v g, st' = .cache v g → v ≠ some 0) :
    Inv { a with cfg := a.cfg.set p ⟨st', rest⟩ } := by
  refine ⟨?_, ?_, hi.timers_ok⟩
  · intro q v g h
    simp only [stateOf_set] at h
    split at h
    · exact hst v g (Option.some.inj h)
    · exact hi.cache_ok q v g h
  · intro q
    simp only [mcount_set]
    split
    · exact hi.rest_count hget
    · exact hi.no_zero q

/-- Delivering anything but a `value (some 0)`, to anyone. -/
theorem Inv.deliver {a : Sys St Msg} (hi : Inv a) (q : Pid) {m : Msg} (hm : m ≠ .value (some 0)) :
    Inv { a with cfg := a.cfg.deliver q m } := by
  refine ⟨?_, ?_, hi.timers_ok⟩
  · intro p v g h
    simp only [stateOf_deliver] at h
    exact hi.cache_ok p v g h
  · intro p
    simp [mcount_deliver, hi.no_zero p, hm]

/-- Arming an `after_run` timer. -/
theorem Inv.arm {a : Sys St Msg} (hi : Inv a) (p : Pid) (g : Nat) :
    Inv { a with timers := a.timers ++ [(p, .after_run g)] } := by
  refine ⟨hi.cache_ok, hi.no_zero, ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hi.timers_ok x hx
  · simp

/-- A death, anyone's. -/
theorem Inv.terminate {a : Sys St Msg} (hi : Inv a) (p : Pid) (r : Reason) :
    Inv (a.terminate p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q v g h
    rw [terminate_stateOf] at h
    split at h
    · cases h
    · exact hi.cache_ok q v g h
  · intro q
    rw [terminate_mcount]
    split
    · rfl
    · exact hi.no_zero q
  · intro x hx
    rw [terminate_timers] at hx
    exact hi.timers_ok x hx

/-! ### Preservation, one lemma per kind of step -/

/-- The cache's and the reader's steps, clause by clause. Every clause is
`set` (the new state, the popped mailbox) followed by at most one `send`
and one `sendAfter`, or by an `exit`. -/
theorem Inv.run {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a) : Inv b := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  have hm := hi.popped_ne hget
  cases st with
  | cache v g =>
    have hv : v ≠ some 0 := hi.cache_ok p v g (by simp [stateOf, hget])
    have hkeep : ∀ gg v' g', (.cache v gg : St) = .cache v' g' → v' ≠ some 0 := fun _ _ _ h => by cases h; exact hv
    cases m with
    | put x =>
      cases x with
      | zero =>
        simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
        rcases hs' with ⟨h1, _⟩ | ⟨_, _, rfl⟩
        · cases h1
        · exact (hi.set hget (hkeep _)).terminate p _
      | succ n =>
        simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
        rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
        · exact (hi.set hget (fun _ _ h => by cases h; simp)).arm p _
        · cases hr
    | get r =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact ((hi.set hget (hkeep _)).deliver r (m := .value v) (by simpa using hv)).arm p _
      · cases hr
    | after_run g' =>
      by_cases hg : g' = g
      · subst hg
        simp only [beh, if_true, applyEffects, List.foldl, applyEffect] at hs'
        rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
        · exact (hi.set hget (fun _ _ h => by cases h; simp)).arm p _
        · cases hr
      · simp only [beh, if_neg hg, applyEffects, List.foldl] at hs'
        rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
        · exact hi.set hget (hkeep _)
        · cases hr
    | ask =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact ((hi.set hget (hkeep _)).deliver p hm).arm p _
      · cases hr
    | value w =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact ((hi.set hget (hkeep _)).deliver p hm).arm p _
      · cases hr
  | reader n =>
    have hkeep : ∀ v' g', (.reader n : St) = .cache v' g' → v' ≠ some 0 := fun _ _ h => by cases h
    have hkeep' : ∀ v' g', (.reader (n + 1) : St) = .cache v' g' → v' ≠ some 0 := fun _ _ h => by cases h
    cases m with
    | ask =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact (hi.set hget hkeep).deliver cache (by simp)
      · cases hr
    | value w =>
      simp only [beh, applyEffects, List.foldl] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact hi.set hget hkeep'
      · cases hr
    | _ =>
      simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact (hi.set hget hkeep).deliver p hm
      · cases hr

/-- Nobody traps, so a signal either vanishes or kills its target. The
proof does not even need that: a trapped signal would be a delivery of
`sig.exitMsg`, which is not a `value`. -/
theorem Inv.signal {a b : Sys St Msg} (h : signalE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨q, _, _, rest, _, hc⟩ := signalE_cases h
  have hpop : Inv { a with signals := rest } := ⟨hi.cache_ok, hi.no_zero, hi.timers_ok⟩
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact hpop
  · exact hpop.deliver q (by simp [Gen.Ttl.sig])
  · exact hpop
  · exact hpop.terminate q .error
  · exact hpop.terminate q .error

/-- This program declares no DOWN codec, so a DOWN step only pops the queue. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, rest, _, hc⟩ := downE_cases h
  rcases hc with ⟨codec, hcodec, _, _⟩ | rfl
  · exact absurd hcodec (by simp [Gen.Ttl.sig])
  · exact ⟨hi.cache_ok, hi.no_zero, hi.timers_ok⟩

/-- A timer firing delivers what it carries, which is never a `value (some 0)`. -/
theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b := by
  obtain ⟨to, m, hm, rfl⟩ := timerE_cases h
  have hne : m ≠ .value (some 0) := hi.timers_ok (to, m) (List.mem_of_getElem? hm)
  have herase : Inv { a with timers := a.timers.eraseIdx i } :=
    ⟨hi.cache_ok, hi.no_zero, fun x hx => hi.timers_ok x (List.mem_of_mem_eraseIdx hx)⟩
  exact herase.deliver to hne

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  cases h with
  | run p _ hrun => exact hi.run hrun
  | signal _ hsig => exact hi.signal hsig
  | down _ hdown => exact hi.down hdown
  | timer i _ htimer => exact hi.timer htimer

/-! ### From the initial system -/

theorem init_inv : Inv init := by
  refine ⟨?_, ?_, ?_⟩
  · intro p v g h
    by_cases h0 : p = 0
    · subst h0
      simp [init, stateOf, Config.get] at h
      obtain ⟨rfl, _⟩ := h
      simp
    · by_cases h1 : p = 1
      · subst h1
        simp [init, stateOf, Config.get] at h
      · simp [init, stateOf, Config.get, h0, h1] at h
  · intro p
    by_cases h0 : p = 0
    · subst h0
      simp [init, mcount, Config.get]
    · by_cases h1 : p = 1
      · subst h1
        simp [init, mcount, Config.get]
      · simp [init, mcount, Config.get, h0, h1]
  · intro x hx
    simp only [init, List.mem_singleton] at hx
    subst hx
    simp

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv (fun h hi => Inv.step h hi) init_inv

/-- **The cache never holds 0**, at any generation. -/
theorem cache_never_zero {s : Sys St Msg} (hr : SysReach beh sig init s) (g : Nat) :
    s.cfg.stateOf cache ≠ some (.cache (some 0) g) :=
  fun h => (reach_inv hr).cache_ok cache (some 0) g h rfl

/-- **No `value (some 0)` is ever in flight**, to the reader or to anyone. -/
theorem no_zero_in_flight {s : Sys St Msg} (hr : SysReach beh sig init s) (p : Pid) :
    s.cfg.mcount p (.value (some 0)) = 0 :=
  (reach_inv hr).no_zero p

/-- The same for the generated behaviour, through `beh_eq_gen`. -/
theorem cache_never_zero_gen {s : Sys St Msg} (hr : SysReach Gen.Ttl.beh sig init s) (g : Nat) :
    s.cfg.stateOf cache ≠ some (.cache (some 0) g) := by
  rw [beh_eq_gen] at hr
  exact cache_never_zero hr g

end Leanactors.Examples.Ttl
