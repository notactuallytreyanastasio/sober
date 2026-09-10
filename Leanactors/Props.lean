import Leanactors.Core
/-!
# Leanactors.Props

Metatheory of the actor model. Four results:

1. **Frame rule**: a step changes at most one actor's state.
2. **Domain preservation**: steps never create or kill actors (until we add spawn/exit).
3. **Mailboxes are queues**: a step pops at most one message from the head
   of each mailbox and only ever appends to the tail. Per-pair FIFO is a
   corollary.
4. **Invariant induction**: if every behaviour preserves `P` on the actor's
   own state, `P` holds on every state in every reachable configuration.
   This is the rule you use to prove GenServer invariants.

Plus `step_sound` / `run_sound`: the executable interpreter only produces
configurations the relational semantics admits, so `#eval` traces are
witnesses of `Reach`.
-/
namespace Leanactors

variable {σ μ : Type}

namespace Config

/-- Projection helpers. -/
def stateOf (c : Config σ μ) (q : Pid) : Option σ := (c.get q).map Actor.state
def mboxOf (c : Config σ μ) (q : Pid) : Option (List μ) := (c.get q).map Actor.mailbox

@[simp] theorem get_set_self (c : Config σ μ) (p : Pid) (a : Actor σ μ) :
    (c.set p a).get p = some a := by
  simp [get, set]

theorem get_set_ne (c : Config σ μ) {p q : Pid} (a : Actor σ μ) (h : q ≠ p) :
    (c.set p a).get q = c.get q := by
  simp [get, set, h]

/-! ### deliver / deliverAll never touch states -/

theorem stateOf_deliver (c : Config σ μ) (p q : Pid) (m : μ) :
    (c.deliver p m).stateOf q = c.stateOf q := by
  unfold deliver stateOf
  cases h : c.actors p with
  | none => rfl
  | some a =>
    by_cases hq : q = p
    · subst hq; simp [get, set, h]
    · simp [get, set, hq]

theorem stateOf_deliverAll (c : Config σ μ) (l : List (Pid × μ)) (q : Pid) :
    (c.deliverAll l).stateOf q = c.stateOf q := by
  induction l generalizing c with
  | nil => rfl
  | cons pm rest ih =>
    obtain ⟨p, m⟩ := pm
    simp only [deliverAll]
    rw [ih, stateOf_deliver]

/-! ### deliver / deliverAll only append to mailboxes -/

theorem mboxOf_deliver (c : Config σ μ) (p q : Pid) (m : μ) :
    ∃ new : List μ, (c.deliver p m).mboxOf q = (c.mboxOf q).map (· ++ new) := by
  unfold deliver mboxOf
  cases h : c.actors p with
  | none => exact ⟨[], by simp [Function.comp_def]⟩
  | some a =>
    by_cases hq : q = p
    · subst hq; exact ⟨[m], by simp [get, set, h]⟩
    · exact ⟨[], by simp [get, set, hq, Function.comp_def]⟩

theorem mboxOf_deliverAll (c : Config σ μ) (l : List (Pid × μ)) (q : Pid) :
    ∃ new : List μ, (c.deliverAll l).mboxOf q = (c.mboxOf q).map (· ++ new) := by
  induction l generalizing c with
  | nil => exact ⟨[], by simp [deliverAll]⟩
  | cons pm rest ih =>
    obtain ⟨p, m⟩ := pm
    simp only [deliverAll]
    obtain ⟨n1, h1⟩ := mboxOf_deliver c p q m
    obtain ⟨n2, h2⟩ := ih (c.deliver p m)
    refine ⟨n1 ++ n2, ?_⟩
    rw [h2, h1, Option.map_map]
    congr 1
    funext l
    simp [Function.comp, List.append_assoc]

/-! ### Domain preservation -/

theorem isSome_deliverAll (c : Config σ μ) (l : List (Pid × μ)) (q : Pid) :
    ((c.deliverAll l).get q).isSome = (c.get q).isSome := by
  have h := stateOf_deliverAll c l q
  unfold stateOf at h
  have := congrArg Option.isSome h
  simpa [Option.isSome_map] using this

end Config

open Config

/-! ## Theorems about `Step` -/

/-- **Frame rule.** Every step names a single pid `p`; every other actor's
state is untouched. -/
theorem Step.frame {beh : Behavior σ μ} {c c' : Config σ μ} (h : Step beh c c') :
    ∃ p, ∀ q, q ≠ p → c'.stateOf q = c.stateOf q := by
  cases h with
  | run p s m rest hget =>
    refine ⟨p, fun q hq => ?_⟩
    rw [stateOf_deliverAll]
    unfold stateOf
    rw [get_set_ne _ _ hq]

/-- **Domain preservation.** No step creates or destroys an actor. -/
theorem Step.domain {beh : Behavior σ μ} {c c' : Config σ μ} (h : Step beh c c') :
    ∀ q, (c'.get q).isSome = (c.get q).isSome := by
  intro q
  cases h with
  | run p s m rest hget =>
    rw [isSome_deliverAll]
    by_cases hq : q = p
    · subst hq; simp [hget]
    · rw [get_set_ne _ _ hq]

/-- **Mailboxes are queues.** For every actor `q`, its mailbox after a step is
its old mailbox with at most one element dropped from the *head* and some
list appended to the *tail*. Nothing is reordered, nothing is inserted in
the middle. -/
theorem Step.queue {beh : Behavior σ μ} {c c' : Config σ μ} (h : Step beh c c') :
    ∀ q, ∃ k, k ≤ 1 ∧ ∃ new : List μ,
      c'.mboxOf q = (c.mboxOf q).map (fun l => l.drop k ++ new) := by
  intro q
  cases h with
  | run p s m rest hget =>
    obtain ⟨new, hnew⟩ := mboxOf_deliverAll (c.set p ⟨(beh p s m).1, rest⟩) (beh p s m).2 q
    rw [hnew]
    by_cases hq : q = p
    · subst hq
      refine ⟨1, Nat.le_refl _, new, ?_⟩
      unfold mboxOf
      simp [hget]
    · refine ⟨0, Nat.zero_le _, new, ?_⟩
      unfold mboxOf
      rw [get_set_ne _ _ hq]
      simp

/-! ## Invariants -/

/-- `P` holds on the state of every live actor. -/
def AllStates (P : σ → Prop) (c : Config σ μ) : Prop :=
  ∀ p a, c.get p = some a → P a.state

/-- A behaviour *preserves* `P` if handling any message keeps `P`. Note this
says nothing about the messages sent; it is purely about local state. -/
def Preserves (beh : Behavior σ μ) (P : σ → Prop) : Prop :=
  ∀ p s m, P s → P (beh p s m).1

/-- Establishing an invariant initially: `ofList` satisfies `P` if every
listed initial state does. -/
theorem Config.ofList_allStates {P : σ → Prop} (xs : List (Pid × σ))
    (hxs : ∀ x ∈ xs, P x.2) : AllStates P (Config.ofList xs : Config σ μ) := by
  intro p a h
  simp only [Config.ofList, Config.get, Option.map_eq_some_iff] at h
  obtain ⟨⟨q, s⟩, hf, rfl⟩ := h
  exact hxs _ (List.mem_of_find?_eq_some hf)

/-- External delivery (a shell doing `GenServer.cast`) touches no state, so
it preserves any state invariant. -/
theorem Config.deliverAll_allStates {P : σ → Prop} {c : Config σ μ}
    (l : List (Pid × μ)) (hc : AllStates P c) : AllStates P (c.deliverAll l) := by
  intro q a h
  have hs := stateOf_deliverAll c l q
  unfold stateOf at hs
  rw [h] at hs
  cases hcq : c.get q with
  | none => rw [hcq] at hs; simp at hs
  | some b => rw [hcq] at hs; simp at hs; rw [hs]; exact hc _ _ hcq

/-- **Invariant induction, single step.** -/
theorem Step.preserves {beh : Behavior σ μ} {P : σ → Prop} (hb : Preserves beh P)
    {c c' : Config σ μ} (h : Step beh c c') (hc : AllStates P c) : AllStates P c' := by
  intro q a hq
  cases h with
  | run p s m rest hget =>
    have hs := stateOf_deliverAll (c.set p ⟨(beh p s m).1, rest⟩) (beh p s m).2 q
    unfold stateOf at hs
    rw [hq] at hs
    by_cases hqp : q = p
    · subst hqp
      simp at hs
      rw [hs]
      exact hb _ s m (hc _ _ hget)
    · rw [get_set_ne _ _ hqp] at hs
      cases hcq : c.get q with
      | none => rw [hcq] at hs; simp at hs
      | some b =>
        rw [hcq] at hs
        simp at hs
        rw [hs]
        exact hc _ _ hcq

/-- **Invariant induction, reachability.** This is the theorem you actually
use: establish `P` initially, show each handler preserves it, conclude it
holds forever under *any* scheduler. -/
theorem Reach.preserves {beh : Behavior σ μ} {P : σ → Prop} (hb : Preserves beh P)
    {c c' : Config σ μ} (h : Reach beh c c') (hc : AllStates P c) : AllStates P c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hs.preserves hb hc)

/-! ## Executable semantics agree with relational semantics -/

theorem step_sound {beh : Behavior σ μ} {c c' : Config σ μ} {p : Pid}
    (h : step beh c p = some c') : Step beh c c' := by
  unfold step at h
  split at h
  · rename_i s m rest hget
    cases h
    exact .run _ p s m rest hget
  · cases h

theorem run_sound {beh : Behavior σ μ} (c : Config σ μ) (sched : List Choice) :
    Reach beh c (run beh c sched) := by
  induction sched generalizing c with
  | nil => exact .refl c
  | cons p ps ih =>
    simp only [run]
    cases hs : step beh c p with
    | none => exact .refl c
    | some c' => exact .step (step_sound hs) (ih c')

end Leanactors
