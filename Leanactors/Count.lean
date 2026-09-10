import Leanactors.Props
/-!
# Leanactors.Count

Message counting. Cross-actor invariants (mutual exclusion, at-most-once
delivery, token conservation) are almost always stated as arithmetic over
"how many copies of message `m` are in `q`'s mailbox". This file gives
`Config.mcount` and one lemma, `Step.chars`, that characterises a step
entirely in terms of states and counts so that example proofs never have to
unfold `deliverAll` again.

Also here: `Reach.inv`, the general (config-level) invariant induction
principle, and `Step.prefix`, the FIFO corollary of the queue lemma.
-/

namespace Leanactors

variable {σ μ : Type}

/-! ## General config-level invariants -/

/-- **Config-level invariant induction.** `AllStates` is the special case
where `I` only looks at states one actor at a time. -/
theorem Reach.inv {beh : Behavior σ μ} {I : Config σ μ → Prop}
    (hstep : ∀ {a b}, Step beh a b → I a → I b)
    {c c' : Config σ μ} (h : Reach beh c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hstep hs hc)

/-- **FIFO corollary.** Whatever survives of an old mailbox is a prefix of
the new one: no reordering, ever. -/
theorem Step.prefix {beh : Behavior σ μ} {c c' : Config σ μ} (h : Step beh c c') :
    ∀ q old new, c.mboxOf q = some old → c'.mboxOf q = some new →
      ∃ k, k ≤ 1 ∧ (old.drop k).IsPrefix new := by
  intro q old new hold hnew
  obtain ⟨k, hk, fresh, hq⟩ := h.queue q
  refine ⟨k, hk, ?_⟩
  rw [hq, hold] at hnew
  simp at hnew
  rw [← hnew]
  exact List.prefix_append _ _

/-! ## Counting -/

namespace Config

variable [DecidableEq μ]

/-- Number of copies of `m` in `q`'s mailbox (0 if `q` does not exist). -/
def mcount (c : Config σ μ) (q : Pid) (m : μ) : Nat :=
  match c.get q with
  | some a => a.mailbox.count m
  | none => 0

omit [DecidableEq μ] in
theorem stateOf_set (c : Config σ μ) (p q : Pid) (a : Actor σ μ) :
    (c.set p a).stateOf q = if q = p then some a.state else c.stateOf q := by
  by_cases h : q = p
  · subst h; simp [stateOf, get_set_self]
  · simp [stateOf, get_set_ne _ _ h, h]

omit [DecidableEq μ] in
theorem isSome_set (c : Config σ μ) (p q : Pid) (a : Actor σ μ) :
    ((c.set p a).get q).isSome = if q = p then true else (c.get q).isSome := by
  by_cases h : q = p
  · subst h; simp [get_set_self]
  · simp [get_set_ne _ _ h, h]

theorem mcount_set (c : Config σ μ) (p q : Pid) (a : Actor σ μ) (m : μ) :
    (c.set p a).mcount q m = if q = p then a.mailbox.count m else c.mcount q m := by
  by_cases h : q = p
  · subst h; simp [mcount, get_set_self]
  · simp [mcount, get_set_ne _ _ h, h]

omit [DecidableEq μ] in
theorem isSome_deliver (c : Config σ μ) (p q : Pid) (m : μ) :
    ((c.deliver p m).get q).isSome = (c.get q).isSome := by
  have h := stateOf_deliver c p q m
  unfold stateOf at h
  have := congrArg Option.isSome h
  simpa [Option.isSome_map] using this

theorem mcount_deliver (c : Config σ μ) (p q : Pid) (m m' : μ) :
    (c.deliver p m').mcount q m =
      c.mcount q m + if q = p ∧ m' = m ∧ (c.get q).isSome then 1 else 0 := by
  unfold deliver
  cases hp : c.actors p with
  | none =>
    by_cases h : q = p
    · subst h; simp [get, hp]
    · simp [h]
  | some a =>
    by_cases h : q = p
    · subst h
      simp only [mcount]
      rw [get_set_self]
      simp only [get, hp, List.count_append, Option.isSome_some, and_true, true_and]
      by_cases hm : m' = m <;> simp [hm]
    · simp [mcount, get_set_ne _ _ h, h]

theorem mcount_deliverAll (c : Config σ μ) (l : List (Pid × μ)) (q : Pid) (m : μ) :
    (c.deliverAll l).mcount q m =
      c.mcount q m + if (c.get q).isSome then l.count (q, m) else 0 := by
  induction l generalizing c with
  | nil => simp [deliverAll]
  | cons pm rest ih =>
    obtain ⟨p, m'⟩ := pm
    simp only [deliverAll]
    rw [ih, mcount_deliver, isSome_deliver, List.count_cons]
    by_cases hs : (c.get q).isSome
    · simp only [hs, and_true, if_true]
      by_cases hqp : q = p <;> by_cases hm : m' = m <;> simp [hqp, hm]
      · omega
      · exact fun h => hqp h.symm
    · simp [hs]

omit [DecidableEq μ] in
/-- Existence from a known state. -/
theorem isSome_of_stateOf {c : Config σ μ} {q : Pid} {s : σ}
    (h : c.stateOf q = some s) : (c.get q).isSome = true := by
  unfold stateOf at h
  cases hq : c.get q with
  | none => rw [hq] at h; simp at h
  | some _ => rfl

/-- A missing actor has an empty count. -/
theorem mcount_of_stateOf_none {c : Config σ μ} {q : Pid}
    (h : c.stateOf q = none) (m : μ) : c.mcount q m = 0 := by
  unfold stateOf at h
  unfold mcount
  cases hq : c.get q with
  | none => rfl
  | some _ => rw [hq] at h; simp at h

end Config

open Config

/-- **Step characterisation.** Every step is: some actor `p` in state `s`
pops `m` off its mailbox (leaving `rest`), moves to `(beh s m).1`, and the
sends `(beh s m).2` are appended to existing mailboxes. Stated purely in
terms of `stateOf` and `mcount` so downstream proofs are arithmetic. -/
theorem Step.chars [DecidableEq μ] {beh : Behavior σ μ} {c c' : Config σ μ}
    (h : Step beh c c') :
    ∃ p s m rest, c.get p = some ⟨s, m :: rest⟩ ∧
      (∀ q, c'.stateOf q = if q = p then some (beh s m).1 else c.stateOf q) ∧
      (∀ q m', c'.mcount q m' =
        (if q = p then rest.count m' else c.mcount q m') +
        if (c.get q).isSome then (beh s m).2.count (q, m') else 0) := by
  cases h with
  | run p s m rest hget =>
    refine ⟨p, s, m, rest, hget, fun q => ?_, fun q m' => ?_⟩
    · rw [stateOf_deliverAll, stateOf_set]
    · rw [mcount_deliverAll, mcount_set, isSome_set]
      by_cases hq : q = p
      · subst hq; simp [hget]
      · simp [hq]

/-- Popping the head: the count in `p`'s own mailbox before the step. -/
theorem mcount_of_get [DecidableEq μ] {c : Config σ μ} {p : Pid} {s : σ} {m : μ} {rest : List μ}
    (h : c.get p = some ⟨s, m :: rest⟩) (m' : μ) :
    c.mcount p m' = rest.count m' + if m = m' then 1 else 0 := by
  simp [mcount, h, List.count_cons]

end Leanactors
