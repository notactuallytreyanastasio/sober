/-!
# Leanactors.SetList

`MapSet`, the model of which is a list without duplicates, in insertion
order. The translator renders `MapSet.t(T)` as `List T` and the `MapSet`
calls as the functions below: `MapSet.new()` is `[]`, `MapSet.new(l)` is
`ofList`, `MapSet.put` is `insert`, `MapSet.delete` is `erase`,
`MapSet.member?` is `contains`, `MapSet.size` is `size`, `MapSet.to_list`
is `toList`, and `union`, `difference` and `intersection` keep their names.

A `MapSet` is unordered on the BEAM and `MapSet.to_list` returns its
elements in term order, not in insertion order; here `toList` is the
identity on the insertion-ordered list. So a property may count a set's
elements, ask whether one is in it, and compare two sets built the same
way, but must not depend on the order `to_list` produces. That is the one
place this model is coarser than `MapSet`.

Like `AssocList`, nothing here assumes its argument is duplicate-free: the
lemmas hold for any list, and `insert` is what keeps a set built from `[]`
duplicate-free. No Mathlib.
-/

namespace Leanactors.SetList

variable {α : Type} [DecidableEq α]

/-- `MapSet.member?/2`. -/
def contains (s : List α) (x : α) : Bool := s.contains x

/-- `MapSet.put/2`: append unless the element is already there. -/
def insert (s : List α) (x : α) : List α := if s.contains x then s else s ++ [x]

/-- `MapSet.delete/2`: drop every copy of the element. -/
def erase (s : List α) (x : α) : List α := s.filter (fun y => !(y == x))

/-- `MapSet.size/1`. -/
def size (s : List α) : Nat := s.length

/-- `MapSet.to_list/1` (insertion order, not the BEAM's term order). -/
def toList (s : List α) : List α := s

/-- `MapSet.new/1`: the list, duplicates removed, first occurrence kept. -/
def ofList (l : List α) : List α := l.foldl insert []

/-- `MapSet.union/2`: `a`, then the elements of `b` it does not have. -/
def union (a b : List α) : List α := b.foldl insert a

/-- `MapSet.difference/2`. -/
def difference (a b : List α) : List α := a.filter (fun x => !b.contains x)

/-- `MapSet.intersection/2`. -/
def intersection (a b : List α) : List α := a.filter (fun x => b.contains x)

/-! ## Lemmas -/

@[simp] theorem contains_eq_mem (s : List α) (x : α) : contains s x = true ↔ x ∈ s := by
  simp [contains]

@[simp] theorem contains_nil (x : α) : contains ([] : List α) x = false := rfl

theorem mem_insert (s : List α) (x y : α) : y ∈ insert s x ↔ y ∈ s ∨ y = x := by
  by_cases h : x ∈ s
  · have e : insert s x = s := by simp [insert, h]
    rw [e]
    exact ⟨Or.inl, fun hy => hy.elim id (fun q => q ▸ h)⟩
  · have e : insert s x = s ++ [x] := by simp [insert, h]
    rw [e]
    simp

@[simp] theorem mem_insert_self (s : List α) (x : α) : x ∈ insert s x :=
  (mem_insert s x x).2 (Or.inr rfl)

/-- `insert` keeps every element that was there. -/
theorem mem_of_mem_insert {s : List α} {x y : α} (h : y ∈ s) : y ∈ insert s x :=
  (mem_insert s x y).2 (Or.inl h)

@[simp] theorem not_mem_erase (s : List α) (x : α) : x ∉ erase s x := by
  simp [erase]

theorem mem_erase {s : List α} {x y : α} (h : y ∈ erase s x) : y ∈ s := by
  simp only [erase, List.mem_filter] at h
  exact h.1

/-- Inserting an element that is already there changes nothing. -/
theorem insert_of_mem {s : List α} {x : α} (h : x ∈ s) : insert s x = s := by
  simp [insert, h]

omit [DecidableEq α] in
@[simp] theorem size_nil : size ([] : List α) = 0 := rfl

theorem size_insert_of_mem {s : List α} {x : α} (h : x ∈ s) : size (insert s x) = size s := by
  rw [insert_of_mem h]

theorem size_insert_of_not_mem {s : List α} {x : α} (h : x ∉ s) :
    size (insert s x) = size s + 1 := by
  simp [size, insert, h]

omit [DecidableEq α] in
@[simp] theorem toList_eq (s : List α) : toList s = s := rfl

@[simp] theorem mem_difference (a b : List α) (x : α) : x ∈ difference a b ↔ x ∈ a ∧ x ∉ b := by
  simp [difference]

@[simp] theorem mem_intersection (a b : List α) (x : α) :
    x ∈ intersection a b ↔ x ∈ a ∧ x ∈ b := by
  simp [intersection]

end Leanactors.SetList
