/-!
# Leanactors.AssocList

Association lists, the model of an Elixir map `%{K => V}`. The translator
renders the type as `List (K × V)` and the `Map` calls as the functions
below: `Map.get(m, k)` is `get?`, `Map.get(m, k, d)` is `(get? m k).getD
d`, `Map.fetch` is `get?` as well (`{:ok, v}` is `some v`, `:error` is
`none`), `Map.put` is `insert` (replace in place, or append), `Map.delete`
is `erase`, `Map.has_key?` and `is_map_key` are `hasKey`, `map_size` is
`size`, `Map.keys`/`Map.values` are `keys`/`values`, and `Map.filter` /
`Map.reject` with a `fn {k, v} -> e end` are `filter` / `reject`.

Nothing here assumes the keys are unique: `get?` finds the first pair,
`insert` replaces the first pair (so the order of the other keys is kept)
and `erase` and `reject` drop every matching pair. A map built from `[]`
by `insert` and `erase` only has unique keys, but the lemmas hold for any
list, which is what the proofs see. No Mathlib.
-/

namespace Leanactors.AssocList

variable {κ ν : Type} [DecidableEq κ]

/-- The value at `k`, if any (`Map.get/2`, `Map.fetch/2`). -/
def get? : List (κ × ν) → κ → Option ν
  | [], _ => none
  | (k', v) :: rest, k => if k = k' then some v else get? rest k

/-- Replace the value at `k`, or append the pair (`Map.put/3`). -/
def insert : List (κ × ν) → κ → ν → List (κ × ν)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k = k' then (k, v) :: rest else (k', v') :: insert rest k v

/-- Drop every pair at `k` (`Map.delete/2`). -/
def erase : List (κ × ν) → κ → List (κ × ν)
  | [], _ => []
  | (k', v) :: rest, k => if k' = k then erase rest k else (k', v) :: erase rest k

/-- `Map.has_key?/2`, `is_map_key/2`. -/
def hasKey (m : List (κ × ν)) (k : κ) : Bool :=
  (get? m k).isSome

/-- `Map.keys/1`. -/
def keys (m : List (κ × ν)) : List κ := m.map (·.1)

/-- `Map.values/1`. -/
def values (m : List (κ × ν)) : List ν := m.map (·.2)

/-- `map_size/1`. -/
def size (m : List (κ × ν)) : Nat := m.length

/-- `Map.filter(m, fn {k, v} -> f end)`: keep the pairs `f` accepts. -/
def filter (m : List (κ × ν)) (f : κ × ν → Bool) : List (κ × ν) :=
  m.filter f

/-- `Map.reject(m, fn {k, v} -> f end)`: drop the pairs `f` accepts. -/
def reject (m : List (κ × ν)) (f : κ × ν → Bool) : List (κ × ν) :=
  m.filter fun kv => !f kv

/-! ## Lemmas -/

@[simp] theorem get?_nil (k : κ) : get? ([] : List (κ × ν)) k = none := rfl

@[simp] theorem get?_cons (k k' : κ) (v : ν) (rest : List (κ × ν)) :
    get? ((k', v) :: rest) k = if k = k' then some v else get? rest k := rfl

@[simp] theorem get?_insert_self (m : List (κ × ν)) (k : κ) (v : ν) :
    get? (insert m k v) k = some v := by
  induction m with
  | nil => simp [insert]
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases h : k = k'
    · subst h; simp [insert]
    · simp [insert, h, ih]

theorem get?_insert_ne (m : List (κ × ν)) {k k' : κ} (v : ν) (h : k' ≠ k) :
    get? (insert m k v) k' = get? m k' := by
  induction m with
  | nil => simp [insert, h]
  | cons kv rest ih =>
    obtain ⟨k'', v''⟩ := kv
    by_cases hk : k = k''
    · subst hk; simp [insert, h]
    · simp only [insert, hk, if_false, get?_cons]
      by_cases h' : k' = k''
      · simp [h']
      · simp [h', ih]

theorem get?_insert (m : List (κ × ν)) (k k' : κ) (v : ν) :
    get? (insert m k v) k' = if k' = k then some v else get? m k' := by
  by_cases h : k' = k
  · subst h; simp
  · simp [h, get?_insert_ne m v h]

@[simp] theorem get?_erase_self (m : List (κ × ν)) (k : κ) :
    get? (erase m k) k = none := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases h : k' = k
    · subst h; simpa [erase] using ih
    · have h' : k ≠ k' := fun e => h e.symm
      simp [erase, h, h', ih]

theorem get?_erase_ne (m : List (κ × ν)) {k k' : κ} (h : k' ≠ k) :
    get? (erase m k) k' = get? m k' := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k'', v''⟩ := kv
    by_cases hk : k'' = k
    · subst hk
      simp [erase, h, ih]
    · simp only [erase, hk, if_false, get?_cons]
      by_cases h' : k' = k''
      · simp [h']
      · simp [h', ih]

theorem get?_erase (m : List (κ × ν)) (k k' : κ) :
    get? (erase m k) k' = if k' = k then none else get? m k' := by
  by_cases h : k' = k
  · subst h; simp
  · simp [h, get?_erase_ne m h]

theorem hasKey_iff (m : List (κ × ν)) (k : κ) :
    hasKey m k = true ↔ ∃ v, get? m k = some v := by
  unfold hasKey
  cases get? m k <;> simp

/-- A found value is a pair of the list. -/
theorem mem_of_get? {m : List (κ × ν)} {k : κ} {v : ν} (h : get? m k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [get?] at h
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases hk : k = k'
    · subst hk
      simp [get?] at h
      subst h
      exact List.mem_cons_self
    · simp [get?, hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Every pair of `insert m k v` is `(k, v)` or a pair of `m`. -/
theorem mem_insert {m : List (κ × ν)} {k k' : κ} {v v' : ν}
    (h : (k', v') ∈ insert m k v) : (k' = k ∧ v' = v) ∨ (k', v') ∈ m := by
  induction m with
  | nil =>
    simp [insert] at h
    exact Or.inl h
  | cons kv rest ih =>
    obtain ⟨k'', v''⟩ := kv
    by_cases hk : k = k''
    · subst hk
      simp [insert] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp [insert, hk] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Every pair of `erase m k` is a pair of `m` at another key. -/
theorem mem_erase {m : List (κ × ν)} {k k' : κ} {v' : ν}
    (h : (k', v') ∈ erase m k) : (k', v') ∈ m ∧ k' ≠ k := by
  induction m with
  | nil => simp [erase] at h
  | cons kv rest ih =>
    obtain ⟨k'', v''⟩ := kv
    by_cases hk : k'' = k
    · subst hk
      simp only [erase, if_true] at h
      exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    · simp only [erase, hk, if_false, List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hk⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

omit [DecidableEq κ] in
/-- Every pair of `reject m f` is a pair of `m` that `f` rejects. -/
theorem mem_reject {m : List (κ × ν)} {f : κ × ν → Bool} {kv : κ × ν}
    (h : kv ∈ reject m f) : kv ∈ m ∧ f kv = false := by
  unfold reject at h
  rw [List.mem_filter] at h
  simpa using h

omit [DecidableEq κ] in
/-- Every pair of `filter m f` is a pair of `m` that `f` accepts. -/
theorem mem_filter {m : List (κ × ν)} {f : κ × ν → Bool} {kv : κ × ν}
    (h : kv ∈ filter m f) : kv ∈ m ∧ f kv = true := by
  unfold filter at h
  exact List.mem_filter.mp h

end Leanactors.AssocList
