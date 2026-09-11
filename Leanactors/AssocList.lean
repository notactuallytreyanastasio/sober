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

/-- Every pair of `m` at a key other than `k` survives `erase`. -/
theorem mem_erase_of_ne {m : List (κ × ν)} {k : κ} {kv : κ × ν}
    (h : kv ∈ m) (hk : kv.1 ≠ k) : kv ∈ erase m k := by
  induction m with
  | nil => cases h
  | cons x rest ih =>
    obtain ⟨k'', v''⟩ := x
    rcases List.mem_cons.mp h with rfl | h
    · simp only [erase, if_neg hk]
      exact List.mem_cons_self
    · by_cases hx : k'' = k
      · simp only [erase, if_pos hx]
        exact ih h
      · simp only [erase, if_neg hx]
        exact List.mem_cons_of_mem _ (ih h)

/-! ## Uniqueness

A map built from `[]` by `insert` and `erase` has unique keys; when every
value inserted is fresh it has unique values too. `Uniq` says both at
once, `key_inj` and `val_inj` are what a property about such a map usually
needs, and `insert_fresh` and `Uniq.erase` are the two steps that keep it.
Nothing else in this file assumes uniqueness. -/

/-- No two entries share a key, and no two entries share a value. -/
def Uniq : List (κ × ν) → Prop
  | [] => True
  | kv :: rest => (∀ x ∈ rest, x.1 ≠ kv.1 ∧ x.2 ≠ kv.2) ∧ Uniq rest

omit [DecidableEq κ] in
@[simp] theorem uniq_nil : Uniq ([] : List (κ × ν)) := trivial

omit [DecidableEq κ] in
theorem uniq_cons {kv : κ × ν} {rest : List (κ × ν)} :
    Uniq (kv :: rest) ↔ (∀ x ∈ rest, x.1 ≠ kv.1 ∧ x.2 ≠ kv.2) ∧ Uniq rest := Iff.rfl

omit [DecidableEq κ] in
/-- One key, one value. -/
theorem Uniq.key_inj {m : List (κ × ν)} (h : Uniq m) {k : κ} {v v' : ν}
    (h1 : (k, v) ∈ m) (h2 : (k, v') ∈ m) : v = v' := by
  induction m with
  | nil => cases h1
  | cons x rest ih =>
    obtain ⟨kx, vx⟩ := x
    obtain ⟨hhead, htail⟩ := h
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨hk2, hv2⟩ | h2
    · exact hv2.symm
    · exact absurd rfl (hhead _ h2).1
    · exact absurd hk2 (hhead _ h1).1
    · exact ih htail h1 h2

omit [DecidableEq κ] in
/-- One value, one key. -/
theorem Uniq.val_inj {m : List (κ × ν)} (h : Uniq m) {k k' : κ} {v : ν}
    (h1 : (k, v) ∈ m) (h2 : (k', v) ∈ m) : k = k' := by
  induction m with
  | nil => cases h1
  | cons x rest ih =>
    obtain ⟨kx, vx⟩ := x
    obtain ⟨hhead, htail⟩ := h
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨hk2, hv2⟩ | h2
    · exact hk2.symm
    · exact absurd rfl (hhead _ h2).2
    · exact absurd hv2 (hhead _ h1).2
    · exact ih htail h1 h2

/-- Inserting a value no entry already carries keeps `Uniq`. -/
theorem Uniq.insert_fresh {m : List (κ × ν)} (h : Uniq m) {k : κ} {v : ν}
    (hf : ∀ x ∈ m, x.2 ≠ v) : Uniq (insert m k v) := by
  induction m with
  | nil =>
    refine (uniq_cons (kv := (k, v)) (rest := [])).mpr ⟨?_, uniq_nil⟩
    intro x hx
    cases hx
  | cons x rest ih =>
    obtain ⟨k', v'⟩ := x
    obtain ⟨hhead, htail⟩ := h
    by_cases hk : k = k'
    · rw [insert, if_pos hk]
      refine uniq_cons.mpr ⟨fun y hy => ⟨hk ▸ (hhead y hy).1, hf y (List.mem_cons_of_mem _ hy)⟩, htail⟩
    · rw [insert, if_neg hk]
      refine uniq_cons.mpr ⟨fun y hy => ?_, ih htail fun y hy => hf y (List.mem_cons_of_mem _ hy)⟩
      obtain ⟨ky, vy⟩ := y
      rcases mem_insert hy with ⟨rfl, rfl⟩ | hy
      · exact ⟨hk, fun e => hf (k', v') List.mem_cons_self (e ▸ rfl)⟩
      · exact hhead _ hy

/-- Erasing a key keeps `Uniq`. -/
theorem Uniq.erase {m : List (κ × ν)} (h : Uniq m) (k : κ) : Uniq (AssocList.erase m k) := by
  induction m with
  | nil => exact uniq_nil
  | cons x rest ih =>
    obtain ⟨k', v'⟩ := x
    obtain ⟨hhead, htail⟩ := h
    by_cases hk : k' = k
    · rw [AssocList.erase, if_pos hk]
      exact ih htail
    · rw [AssocList.erase, if_neg hk]
      refine uniq_cons.mpr ⟨fun y hy => ?_, ih htail⟩
      obtain ⟨ky, vy⟩ := y
      exact hhead _ (mem_erase hy).1

end Leanactors.AssocList
