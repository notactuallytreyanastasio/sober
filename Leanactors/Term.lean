/-!
# Leanactors.Term

An opaque term. The translator gives this type to every field whose Elixir
type it does not know: a message argument or state field of a module with
no `@type` declarations (untyped mode), a `term()`, `any()` or
`reference()` in a declaration, and the reference an external resource
call such as `:ets.new/2` returns.

A `Term` carries nothing but a number, so the model can compare terms
(`DecidableEq`, which every map key and every property needs) and create
fresh ones: a module that calls `:ets.new` gets a hidden counter field
`ets : Nat` in its state, the `n`-th table created is `Term.mk n`, and the
counter is bumped. That is all the model knows about an ETS table. The
effects of `:ets.new`, `:ets.delete` and their `try ... rescue ... end`
wrappers on the real table storage are abstracted away, so what is proved
about a registry is a property of its map of references, not of ETS.
-/

namespace Leanactors

/-- An opaque term, distinguished only by its number. -/
structure Term where
  id : Nat
  deriving DecidableEq, Repr

namespace Term

/-- The `n`-th fresh term (what the `n`-th `:ets.new` returns). -/
def fresh (n : Nat) : Term := ⟨n⟩

@[simp] theorem id_mk (n : Nat) : (Term.mk n).id = n := rfl

@[simp] theorem fresh_eq_mk (n : Nat) : fresh n = Term.mk n := rfl

theorem mk_inj {a b : Nat} (h : Term.mk a = Term.mk b) : a = b := by
  cases h; rfl

theorem mk_injective {a b : Nat} : Term.mk a = Term.mk b ↔ a = b :=
  ⟨mk_inj, fun h => h ▸ rfl⟩

/-- A term below the counter is never the one the counter creates next. -/
theorem mk_ne_of_lt {a b : Nat} (h : a < b) : Term.mk a ≠ Term.mk b := by
  intro e
  exact Nat.lt_irrefl _ (mk_inj e ▸ h)

theorem ne_of_id_ne {t u : Term} (h : t.id ≠ u.id) : t ≠ u := by
  intro e
  exact h (e ▸ rfl)

end Term

end Leanactors
