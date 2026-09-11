/-!
# Leanactors.Str

Elixir binaries are Lean `String`s. A `String.t()`, a `binary()` and every
string literal in a translated module render at this type, which is what the
model needs of them: `DecidableEq` (so a state that stores one still derives
`DecidableEq`, and a property may compare two) and `Repr` (so the checkers
and the trace printers can show one).

String *interpolation* is the reason this file exists. The translator turns
`"a#{e}b"` into `"a" ++ Str.toStr e ++ "b"`, so it needs one function that
renders a value of any modelled type as a `String`. `ToStr` is that
function. The instances below fix the rendering for the types whose Elixir
rendering is known -- a binary is itself, an integer is its decimal digits,
a boolean is `true`/`false` -- and the low-priority instance renders
everything else through its derived `Repr`.

That last instance is the honest part of the model: an Elixir value with no
printable model (an inductive standing for a tagged union, an opaque `Term`,
an `Instant`) still has to become *some* string, and the string it becomes
is Lean's `repr`, not Elixir's `to_string`. So a property may compare two
interpolated strings for equality, and may see that they differ when their
inputs differ, but the exact bytes of an interpolated string are a Lean
artefact and no property should depend on them. `toStr_string`,
`toStr_nat` and `toStr_bool` below are the three renderings that are
faithful.
-/

namespace Leanactors

/-- How a value is rendered inside an Elixir string interpolation. -/
class ToStr (α : Type) where
  toStr : α → String

/-- A binary interpolated into a binary is itself. -/
instance : ToStr String := ⟨id⟩
instance : ToStr Nat := ⟨fun n => toString n⟩
instance : ToStr Int := ⟨fun i => toString i⟩
instance : ToStr Bool := ⟨fun b => toString b⟩

/-- Anything else is rendered through its derived `Repr`: an opaque
rendering, distinct for distinct values of a type whose `Repr` is injective,
but not the bytes the BEAM would produce. -/
instance (priority := low) {α : Type} [Repr α] : ToStr α := ⟨fun a => (repr a).pretty⟩

namespace Str

/-- The rendering the translator emits for `#{e}` in a binary. -/
def toStr {α : Type} [ToStr α] (a : α) : String := ToStr.toStr a

@[simp] theorem toStr_string (s : String) : toStr s = s := rfl
@[simp] theorem toStr_nat (n : Nat) : toStr n = toString n := rfl
@[simp] theorem toStr_bool (b : Bool) : toStr b = toString b := rfl

/-- `<>` and interpolation build strings with `++`, which is associative. -/
theorem append_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) :=
  String.append_assoc

@[simp] theorem append_empty (a : String) : a ++ "" = a := String.append_empty

@[simp] theorem empty_append (a : String) : "" ++ a = a := String.empty_append

end Str

end Leanactors
