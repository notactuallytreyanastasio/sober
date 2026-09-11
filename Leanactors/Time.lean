/-!
# Leanactors.Time

Time, as much of it as the model has: none.

`DateTime.utc_now()`, `System.monotonic_time(_)` and their neighbours are
reads of a clock the model does not have, so the translator renders every
one of them as the single opaque value `Instant.now`. An `Instant` has
`DecidableEq` (a state may store one, a clause may compare two) and `Repr`
(a trace may print one) and nothing else: no order, no arithmetic, no
`toString` of its own. Two consequences, both deliberate:

* Lean will not elaborate `t < u`, `t - u` or `t + n` on an `Instant`; and
  the translator refuses such an expression before Lean sees it, with a
  message saying the model has no clock. A module whose behaviour depends
  on elapsed time is therefore *not* translated with its timing quietly
  wrong -- it is rejected.
* Two reads of the clock are equal, because there is only one `Instant`.
  A property may not conclude anything from that: `t = u` holds in the
  model for reasons that have nothing to do with the BEAM. What a
  translated module may do with an instant is store it, pass it on, and
  put it in a message -- which is what the modules that read a clock
  mostly do with the result.

Timeouts are a different thing and are modelled: see `Sys.sendAfter` and
the `after` generation counter in the translator header.
-/

namespace Leanactors

/-- An opaque instant: the one value a clock read produces. -/
inductive Instant where
  /-- The result of `DateTime.utc_now()`, `System.monotonic_time(_)`, ... -/
  | now
  deriving Repr, DecidableEq

namespace Instant

/-- There is only one instant, so any two clock reads are equal. This is a
fact about the model, not about time: no property should rest on it. -/
theorem eq_now (t : Instant) : t = now := by cases t; rfl

theorem all_eq (t u : Instant) : t = u := by cases t; cases u; rfl

end Instant

end Leanactors
