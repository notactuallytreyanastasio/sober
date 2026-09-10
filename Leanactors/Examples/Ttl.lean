import Leanactors.Sys
import Leanactors.Gen.Ttl
/-!
# Leanactors.Examples.Ttl

A cache with a time-to-live, translated from `elixir/src/ttl.ex`. The
cache is a raw process whose `receive` has an `after` clause:

```elixir
def run(v) do
  receive do
    {:put, 0} -> raise ArgumentError, "0 is not a cacheable value"
    {:put, x} -> run(x)
    {:get, from} -> send(from, {:value, v}); run(v)
  after
    200 -> run(nil)
  end
end
```

Three translator features meet here. The `after` clause becomes a
model-only message `after_run` that the cache sends itself as an untimed
timer every time it re-enters the receive; the after body is the clause
for that message. `Process.register(pid, __MODULE__)` in `Cache.start`
makes `cache` the constant pid 0 without a `--pid` flag. The `raise` is
an `.exit .error` with the state unchanged.

Timers are untimed, so a stale `after_run` may fire right after a `put`
and expire the value early. That over-approximates the BEAM (where any
message resets the TTL) and is sound for the safety property below.

**Property.** The cache never holds the value 0, and no `value (some 0)`
reply is ever in flight to the reader: a `put 0` kills the cache instead.
-/

namespace Leanactors.Examples.Ttl

open Leanactors Config Sys

export Leanactors.Gen.Ttl (Msg St cache sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, _, .cache v, .put 0 => (.cache v, [.exit .error])
  | me, _, .cache _, .put x => (.cache (some x), [.sendAfter me .after_run])
  | me, _, .cache v, .get r => (.cache v, [.send r (.value v), .sendAfter me .after_run])
  | me, _, .cache _, .after_run => (.cache none, [.sendAfter me .after_run])
  | me, _, .cache v, m => (.cache v, [.send me m, .sendAfter me .after_run])
  | me, _, .reader n, .ask => (.reader n, [.send cache (.get me)])
  | _, _, .reader n, .value _ => (.reader (n + 1), [])
  | me, _, .reader n, m => (.reader n, [.send me m])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Ttl.beh = beh := by
  funext me fresh s m
  cases s with
  | cache v =>
    cases m with
    | put x => cases x <;> rfl
    | get _ => rfl
    | after_run => rfl
    | ask => rfl
    | value _ => rfl
  | reader n => cases m <;> rfl

/-- The cache at pid 0 (empty, its first receive has armed the timer) and
a reader at pid 1. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.cache none, []⟩
                     else if p = 1 then some ⟨.reader 0, []⟩ else none⟩
    next := 2, links := [], signals := [], timers := [(0, .after_run)] }

/-! ## Bounded model check -/

def livePids (s : Sys St Msg) : List Pid :=
  (List.range s.next).filter fun p => (s.cfg.get p).isSome

/-- The cache never holds 0 and never has a `value (some 0)` in flight. -/
def checkInv (s : Sys St Msg) : Bool :=
  (match s.cfg.stateOf 0 with
   | some (.cache (some 0)) => false
   | _ => true) &&
  s.cfg.mcount 1 (.value (some 0)) = 0

/-- Every interleaving of actor runs, timer firings and environment
stimulus (`put 0` and `put 1` to the cache, `ask` to the reader), to a
depth bound. -/
partial def explore (b : EBehavior St Msg) (sg : Signals St Msg) (s : Sys St Msg)
    (depth env : Nat) (path : List String := []) : Nat × Option (List String) :=
  if !checkInv s then (1, some path.reverse)
  else if depth = 0 then (1, none)
  else
    let runs := (livePids s).filterMap fun p => (runE b s p).map fun s' => (s', env, s!"run {p}")
    let sigs := (signalE sg s).map (fun s' => [(s', env, "signal")]) |>.getD []
    let timers := (List.range s.timers.length).filterMap fun i =>
      (timerE s i).map fun s' => (s', env, s!"timer {i}")
    let envs := if env = 0 then [] else
      [((.put 0 : Msg), 0), (.put 1, 0), (.ask, 1)].map fun (m, p) =>
        ({ s with cfg := s.cfg.deliver p m }, env - 1, s!"env {repr m} -> {p}")
    (runs ++ sigs ++ timers ++ envs).foldl (fun (n, bad) (s', e, lbl) =>
      match bad with
      | some _ => (n, bad)
      | none =>
        let (n', bad') := explore b sg s' (depth - 1) e (lbl :: path)
        (n + n', bad')) (1, none)

#eval explore beh sig init 7 3

/-- **Mutant**: the cache stores 0 instead of raising. The checker reports
the first violating path in its search order (runs and timers before
environment stimulus): two stale timer expiries, then `env put 0 -> 0`,
`run 0`. -/
def behNoRaise : EBehavior St Msg
  | me, _, .cache _, .put x => (.cache (some x), [.sendAfter me .after_run])
  | me, fresh, s, m => beh me fresh s m

#eval explore behNoRaise sig init 7 3

/-- A concrete trace: put 5, the reader asks and is answered, the timer
expires the value, the reader asks again and gets `none`. -/
def trace : Sys St Msg :=
  let s1 := { init with cfg := (init.cfg.deliver 0 (.put 5)).deliver 1 .ask }
  -- put; ask -> get; get -> value 5; reader counts; the (stale) initial timer expires
  let s2 := runSys beh sig s1 [.run 0, .run 1, .run 0, .run 1, .timer 0]
  let s3 := { s2 with cfg := s2.cfg.deliver 1 .ask }
  -- ask -> get; the cache handles the expiry, then the get (value none); reader counts
  runSys beh sig s3 [.run 1, .run 0, .run 0, .run 1]

#eval (trace.cfg.stateOf 0, trace.cfg.stateOf 1, trace.timers.length)

end Leanactors.Examples.Ttl
