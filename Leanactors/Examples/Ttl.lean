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
model-only message `after_run g` carrying a generation. The cache's state
has a hidden trailing field `gen`, the generation of the timer armed by
the current receive: the spawn starts at generation 0 and arms
`after_run 0`, every re-entry of the receive moves to `gen + 1` and arms
`after_run (gen + 1)`, and the after body runs only for a message of the
current generation. A timer armed before a later message was handled is
therefore stale, and the cache consumes and ignores it when it fires.
That is the BEAM's rule (each receive starts a fresh timeout, a processed
message cancels it) written with untimed timers: any pending timer may
still fire at any step, but only the live one does anything.
`Process.register(pid, __MODULE__)` in `Cache.start` makes `cache` the
constant pid 0 without a `--pid` flag. The `raise` is an `.exit .error`
with the state unchanged.

**Property.** The cache never holds the value 0, and no `value (some 0)`
reply is ever in flight to the reader: a `put 0` kills the cache instead.
`TtlProof.lean` proves it for every reachable configuration; the checker
below validates it first.
-/

namespace Leanactors.Examples.Ttl

open Leanactors Config Sys

export Leanactors.Gen.Ttl (Msg St cache sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, _, .cache v gen, .put 0 => (.cache v gen, [.exit .error])
  | me, _, .cache _ gen, .put x => (.cache (some x) (gen + 1), [.sendAfter me (.after_run (gen + 1))])
  | me, _, .cache v gen, .get r =>
      (.cache v (gen + 1), [.send r (.value v), .sendAfter me (.after_run (gen + 1))])
  | me, _, .cache v gen, .after_run g =>
      if g = gen then (.cache none (gen + 1), [.sendAfter me (.after_run (gen + 1))])
      else (.cache v gen, [])
  | me, _, .cache v gen, m => (.cache v (gen + 1), [.send me m, .sendAfter me (.after_run (gen + 1))])
  | me, _, .reader n, .ask => (.reader n, [.send cache (.get me)])
  | _, _, .reader n, .value _ => (.reader (n + 1), [])
  | me, _, .reader n, m => (.reader n, [.send me m])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Ttl.beh = beh := by
  funext me fresh s m
  cases s with
  | cache v gen =>
    cases m with
    | put x => cases x <;> rfl
    | get _ => rfl
    | after_run _ => rfl
    | ask => rfl
    | value _ => rfl
  | reader n => cases m <;> rfl

/-- The cache at pid 0 (empty, at generation 0, its first receive has armed
the generation-0 timer) and a reader at pid 1. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.cache none 0, []⟩
                     else if p = 1 then some ⟨.reader 0, []⟩ else none⟩
    next := 2, links := [], signals := [], timers := [(0, .after_run 0)] }

/-! ## Bounded model check -/

def livePids (s : Sys St Msg) : List Pid :=
  (List.range s.next).filter fun p => (s.cfg.get p).isSome

/-- The cache never holds 0 and never has a `value (some 0)` in flight. -/
def checkInv (s : Sys St Msg) : Bool :=
  (match s.cfg.stateOf 0 with
   | some (.cache (some 0) _) => false
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
environment stimulus): the live timer expires the cache twice (each
firing is of the current generation, so each runs the after body and
arms the next), then `env put 0 -> 0`, `run 0`. -/
def behNoRaise : EBehavior St Msg
  | me, _, .cache _ gen, .put x => (.cache (some x) (gen + 1), [.sendAfter me (.after_run (gen + 1))])
  | me, fresh, s, m => beh me fresh s m

#eval explore behNoRaise sig init 7 3

/-- put 5 (generation 1), the reader asks and is answered (generation 2),
the reader counts. Three timers are pending: generations 0, 1 and 2. -/
def served : Sys St Msg :=
  let s1 := { init with cfg := (init.cfg.deliver 0 (.put 5)).deliver 1 .ask }
  runSys beh sig s1 [.run 0, .run 1, .run 0, .run 1]

/-- The stale generation-0 timer fires: the cache ignores it and keeps 5. -/
def afterStale : Sys St Msg := runSys beh sig served [.timer 0, .run 0]

#eval (afterStale.cfg.stateOf 0, afterStale.timers)

/-- Then the live generation-2 timer (now at index 1) fires and expires the
value; the reader asks again and gets `none`. -/
def trace : Sys St Msg :=
  let s2 := runSys beh sig afterStale [.timer 1, .run 0]
  let s3 := { s2 with cfg := s2.cfg.deliver 1 .ask }
  runSys beh sig s3 [.run 1, .run 0, .run 1]

#eval (trace.cfg.stateOf 0, trace.cfg.stateOf 1, trace.timers)

end Leanactors.Examples.Ttl
