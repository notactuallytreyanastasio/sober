import Leanactors.Sys
/-!
# Leanactors.Explore

A bounded explorer for `Sys`, shared by the example files. From a start
configuration it enumerates, depth-first, every interleaving of

* `run p` for every live pid `p` (`runE`),
* `signal` (`signalE`, deliver the oldest pending exit signal),
* `down` (`downE`, deliver the oldest pending DOWN notification),
* `timer i` for every pending timer index (`timerE`),
* `env m -> p`: the environment sends `m` to the live pid `p`, for every
  `m` the caller allows at `p`; each such step spends one unit of the
  environment budget,

to a depth bound, checking a `Bool` invariant at every configuration. The
result is the number of configurations visited and, if the invariant ever
failed, the first violating path as readable labels. Steps that are not
enabled (`none`) are skipped, so a model without monitors or timers pays
nothing for the `down` and `timer` cases.

The order above is also the search order, so a witness is the
lexicographically first violation in it.
-/

namespace Leanactors.Sys

/-- The pids below the fresh counter that have a live actor. -/
def livePids (s : Sys σ μ) : List Pid :=
  (List.range s.next).filter fun p => (s.cfg.get p).isSome

/-- Every interleaving of actor runs, exit-signal and DOWN deliveries,
timer firings and environment messages (`envMsgs p` may be sent to the
live pid `p`), to depth `depth` with at most `env` environment messages.
Returns the number of configurations visited and the first path on which
`check` fails, if any. -/
partial def exploreWith [Repr μ] (beh : EBehavior σ μ) (sig : Signals σ μ)
    (check : Sys σ μ → Bool) (envMsgs : Pid → List μ) (s : Sys σ μ)
    (depth env : Nat) (path : List String := []) : Nat × Option (List String) :=
  if !check s then (1, some path.reverse)
  else if depth = 0 then (1, none)
  else
    let runs := s.livePids.filterMap fun p => (runE beh s p).map fun s' => (s', env, s!"run {p}")
    let sigs := (signalE sig s).map (fun s' => [(s', env, "signal")]) |>.getD []
    let downs := (downE sig s).map (fun s' => [(s', env, "down")]) |>.getD []
    let timers := (List.range s.timers.length).filterMap fun i =>
      (timerE s i).map fun s' => (s', env, s!"timer {i}")
    let envs := if env = 0 then [] else
      s.livePids.flatMap fun p =>
        (envMsgs p).map fun m =>
          ({ s with cfg := s.cfg.deliver p m }, env - 1, s!"env {repr m} -> {p}")
    (runs ++ sigs ++ downs ++ timers ++ envs).foldl (fun (n, bad) (s', e, lbl) =>
      match bad with
      | some _ => (n, bad)
      | none =>
        let (n', bad') := exploreWith beh sig check envMsgs s' (depth - 1) e (lbl :: path)
        (n + n', bad')) (1, none)

/-- `exploreWith` where the environment may send any of `envMsgs` to any
live pid. -/
def explore [Repr μ] (beh : EBehavior σ μ) (sig : Signals σ μ)
    (check : Sys σ μ → Bool) (envMsgs : List μ) (s : Sys σ μ)
    (depth env : Nat) : Nat × Option (List String) :=
  exploreWith beh sig check (fun _ => envMsgs) s depth env

end Leanactors.Sys
