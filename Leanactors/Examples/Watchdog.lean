import Leanactors.Sys
import Leanactors.Gen.Watchdog
/-!
# Leanactors.Examples.Watchdog

A watchdog, translated from `elixir/src/watchdog.ex`: it pings a linked
worker, arms a GenServer timeout, and on `:timeout` kills the worker with
`Process.exit/2` and restarts it on the resulting `EXIT`.

Timers are untimed in the model, so a `:timeout` may fire even though a
`:pong` arrived first: the watchdog may kill a healthy worker. That is a
sound over-approximation for the property below, which does not care why
a worker died.

**Property.** The watchdog never dies, and whenever its worker is gone a
restart is already in flight.
-/

namespace Leanactors.Examples.Watchdog

open Leanactors Config Sys

export Leanactors.Gen.Watchdog (Msg St watchdog sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | me, fresh, .watchdog none _, .start =>
      (.watchdog (some fresh) true, [.spawnLink (.worker false 0), .send fresh .ping, .sendAfter me .timeout])
  | me, _, .watchdog (some w) true, .pong => (.watchdog (some w) true, [.send w .ping, .sendAfter me .timeout])
  | _, _, .watchdog (some w) true, .timeout => (.watchdog (some w) false, [.signal w .error])
  | me, fresh, .watchdog (some w) b, .EXIT who _ =>
      if who = w then
        (.watchdog (some fresh) true, [.spawnLink (.worker false 0), .send fresh .ping, .sendAfter me .timeout])
      else (.watchdog (some w) b, [])
  | _, _, .worker false n, .ping => (.worker false (n + 1), [.send watchdog .pong])
  | _, _, .worker _ n, .hang => (.worker true n, [])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Watchdog.beh = beh := by
  funext me fresh s m
  cases s with
  | watchdog w b => cases w <;> cases b <;> cases m <;> first | rfl | simp [Gen.Watchdog.beh, beh]
  | worker h n => cases h <;> cases m <;> rfl

def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.watchdog none false, [.start]⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## Invariant (same shape as the supervisor's) -/

structure Inv (s : Sys St Msg) : Prop where
  next_pos : 0 < s.next
  dog_alive : ∃ w b, s.cfg.stateOf 0 = some (.watchdog w b)
  child_ok : ∀ w b, s.cfg.stateOf 0 = some (.watchdog (some w) b) →
    ((s.cfg.get w).isSome ∧ (0, w) ∈ s.links) ∨
    (∃ r, (0, w, r) ∈ s.signals) ∨
    (∃ r, 0 < s.cfg.mcount 0 (.EXIT w r))

/-! ## Bounded model check -/

def livePids (s : Sys St Msg) : List Pid :=
  (List.range s.next).filter fun p => (s.cfg.get p).isSome

def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.watchdog none _) => true
  | some (.watchdog (some w) _) =>
    ((s.cfg.get w).isSome && s.links.contains (0, w)) ||
    [Reason.normal, .error].any (fun r => s.signals.contains (0, w, r)) ||
    [Reason.normal, .error].any (fun r => 0 < s.cfg.mcount 0 (.EXIT w r))
  | _ => false

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
      (livePids s).map fun p => ({ s with cfg := s.cfg.deliver p .hang }, env - 1, s!"env hang -> {p}")
    (runs ++ sigs ++ timers ++ envs).foldl (fun (n, bad) (s', e, lbl) =>
      match bad with
      | some _ => (n, bad)
      | none =>
        let (n', bad') := explore b sg s' (depth - 1) e (lbl :: path)
        (n + n', bad')) (1, none)

#eval explore beh sig init 8 2

/-- **Mutant**: the watchdog uses `send(w, :stop)`-style politeness instead
of `Process.exit`, i.e. it forgets to kill. A hung worker is never
replaced, though the invariant does not see that (the worker is alive and
linked). What *does* break the invariant: forgetting `trap_exit`. -/
def sigNoTrap : Signals St Msg := { sig with traps := fun _ => false }

#eval explore beh sigNoTrap init 8 2

/-- A concrete trace: start, ping/pong, the worker hangs, the timeout
fires, the kill signal lands, the EXIT arrives, the watchdog restarts. -/
def trace : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0, .run 1, .run 0]         -- start; worker pongs; dog re-pings + re-arms
  let s2 := { s1 with cfg := s1.cfg.deliver 1 .hang }
  -- ping answered, hang, timeout fires, pong then timeout handled (kill sent),
  -- kill delivered (worker dies, EXIT queued), EXIT delivered, restart
  runSys beh sig s2 [.run 1, .run 1, .timer 0, .run 0, .run 0, .signal, .signal, .run 0]

#eval (trace.cfg.stateOf 0, trace.cfg.stateOf 1, trace.cfg.stateOf 2, trace.links, trace.signals, trace.timers.length)

end Leanactors.Examples.Watchdog
