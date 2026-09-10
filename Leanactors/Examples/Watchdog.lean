import Leanactors.Explore
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

def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.watchdog none _) => true
  | some (.watchdog (some w) _) =>
    ((s.cfg.get w).isSome && s.links.contains (0, w)) ||
    [Reason.normal, .error].any (fun r => s.signals.contains (0, w, r)) ||
    [Reason.normal, .error].any (fun r => 0 < s.cfg.mcount 0 (.EXIT w r))
  | _ => false

-- The environment may hang any live pid (the watchdog ignores `hang`).
#eval explore beh sig checkInv [.hang] init 8 2

/-! An unhandled cast crashes a GenServer, and the translator models that
as `.exit .error`. With `handle_cast(:pong, {w, true})` as the *only*
`:pong` clause the generated behaviour gained
`| _, _, .watchdog s_0 s_1, .pong => (.watchdog s_0 s_1, [.exit .error])`
and `explore Gen.Watchdog.beh sig checkInv [.hang] init 8 2` found the violation after 742
configurations:

  `["run 0", "run 1", "run 0", "timer 0", "run 0", "run 1", "run 0"]`

start; the worker pongs; the watchdog re-pings and re-arms; the timeout
fires; the watchdog sends the kill and clears the flag; the worker, whose
kill signal is still pending, answers the second ping; that late `:pong`
matches no clause and the watchdog exits. `handle_cast(:pong, s)` in
`watchdog.ex` is the fix; the crash clause is gone from the generated file. -/

/-- **Mutant**: the watchdog uses `send(w, :stop)`-style politeness instead
of `Process.exit`, i.e. it forgets to kill. A hung worker is never
replaced, though the invariant does not see that (the worker is alive and
linked). What *does* break the invariant: forgetting `trap_exit`. -/
def sigNoTrap : Signals St Msg := { sig with traps := fun _ => false }

#eval explore beh sigNoTrap checkInv [.hang] init 8 2

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
