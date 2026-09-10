import Leanactors.Sys
import Leanactors.Gen.Supervisor
/-!
# Leanactors.Examples.Supervisor

A one-for-one supervisor with a single permanent worker. The Elixir:

```elixir
defmodule Sup do
  use GenServer
  def init(_), do: Process.flag(:trap_exit, true); {:ok, {nil, 0}}
  def handle_info(:start, {nil, k}), do: {:noreply, {spawn_link(Worker, :run, [0]), k}}
  def handle_info({:EXIT, c, _}, {c, k}), do: {:noreply, {spawn_link(Worker, :run, [0]), k + 1}}
  def handle_info(_, s), do: {:noreply, s}
end

defmodule Worker do
  def run(n) do
    receive do
      :job -> run(n + 1)
      :crash -> exit(:boom)
      :stop -> exit(:normal)
    end
  end
end
```

**Property.** The supervisor never dies, and whenever it has no live child a
restart is already in flight: either the worker's exit signal is pending
or the `{:EXIT, ...}` message is in the supervisor's mailbox.
-/

namespace Leanactors.Examples.Supervisor

open Leanactors Config Sys

-- `Msg`, `St`, `sup` and `sig` come from the translation of `elixir/src/supervisor.ex`.
export Leanactors.Gen.Supervisor (Msg St sup sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, fresh, .sup none k, .start => (.sup (some fresh) k, [.spawnLink (.worker 0)])
  | _, fresh, .sup (some c) k, .EXIT who _ =>
      if who = c then (.sup (some fresh) (k + 1), [.spawnLink (.worker 0)])
      else (.sup (some c) k, [])
  | _, _, .worker n, .job => (.worker (n + 1), [])
  | _, _, .worker n, .crash => (.worker n, [.exit .error])
  | _, _, .worker n, .stop => (.worker n, [.exit .normal])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Supervisor.beh = beh := by
  funext me fresh s m
  cases s with
  | sup c k => cases c <;> cases m <;> first | rfl | simp [Gen.Supervisor.beh, beh]
  | worker n => cases m <;> rfl

/-- The supervisor at pid 0 with `:start` in its mailbox; pid 1 is fresh. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.sup none 0, [.start]⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## Invariant -/

structure Inv (s : Sys St Msg) : Prop where
  /-- Fresh pids never collide with the supervisor. -/
  next_pos : 0 < s.next
  sup_alive : ∃ child k, s.cfg.stateOf 0 = some (.sup child k)
  /-- The current child is alive and linked, or its exit is on its way. -/
  child_ok : ∀ c k, s.cfg.stateOf 0 = some (.sup (some c) k) →
    ((s.cfg.get c).isSome ∧ (0, c) ∈ s.links) ∨
    (∃ r, (0, c, r) ∈ s.signals) ∨
    (∃ r, 0 < s.cfg.mcount 0 (.EXIT c r))

/-! ## Bounded model check -/

def livePids (s : Sys St Msg) : List Pid :=
  (List.range s.next).filter fun p => (s.cfg.get p).isSome

def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.sup none _) => true
  | some (.sup (some c) _) =>
    ((s.cfg.get c).isSome && s.links.contains (0, c)) ||
    [Reason.normal, .error].any (fun r => s.signals.contains (0, c, r)) ||
    [Reason.normal, .error].any (fun r => 0 < s.cfg.mcount 0 (.EXIT c r))
  | _ => false

/-- Every interleaving of actor runs, signal deliveries and environment
messages (`job`/`crash`/`stop` to any live pid), to a depth bound. -/
partial def explore (b : EBehavior St Msg) (sg : Signals St Msg) (s : Sys St Msg)
    (depth env : Nat) (path : List String := []) : Nat × Option (List String) :=
  if !checkInv s then (1, some path.reverse)
  else if depth = 0 then (1, none)
  else
    let runs := (livePids s).filterMap fun p => (runE b s p).map fun s' => (s', env, s!"run {p}")
    let sigs := (signalE sg s).map (fun s' => [(s', env, "signal")]) |>.getD []
    let envs := if env = 0 then [] else
      (livePids s).flatMap fun p =>
        [(.job : Msg), .crash, .stop].map fun m =>
          ({ s with cfg := s.cfg.deliver p m }, env - 1, s!"env {repr m} -> {p}")
    (runs ++ sigs ++ envs).foldl (fun (n, bad) (s', e, lbl) =>
      match bad with
      | some _ => (n, bad)
      | none =>
        let (n', bad') := explore b sg s' (depth - 1) e (lbl :: path)
        (n + n', bad')) (1, none)

#eval explore beh sig init 9 4

/-- **Mutant**: the supervisor forgets `Process.flag(:trap_exit, true)`. -/
def sigNoTrap : Signals St Msg := { sig with traps := fun _ => false }

#eval explore beh sigNoTrap init 9 4

/-- A concrete trace: start, one job, a crash, the signal, the restart. -/
def trace : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0]                              -- spawns worker 1
  let s2 := { s1 with cfg := (s1.cfg.deliver 1 .job).deliver 1 .crash }
  runSys beh sig s2 [.run 1, .run 1, .signal, .run 0]                 -- job, crash, signal, restart

#eval (trace.cfg.stateOf 0, trace.cfg.stateOf 1, trace.cfg.stateOf 2, trace.next, trace.links, trace.signals)

end Leanactors.Examples.Supervisor
