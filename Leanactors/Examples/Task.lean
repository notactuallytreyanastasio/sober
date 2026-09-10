import Leanactors.Explore
import Leanactors.Gen.Task
/-!
# Leanactors.Examples.Task

An async task, translated from `elixir/src/task.ex`: the caller starts a
worker, monitors it, and waits for either `{:reply, v}` or
`{:DOWN, _, :process, pid, reason}`.

**Property.** A pending job is never lost: while the caller is waiting on
worker `w`, either `w` is alive and monitored, or its DOWN notification is
queued, or the reply is in the caller's mailbox, or the DOWN message is.
-/

namespace Leanactors.Examples.Task

open Leanactors Config Sys

export Leanactors.Gen.Task (Msg St caller sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | me, fresh, .caller none r, .go => (.caller (some fresh) r, [.spawn (.worker me 0), .monitor fresh])
  | _, _, .caller _ r, .reply _ => (.caller none (r + 1), [])
  | _, _, .caller (some w) r, .DOWN who _ =>
      if who = w then (.caller none r, []) else (.caller (some w) r, [])
  | _, _, .worker parent n, .compute => (.worker parent n, [.send parent (.reply (n + 1)), .exit .normal])
  | _, _, .worker p n, .crash => (.worker p n, [.exit .error])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Task.beh = beh := by
  funext me fresh s m
  cases s with
  | caller w r => cases w <;> cases m <;> first | rfl | simp [Gen.Task.beh, beh]
  | worker p n => cases m <;> rfl

/-- The caller at pid 0 with `:go` in its mailbox; pid 1 is fresh. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.caller none 0, [.go]⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## Invariant -/

structure Inv (s : Sys St Msg) : Prop where
  next_pos : 0 < s.next
  /-- Nobody links, so no exit signal can ever reach the (non-trapping) caller. -/
  links_nil : s.links = []
  signals_nil : s.signals = []
  caller_alive : ∃ w r, s.cfg.stateOf 0 = some (.caller w r)
  /-- A pending job always has its answer or its failure on the way. -/
  pending_ok : ∀ w r, s.cfg.stateOf 0 = some (.caller (some w) r) →
    ((s.cfg.get w).isSome ∧ (0, w) ∈ s.monitors) ∨
    (∃ rs, (0, w, rs) ∈ s.downs) ∨
    (∃ v, 0 < s.cfg.mcount 0 (.reply v)) ∨
    (∃ rs, 0 < s.cfg.mcount 0 (.DOWN w rs))

/-! ## Bounded model check -/

def checkInv (s : Sys St Msg) : Bool :=
  s.links.isEmpty && s.signals.isEmpty &&
  match s.cfg.stateOf 0 with
  | some (.caller none _) => true
  | some (.caller (some w) _) =>
    ((s.cfg.get w).isSome && s.monitors.contains (0, w)) ||
    [Reason.normal, .error].any (fun rs => s.downs.contains (0, w, rs)) ||
    (List.range 8).any (fun v => 0 < s.cfg.mcount 0 (.reply v)) ||
    [Reason.normal, .error].any (fun rs => 0 < s.cfg.mcount 0 (.DOWN w rs))
  | _ => false

/-- The property itself, weaker than `Inv`: a pending job is alive or its
answer/failure is on the way. Used to show the mutant loses a job. -/
def jobNotLost (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.caller (some w) _) =>
    (s.cfg.get w).isSome ||
    [Reason.normal, .error].any (fun rs => s.downs.contains (0, w, rs)) ||
    (List.range 8).any (fun v => 0 < s.cfg.mcount 0 (.reply v)) ||
    [Reason.normal, .error].any (fun rs => 0 < s.cfg.mcount 0 (.DOWN w rs))
  | _ => true

-- The environment may send `go`/`compute`/`crash` to any live pid.
#eval explore beh sig checkInv [.go, .compute, .crash] init 9 4

/-- **Mutant**: the caller forgets `Process.monitor`. A crash is silent and
the job is lost: the caller waits forever. -/
def behNoMonitor : EBehavior St Msg
  | me, fresh, .caller none r, .go => (.caller (some fresh) r, [.spawn (.worker me 0)])
  | _, _, .caller _ r, .reply _ => (.caller none (r + 1), [])
  | _, _, .caller (some w) r, .DOWN who _ =>
      if who = w then (.caller none r, []) else (.caller (some w) r, [])
  | _, _, .worker parent n, .compute => (.worker parent n, [.send parent (.reply (n + 1)), .exit .normal])
  | _, _, .worker p n, .crash => (.worker p n, [.exit .error])
  | _, _, s, _ => (s, [])

#eval explore behNoMonitor sig checkInv [.go, .compute, .crash] init 9 4
-- and against the property alone: the job is lost the moment the unmonitored worker crashes
#eval explore behNoMonitor sig jobNotLost [.go, .compute, .crash] init 9 4

/-- Concrete traces: a completed job, and a crashed one. -/
def done : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0]                                  -- spawn + monitor worker 1
  runSys beh sig { s1 with cfg := s1.cfg.deliver 1 .compute } [.run 1, .run 0, .down, .run 0]

def crashed : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0]
  runSys beh sig { s1 with cfg := s1.cfg.deliver 1 .crash } [.run 1, .down, .run 0]

#eval (done.cfg.stateOf 0, done.cfg.stateOf 1, done.monitors, done.downs)
#eval (crashed.cfg.stateOf 0, crashed.cfg.stateOf 1, crashed.monitors, crashed.downs)

end Leanactors.Examples.Task
