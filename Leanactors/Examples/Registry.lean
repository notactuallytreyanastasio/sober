import Leanactors.Explore
import Leanactors.Gen.Registry
/-!
# Leanactors.Examples.Registry

A name registry, translated from `elixir/src/registry.ex`: names from a
small enum map to the pid that registered them. The state is an Elixir map
`%{name() => pid()}`, modelled as the association list `List (Name × Pid)`
of `Leanactors/AssocList.lean`. A registering client is monitored and its
names are dropped when its DOWN arrives; two clients (pids 1 and 2) claim
names through a blocking `GenServer.call` and may crash.

**Property.** A registered name maps to a live pid or a DOWN for it is in
flight: for every `(n, p)` in the registry's map, either `p` is alive and
monitored by the registry, or its DOWN is queued, or the DOWN message is
already in the registry's mailbox. The same shape as the task invariant,
quantified over the entries of a map.
-/

namespace Leanactors.Examples.Registry

open Leanactors Config Sys

export Leanactors.Gen.Registry (Name Err Reply Msg St reg sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, _, .reg m, .register pid n =>
      if AssocList.hasKey m n then (.reg m, [.send pid (.reply (.error .taken))])
      else (.reg (AssocList.insert m n pid), [.monitor pid, .send pid (.reply .ok)])
  | _, _, .reg m, .lookup caller n =>
      match AssocList.get? m n with
      | some p => (.reg m, [.send caller (.reply (.found p))])
      | none => (.reg m, [.send caller (.reply .not_found)])
  | _, _, .reg m, .unregister n => (.reg (AssocList.erase m n), [])
  | _, _, .reg m, .DOWN p _ => (.reg (AssocList.reject m fun (_, q) => q = p), [])
  | me, _, .client k, .claim n => (.client_await0 k, [.send reg (.register me n)])
  | _, _, .client k, .crash => (.client k, [.exit .error])
  | _, _, .client_await0 k, .reply r => if r = .ok then (.client (k + 1), []) else (.client k, [])
  | me, _, .client_await0 k, m => (.client_await0 k, [.send me m])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Registry.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;> first | rfl | simp [Gen.Registry.beh, beh]

/-- The registry at pid 0 with an empty map, two idle clients at 1 and 2. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.reg [], []⟩
                     else if p = 1 ∨ p = 2 then some ⟨.client 0, []⟩ else none⟩
    next := 3, links := [], signals := [] }

/-! ## The property, as a bounded check -/

/-- `p` is alive and monitored by the registry, or a DOWN for it is queued,
or the DOWN message is in the registry's mailbox. -/
def entryOk (s : Sys St Msg) (p : Pid) : Bool :=
  ((s.cfg.get p).isSome && s.monitors.contains (0, p)) ||
  [Reason.normal, .error, .kill].any (fun rs => s.downs.contains (0, p, rs)) ||
  [Reason.normal, .error, .kill].any (fun rs => 0 < s.cfg.mcount 0 (.DOWN p rs))

/-- The registry is alive and every registered pid is accounted for. -/
def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.reg m) => m.all fun (_, p) => entryOk s p
  | _ => false

/-- The environment: clients claim `a` or `b` and may crash; anyone may
ask the registry to unregister `a`. -/
def envMsgs : Pid → List Msg
  | 0 => [.unregister .a]
  | 1 => [.claim .a, .claim .b, .crash]
  | 2 => [.claim .a, .crash]
  | _ => []

def explore (b : EBehavior St Msg) (sg : Signals St Msg) (chk : Sys St Msg → Bool)
    (s : Sys St Msg) (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sg chk envMsgs s depth env

#eval explore beh sig checkInv init 7 3

/-- **Mutant**: the registry forgets `Process.monitor`. A crashed client's
name stays mapped to a dead pid. -/
def behNoMonitor : EBehavior St Msg
  | _, _, .reg m, .register pid n =>
      if AssocList.hasKey m n then (.reg m, [.send pid (.reply (.error .taken))])
      else (.reg (AssocList.insert m n pid), [.send pid (.reply .ok)])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behNoMonitor sig checkInv init 7 3

/-- The property alone, weaker than `checkInv` (alive, or a DOWN on its
way, without asking for the monitor): the mutant loses a name the moment
an unmonitored client crashes. -/
def nameNotLost (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.reg m) => m.all fun (_, p) =>
      (s.cfg.get p).isSome ||
      [Reason.normal, .error, .kill].any (fun rs => s.downs.contains (0, p, rs)) ||
      [Reason.normal, .error, .kill].any (fun rs => 0 < s.cfg.mcount 0 (.DOWN p rs))
  | _ => false

#eval explore behNoMonitor sig nameNotLost init 7 3

/-! ## Concrete traces -/

/-- Client 1 claims `a`, then client 2 asks for `a` and is told it is taken. -/
def taken : Sys St Msg :=
  let s1 := runSys beh sig { init with cfg := init.cfg.deliver 1 (.claim .a) } [.run 1, .run 0, .run 1]
  runSys beh sig { s1 with cfg := s1.cfg.deliver 2 (.claim .a) } [.run 2, .run 0, .run 2]

/-- Then client 1 crashes: its DOWN reaches the registry and `a` is freed. -/
def freed : Sys St Msg :=
  runSys beh sig { taken with cfg := taken.cfg.deliver 1 .crash } [.run 1, .down, .run 0]

#eval (taken.cfg.stateOf 0, taken.cfg.stateOf 1, taken.cfg.stateOf 2, taken.monitors)
#eval (freed.cfg.stateOf 0, freed.cfg.stateOf 1, freed.cfg.stateOf 2, freed.monitors, freed.downs)

end Leanactors.Examples.Registry
