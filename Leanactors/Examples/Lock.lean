import Leanactors.Count
/-!
# Leanactors.Examples.Lock

A lock server and any number of clients. The Elixir we are modelling:

```elixir
defmodule Lock do
  use GenServer
  # state: {holder :: pid() | nil, queue :: [pid()]}
  def handle_cast({:acquire, p}, {nil, q}), do: send(p, :grant); {:noreply, {p, q}}
  def handle_cast({:acquire, p}, {h, q}),   do: {:noreply, {h, q ++ [p]}}
  def handle_cast({:release, p}, {p, []}),  do: {:noreply, {nil, []}}
  def handle_cast({:release, p}, {p, [n | rest]}), do: send(n, :grant); {:noreply, {n, rest}}
  def handle_cast({:release, _}, s), do: {:noreply, s}
end

defmodule Client do
  # phase :: :idle | :waiting | :holding ; driven by external :tick
  def handle_info(:tick, :idle),   do: GenServer.cast(Lock, {:acquire, self()}); {:noreply, :waiting}
  def handle_info(:grant, :waiting), do: {:noreply, :holding}
  def handle_info(:tick, :holding), do: GenServer.cast(Lock, {:release, self()}); {:noreply, :idle}
  def handle_info(_, s), do: {:noreply, s}
end
```

**Safety**: no two clients are `:holding` at once. No type system can
state this; it is a property of the *configuration*, including messages in
flight. We prove it via a numeric token invariant over mailbox counts.
-/

namespace Leanactors.Examples.Lock

open Leanactors Config

inductive Msg
  | acquire (p : Pid)
  | release (p : Pid)
  | grant
  | tick
  deriving Repr, DecidableEq

inductive Phase | idle | waiting | holding
  deriving Repr, DecidableEq

inductive St
  | srv (holder : Option Pid) (queue : List Pid)
  | cli (phase : Phase)
  deriving Repr, DecidableEq

/-- The lock server lives at pid 0. -/
def server : Pid := 0

def beh : Behavior St Msg
  | _,  .srv none q,     .acquire p => (.srv (some p) q, [(p, .grant)])
  | _,  .srv (some h) q, .acquire p => (.srv (some h) (q ++ [p]), [])
  | _,  .srv (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.srv none [], [])
        | n :: rest => (.srv (some n) rest, [(n, .grant)])
      else (.srv (some h) q, [])
  | me, .cli .idle,    .tick  => (.cli .waiting, [(server, .acquire me)])
  | _,  .cli .waiting, .grant => (.cli .holding, [])
  | me, .cli .holding, .tick  => (.cli .idle, [(server, .release me)])
  | _,  s, _ => (s, [])

/-! ## The invariant

For each pid `p` we track six numbers:

* `a p` = copies of `acquire p` in the server's mailbox
* `qn p` = occurrences of `p` in the server's queue
* `g p` = copies of `grant` in `p`'s mailbox
* `r p` = copies of `release p` in the server's mailbox
* `w p` = 1 if `p` is a client in phase `waiting`
* `hd p` = 1 if `p` is a client in phase `holding`

A **non-holder** `p` satisfies `g = hd = r = 0` and `a + qn = w`.
The **holder** `h` satisfies `g + hd + r = 1` with the token's location
pinning the client's phase:
* `g = 1 → w = 1 ∧ a = qn = 0` (grant in flight; client still waiting)
* `hd = 1 → a = qn = 0`         (holding; nothing pending)
* `r = 1 → a + qn = w`          (release in flight; client may have re-requested)

Note this does *not* assume FIFO. The case "acquire h processed while h is
still holder" (impossible under FIFO) is simply handled by `a + qn = w`.
-/

def phaseOf (c : Config St Msg) (p : Pid) : Option Phase :=
  match c.stateOf p with
  | some (.cli ph) => some ph
  | _ => none

def w (c : Config St Msg) (p : Pid) : Nat := if phaseOf c p = some .waiting then 1 else 0
def hd (c : Config St Msg) (p : Pid) : Nat := if phaseOf c p = some .holding then 1 else 0
def a (c : Config St Msg) (p : Pid) : Nat := c.mcount server (.acquire p)
def r (c : Config St Msg) (p : Pid) : Nat := c.mcount server (.release p)
def g (c : Config St Msg) (p : Pid) : Nat := c.mcount p .grant

structure Inv (c : Config St Msg) : Prop where
  srv : ∃ h q, c.stateOf server = some (.srv h q)
  only_srv : ∀ p h q, c.stateOf p = some (.srv h q) → p = server
  nonholder : ∀ h q, c.stateOf server = some (.srv h q) → ∀ p, h ≠ some p →
    g c p = 0 ∧ hd c p = 0 ∧ r c p = 0 ∧ a c p + q.count p = w c p
  holder : ∀ h q, c.stateOf server = some (.srv (some h) q) →
    g c h + hd c h + r c h = 1 ∧
    (g c h = 1 → w c h = 1 ∧ a c h = 0 ∧ q.count h = 0) ∧
    (hd c h = 1 → a c h = 0 ∧ q.count h = 0) ∧
    (r c h = 1 → a c h + q.count h = w c h)

/-- **Mutual exclusion follows from the invariant.** -/
theorem Inv.mutex {c : Config St Msg} (hi : Inv c) :
    ∀ p q, hd c p = 1 → hd c q = 1 → p = q := by
  intro p q hp hq
  obtain ⟨h, qu, hs⟩ := hi.srv
  have key : ∀ x, hd c x = 1 → h = some x := by
    intro x hx
    by_cases hne : h = some x
    · exact hne
    · have := (hi.nonholder h qu hs x hne).2.1
      omega
  exact Option.some.inj ((key p hp).symm.trans (key q hq))

/-! ## Bounded model check

Before proving `Inv` inductive we check it on every interleaving up to a
depth bound, including environment ticks delivered at arbitrary times.
This is cheap insurance against an invariant that is *true* but not
*inductive*. -/

/-- Server at pid 0, idle clients at pids `1..n`, all mailboxes empty. -/
def initCfg (n : Nat) : Config St Msg :=
  ⟨fun p => if p = server then some ⟨.srv none [], []⟩
            else if p ≤ n then some ⟨.cli .idle, []⟩ else none⟩

/-! ## Environment

Ticks are external stimulus (a timer, a user, a shell). They may arrive at
any pid at any time. `ReachEnv` interleaves environment ticks with actor
steps; it is the honest reachability relation for this system. -/

inductive EnvStep : Config St Msg → Config St Msg → Prop
  | tick (c : Config St Msg) (p : Pid) : EnvStep c (c.deliver p .tick)

inductive ReachEnv : Config St Msg → Config St Msg → Prop
  | refl (c) : ReachEnv c c
  | step {a b c} : Step beh a b → ReachEnv b c → ReachEnv a c
  | env {a b c} : EnvStep a b → ReachEnv b c → ReachEnv a c

instance : DecidableEq (Option Phase) := inferInstance

def checkInv (c : Config St Msg) (pids : List Pid) : Bool :=
  match c.stateOf server with
  | some (.srv h q) =>
    pids.all fun p =>
      (match c.stateOf p with
       | some (.cli _) => true
       | some (.srv _ _) => decide (p = server)
       | none => true) &&
      (if h = some p then
        decide (g c p + hd c p + r c p = 1) &&
        (g c p != 1 || decide (w c p = 1 ∧ a c p = 0 ∧ q.count p = 0)) &&
        (hd c p != 1 || decide (a c p = 0 ∧ q.count p = 0)) &&
        (r c p != 1 || decide (a c p + q.count p = w c p))
      else
        decide (g c p = 0 ∧ hd c p = 0 ∧ r c p = 0 ∧ a c p + q.count p = w c p))
  | _ => false

def mutexOk (c : Config St Msg) (pids : List Pid) : Bool :=
  (pids.filter fun p => hd c p = 1).length ≤ 1

/-- Explore all schedules under behaviour `b`: at each node either some actor
runs or the environment ticks some client (bounded by `ticks`). Returns the
number of configurations visited and, if one violated `Inv` or mutex, the
path to it. -/
partial def explore (b : Behavior St Msg) (c : Config St Msg) (pids : List Pid)
    (depth ticks : Nat) (path : List String := []) : Nat × Option (List String) :=
  if !(checkInv c pids && mutexOk c pids) then (1, some path.reverse)
  else if depth = 0 then (1, none)
  else
    let runs := pids.filterMap fun p => (step b c p).map fun c' => (c', ticks, s!"run {p}")
    let tks := if ticks = 0 then [] else
      (pids.filter (· ≠ server)).map fun p => (c.deliver p .tick, ticks - 1, s!"tick {p}")
    (runs ++ tks).foldl (fun (n, bad) (c', t, lbl) =>
      match bad with
      | some _ => (n, bad)
      | none =>
        let (n', bad') := explore b c' pids (depth - 1) t (lbl :: path)
        (n + n', bad')) (1, none)

#eval explore beh (initCfg 2) [0, 1, 2] 9 5
#eval explore beh (initCfg 3) [0, 1, 2, 3] 7 4

end Leanactors.Examples.Lock
