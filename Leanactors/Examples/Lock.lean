import Leanactors.Count
import Leanactors.Gen.Lock
/-!
# Leanactors.Examples.Lock

A lock server and any number of clients. The Elixir we are modelling:

```elixir
defmodule Lock do
  use GenServer
  # state: {holder :: from | nil, queue :: [from]}
  def handle_call(:acquire, from, {nil, q}), do: {:reply, :ok, {from, q}}
  def handle_call(:acquire, from, {h, q}),   do: {:noreply, {h, q ++ [from]}}
  def handle_cast({:release, p}, {{p, _}, []}), do: {:noreply, {nil, []}}
  def handle_cast({:release, p}, {{p, _}, [n | rest]}), do: GenServer.reply(n, :ok); {:noreply, {n, rest}}
  def handle_cast({:release, _}, s), do: {:noreply, s}
end

defmodule Client do
  # phase :: :idle | :holding ; driven by external :tick
  def handle_info(:tick, :idle),    do: :ok = GenServer.call(Lock, :acquire); {:noreply, :holding}
  def handle_info(:tick, :holding), do: GenServer.cast(Lock, {:release, self()}); {:noreply, :idle}
end
```

Clients *block* in `GenServer.call`. The translator turns that into the
await state `St.client_await0`: the client sends `acquire`, waits for
`reply ok`, and re-enqueues anything else that arrives meanwhile.

**Safety**: no two clients are `:holding` at once. No type system can
state this; it is a property of the *configuration*, including messages in
flight. We prove it via a numeric token invariant over mailbox counts.
-/

-- Lemma sets below are shared across branches that need different subsets.
set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Lock

open Leanactors Config

-- `Msg`, `Phase`, `St` and `server` come from the translation of `elixir/src/lock.ex`.
export Leanactors.Gen.Lock (Msg Phase Reply St server)

def beh : Behavior St Msg
  | _,  .lock none q,     .acquire p => (.lock (some p) q, [(p, .reply .ok)])
  | _,  .lock (some h) q, .acquire p => (.lock (some h) (q ++ [p]), [])
  | _,  .lock (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.lock none [], [])
        | n :: rest => (.lock (some n) rest, [(n, .reply .ok)])
      else (.lock (some h) q, [])
  | me, .client .idle,    .tick      => (.client_await0, [(server, .acquire me)])
  | me, .client .holding, .tick      => (.client .idle, [(server, .release me)])
  | _,  .client_await0,   .reply .ok => (.client .holding, [])
  | me, .client_await0,   m          => (.client_await0, [(me, m)])
  | _,  s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Lock.beh = beh := by
  funext p s m
  cases s with
  | lock h q => cases h <;> cases q <;> cases m <;> first | rfl | simp [Gen.Lock.beh, beh]
  | client ph => cases ph <;> cases m <;> first | rfl | simp [Gen.Lock.beh, beh]
  | client_await0 =>
    cases m with
    | reply r => cases r; rfl
    | tick => rfl
    | acquire _ => rfl
    | release _ => rfl

/-! ## The invariant

For each pid `p` we track six numbers:

* `a p` = copies of `acquire p` in the server's mailbox
* `qn p` = occurrences of `p` in the server's queue
* `g p` = copies of `reply ok` in `p`'s mailbox
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

/-- Where a client is in the protocol. The generated await state plays the
role `waiting` had before clients blocked. -/
inductive Loc | idle | waiting | holding
  deriving Repr, DecidableEq

def locOf (c : Config St Msg) (p : Pid) : Option Loc :=
  match c.stateOf p with
  | some (.client .idle) => some .idle
  | some (.client .holding) => some .holding
  | some .client_await0 => some .waiting
  | _ => none

def w (c : Config St Msg) (p : Pid) : Nat := if locOf c p = some .waiting then 1 else 0
def hd (c : Config St Msg) (p : Pid) : Nat := if locOf c p = some .holding then 1 else 0
def a (c : Config St Msg) (p : Pid) : Nat := c.mcount server (.acquire p)
def r (c : Config St Msg) (p : Pid) : Nat := c.mcount server (.release p)
/-- Grants in flight: `reply ok` messages in `p`'s mailbox. -/
def g (c : Config St Msg) (p : Pid) : Nat := c.mcount p (.reply .ok)

/-- `relBeforeAcq h mb`: no `acquire h` precedes a `release h` in `mb`.

This is where mailbox FIFO is load-bearing. Client `h` sends `release`
while holding and can only send its next `acquire` after that, so under
per-pair FIFO the server never sees `acquire h` ahead of a pending
`release h`. Without it the server could enqueue the current holder,
and rank accounting (FCFS) would break. -/
def relBeforeAcq (h : Pid) : List Msg → Bool
  | [] => true
  | .acquire h' :: rest => (h' != h || rest.count (.release h) == 0) && relBeforeAcq h rest
  | _ :: rest => relBeforeAcq h rest

theorem relBeforeAcq_tail {h : Pid} {m : Msg} {l : List Msg}
    (hl : relBeforeAcq h (m :: l) = true) : relBeforeAcq h l = true := by
  cases m <;> simp [relBeforeAcq] at hl <;> simp_all

theorem relBeforeAcq_head {h : Pid} {l : List Msg}
    (hl : relBeforeAcq h (.acquire h :: l) = true) : l.count (.release h) = 0 := by
  simp [relBeforeAcq] at hl
  exact hl.1

/-- Appending is safe unless the new message is `release h` while an
`acquire h` is already pending. -/
theorem relBeforeAcq_append {h : Pid} {l : List Msg} (m : Msg)
    (hl : relBeforeAcq h l = true) (hm : m = .release h → l.count (.acquire h) = 0) :
    relBeforeAcq h (l ++ [m]) = true := by
  induction l with
  | nil =>
    cases m with
    | acquire x => simp [relBeforeAcq]
    | release x => simp [relBeforeAcq]
    | reply r => simp [relBeforeAcq]
    | tick => simp [relBeforeAcq]
  | cons x rest ih =>
    cases x with
    | acquire x' =>
      simp [relBeforeAcq] at hl
      obtain ⟨h1, h2⟩ := hl
      have hm' : m = .release h → rest.count (.acquire h) = 0 := by
        intro e; have := hm e; simp [List.count_cons] at this; exact this.1
      have ih' := ih h2 hm'
      simp only [List.cons_append, relBeforeAcq, ih', Bool.and_true]
      by_cases hx : x' = h
      · subst hx
        simp at h1 ⊢
        cases m with
        | release y =>
          by_cases hy : y = x'
          · subst hy; have := hm rfl; simp at this
          · simp [List.count_append, List.count_cons, h1, hy]
        | acquire y => simp [List.count_append, List.count_cons, h1]
        | reply r => simp [List.count_append, List.count_cons, h1]
        | tick => simp [List.count_append, List.count_cons, h1]
      · simp [hx]
    | release x' =>
      simp [relBeforeAcq] at hl
      have hm' : m = .release h → rest.count (.acquire h) = 0 := by
        intro e; have := hm e; simp [List.count_cons] at this; exact this
      simpa [relBeforeAcq] using ih hl hm'
    | reply r =>
      simp [relBeforeAcq] at hl
      have hm' : m = .release h → rest.count (.acquire h) = 0 := by
        intro e; have := hm e; simp [List.count_cons] at this; exact this
      simpa [relBeforeAcq] using ih hl hm'
    | tick =>
      simp [relBeforeAcq] at hl
      have hm' : m = .release h → rest.count (.acquire h) = 0 := by
        intro e; have := hm e; simp [List.count_cons] at this; exact this
      simpa [relBeforeAcq] using ih hl hm'

structure Inv (c : Config St Msg) : Prop where
  hasServer : ∃ h q, c.stateOf server = some (.lock h q)
  queue_empty : ∀ q, c.stateOf server = some (.lock none q) → q = []
  /-- FIFO consequence: `release h` is never behind an `acquire h`. -/
  ordered : ∀ h mb, c.mboxOf server = some mb → relBeforeAcq h mb = true
  /-- The holder is never also queued (needs `ordered`). -/
  holder_not_queued : ∀ h q, c.stateOf server = some (.lock (some h) q) → q.count h = 0
  only_srv : ∀ p h q, c.stateOf p = some (.lock h q) → p = server
  nonholder : ∀ h q, c.stateOf server = some (.lock h q) → ∀ p, h ≠ some p →
    g c p = 0 ∧ hd c p = 0 ∧ r c p = 0 ∧ a c p + q.count p = w c p
  holder : ∀ h q, c.stateOf server = some (.lock (some h) q) →
    g c h + hd c h + r c h = 1 ∧
    (g c h = 1 → w c h = 1 ∧ a c h = 0 ∧ q.count h = 0) ∧
    (hd c h = 1 → a c h = 0 ∧ q.count h = 0) ∧
    (r c h = 1 → a c h + q.count h = w c h)

/-- **Mutual exclusion follows from the invariant.** -/
theorem Inv.mutex {c : Config St Msg} (hi : Inv c) :
    ∀ p q, hd c p = 1 → hd c q = 1 → p = q := by
  intro p q hp hq
  obtain ⟨h, qu, hs⟩ := hi.hasServer
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
  ⟨fun p => if p = server then some ⟨.lock none [], []⟩
            else if p ≤ n then some ⟨.client .idle, []⟩ else none⟩

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


def checkInv (c : Config St Msg) (pids : List Pid) : Bool :=
  match c.stateOf server with
  | some (.lock h q) =>
    (h != none || q.isEmpty) &&
    (match h with | some hh => q.count hh == 0 | none => true) &&
    (match c.mboxOf server with | some mb => pids.all (relBeforeAcq · mb) | none => false) &&
    pids.all fun p =>
      (match c.stateOf p with
       | some (.client _) => true
       | some .client_await0 => true
       | some (.lock _ _) => decide (p = server)
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
