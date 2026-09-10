# leanactors: design notes

These notes are for someone who knows Elixir and Lean 4 but has not opened
this repository. They explain what was built, why it has the shape it has,
and what was learned along the way. The README is the reference; this is
the narrative. Node ids in parentheses refer to the decision graph exported
in `docs/graph-data.json` (127 nodes, types goal/option/decision/action/
outcome/observation), which was kept in real time as the work was done.

## 1. The question and the thesis

The original prompt (node 1) was: could Lean and Elixir's gradual type
system be combined to formally verify Elixir programs? Build an actor model
in Lean and try it.

The thesis that emerged is a division of labour:

* Elixir's `@type` declarations are the **type oracle**. They fix the shapes:
  what messages exist, what a state looks like, where `nil` means `Option`,
  which atom unions are enums. Nothing in the translator inspects values;
  every translation decision is type-directed.
* Lean handles the **interleavings**. Elixir's type checker can confirm that
  each `handle_cast` clause returns a `non_neg_integer()` given one; it
  cannot say anything about what happens when several processes and their
  in-flight messages are scheduled in arbitrary order. That is a property
  of the whole configuration, and it is what the Lean proofs are about.

Three ways of building the Lean side were considered at the start (nodes
2-4). A deep embedding (Elixir AST plus operational semantics interpreted in
Lean) was rejected for v1 as too much metatheory before any payoff. Modelling
the BEAM in full (mailboxes, links, monitors, supervisors) before proving
anything was deferred. The choice (node 5) was a shallow embedding: an actor
is a Lean function, the scheduler is a labelled transition system, and BEAM
features are layered on once the core is proven. The rationale recorded on
the edge is "provable in days not months, keeps proofs about the system not
the interpreter". That turned out to hold.

Everything is plain Lean 4 (4.33.1), no Mathlib. The absence of Mathlib
shows up repeatedly in the observation nodes as small friction (`by_contra`
missing, `Nat.` prefixes, `List.count` on singletons not reducing), never as
a blocker.

## 2. The model, layer by layer

### Config and Step (`Leanactors/Core.lean`, 104 lines)

An actor's behaviour is a pure function:

```lean
abbrev Behavior (σ μ : Type) := Pid → σ → μ → σ × List (Pid × μ)
```

It receives its own pid (`self()`), its state and one message, and returns
the new state and the sends it wants made, in order. This is
`handle_cast/2` with `send/2` reified as data. A `Config` maps pids to
`Option (Actor σ μ)`, where an actor is a state and a mailbox (a `List μ`).
`deliver` appends to the tail of a mailbox and silently drops sends to
dead pids, which is what the BEAM does.

`Step beh c c'` is the relational semantics: some actor with a non-empty
mailbox pops its head, runs `beh`, and the sends are delivered. Which actor
runs is the scheduler's choice, and `Reach` is the reflexive-transitive
closure, so a theorem stated over `Reach` holds under every scheduler,
fair or not. `step` and `run` are the executable versions, and `run_sound`
(`Props.lean`) says every `run` result is `Reach`-able, so a concrete
`#eval` trace is covered by a theorem about `Reach` with no extra proof.

### Props (`Leanactors/Props.lean`, 230 lines)

The general theorems about `Step`:

* `Step.frame`: a step names one pid; every other actor's state is untouched.
* `Step.domain`: no step creates or destroys an actor.
* `Step.queue`: every mailbox after a step is the old mailbox with at most
  one element dropped from the head and some list appended to the tail.
  This is the FIFO lemma.
* `Preserves beh P` / `Step.preserves` / `Reach.preserves`: if every clause
  preserves a per-state predicate `P`, so does every reachable configuration.
* `step_sound` / `run_sound`: the executable semantics is contained in the
  relational one.

### Count (`Leanactors/Count.lean`, 229 lines)

Cross-actor invariants need to talk about messages in flight. `mcount c q m`
counts occurrences of `m` in `q`'s mailbox. The central theorem is
`Step.chars`: every step is characterised as arithmetic over `stateOf` and
`mcount`, plus an exact mailbox equation

```lean
c'.mboxOf q = (if q = p then some rest else c.mboxOf q).map (· ++ sendsTo (beh p s m).2 q)
```

Downstream proofs `obtain ⟨p, s, m, rest, hget, hstate, hcount, hmbox⟩ := h.chars`
and then reason with `simp` and `omega`. `Reach.inv` is the configuration-
level induction principle. The mailbox clause was added later (node 77),
when the FCFS proof needed the list and not just its counts.

### Sys (`Leanactors/Sys.lean`, 327 lines)

Spawning, links, monitors, exits and timers are a layer over `Config`, not
a rewrite of it (decision at node 86; the in-place rewrite was rejected as
"weeks of re-proving", the synchronous exit cascade because it needs
well-founded recursion over a function-typed config). An `EBehavior`
returns a list of `Effect`s (`send`, `spawn`, `spawnLink`, `link`,
`monitor`, `spawnMonitor`, `sendAfter`, `signal`, `exit`) and additionally
receives the next fresh pid, so a parent knows its child's pid in the same
step. A `Sys` is a `Config` plus `next`, `links`, `signals`, `monitors`,
`downs` and `timers`.

Exits propagate asynchronously, as on the BEAM. `Sys.terminate p r` removes
`p`, drops its links, and queues one `(q, p, r)` signal per linked `q` and
one DOWN per watcher. Separate steps `signalE` and `downE` deliver the
oldest pending signal or notification: a trapping target receives the exit
as a message through the `Signals.exitMsg` codec, a non-trapping target
ignores `normal` and is itself terminated by `error`, which queues more
signals. No recursion, every step is a plain function. `SysStep` has four
constructors (`run`, `signal`, `down`, `timer`), `SysReach.inv` is the
induction principle, and `runSys_sound` is the executable counterpart.

The conservativity theorem `runE_lift` says that on a system with no
links, signals, monitors, downs or timers, running the lifted message-only
behaviour is exactly the old `step`. The bank and lock results never had to
be touched when `Sys` arrived (node 88).

## 3. The translator

`elixir/to_lean.exs` (799 lines, one module `ToLean`) reads a file of
`GenServer` modules and emits one Lean file per source into
`Leanactors/Gen/`. The invocation is fixed by `check.sh`, for example

```
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server
```

where `--pid Lock=server` says that the registered name `Lock` is the
constant pid `server` (0 in the generated file). The generated files are
committed, and `check.sh` regenerates all five and fails if any differs.

### Conventions

* `@type msg` is a union of atoms and tagged tuples; each alternative is a
  `Msg` constructor. `@type call` alternatives become constructors with a
  leading `caller : Pid`; `@type reply` becomes the single constructor
  `Msg.reply`. All modules in one file share one `Msg` and one `St`.
* `@type state` gives one `St` constructor per module, named after the
  module in lowercase, with positional fields `f0, f1, ...` for tuples or
  `s` for a scalar. `pid()` and `GenServer.from()` are `Pid`, `integer()`
  is `Int`, `non_neg_integer()` is `Nat`, `boolean()` is `Bool`, `[T]` is
  `List T`, `T | nil` is `Option T`, and a union of atoms is a generated
  enum (`Phase`, `Reply`).
* `handle_cast/2`, `handle_info/2` and `handle_call/3` clauses, in source
  order, become the arms of `def beh`. Guards become `if ... then ... else`
  with fallthrough to the next clause that subsumes the pattern; subsumed
  clauses are dropped because Lean rejects redundant alternatives (node 47).
* Each module gets a catch-all arm and `beh` ends with `| _, s, _ => (s, [])`,
  annotated "GenServer would crash (cast) or ignore (info). Modelled as ignore."

### The type-directed decisions

Node 47 lists what the types alone settled. A pattern variable at an
`Option` position that is already bound at the base type becomes `some x'`
plus an equality guard: this is how the non-linear Elixir pattern
`handle_cast({:release, p}, {{p, _}, [n | rest]})` becomes a Lean pattern
`.lock (some p') (n :: rest), .release p` with `if p = p'`. `nil` at an
`Option` position is `none`; an atom at an enum type is a constructor;
`{:noreply, v}` with `v : Int` at an `Option Int` state is `some v`;
`[h | t]` at a list type is `h :: t`; `{pid, _}` at a `GenServer.from()`
position keeps the pid. No `@spec` beyond `msg` and `state` was needed.

Blocking calls are the one place the translator changes control flow. A
statement `v = GenServer.call(Mod, m)` splits the clause (`cps_split`): the
part before it runs and sends `Mod.m self`, the actor enters a generated
state `<mod>_await<i>` carrying the free variables the continuation needs,
a second clause resumes on `reply v`, and any other message arriving in the
await state is re-enqueued to self. Awaits nest: `Gen/Bank.lean` has
`client_await0`, `client_await1` and `client_await2 (a : Int)`, the last
capturing the first call's result for the `:audit` handler.

Effects mode is switched on per file (decision at node 101) when a handler
uses `Process.flag(:trap_exit, true)`, `GenServer.start_link`/`start`,
`Process.monitor`, `Process.send_after`, `Process.exit`, `{:stop, _, _}`,
`exit/1` or `{:noreply, s, t}`. Then the file emits an `EBehavior`, clauses
bind `fresh`, `{:ok, pid} = GenServer.start_link(Worker, arg)` becomes
`.spawnLink (.worker <arg>)` with `pid` aliased to `fresh`, exit reasons
collapse to `.normal` or `.error`, `{:EXIT, pid(), term()}` is typed
`EXIT (Pid) (Reason)`, `{:DOWN, ref, :process, pid, reason}` is typed
`DOWN (Pid) (Reason)` with the `ref` dropped, and a `sig : Signals St Msg`
record is generated with `traps` derived from which modules call
`Process.flag`. Files without effects keep producing a plain `Behavior`,
byte for byte as before.

### The trust boundary

The translator is unverified. What makes that acceptable is that every
example has a hand-written `beh` in `Leanactors/Examples/X.lean`, written
by reading the Elixir, and a theorem

```lean
theorem beh_eq_gen : Gen.Lock.beh = beh := by
  funext p s m
  cases s with ...  <;> first | rfl | simp [Gen.Lock.beh, beh]
```

All proofs are about the hand-written `beh`; `beh_eq_gen` connects them to
the generated one, and the generated one is what corresponds to the source.
A translator bug therefore shows up as a failed `rfl`, not as a false
theorem (node 104). Node 50 notes how cheap this is: one line per model
once both sides are structural matches on the same inductives; only guard
orientation and clause order had to agree, field names and redundant
catch-alls did not.

What is still trusted: that two independent readings of the same Elixir
(the translator's and the human's) are both faithful to what the BEAM does.
The drivers under `elixir/*.exs` are the check on that. `bank.exs` runs the
same stimulus on the BEAM and exits 1 if the final states differ from the
Lean `#eval` trace; the others check the proven property on a real run.

### What each source exercises

| Source | Mode | Translator features |
|---|---|---|
| `elixir/src/bank.ex` | messages | casts, guard fallthrough, `handle_call` server side, `Option Int` state, one and two nested blocking calls on the client |
| `elixir/src/lock.ex` | messages | `handle_call` with deferred `GenServer.reply/2`, non-linear pattern with equality guard, `[n \| rest]`, pattern-LHS blocking call (`:ok = GenServer.call(...)`), enum state |
| `elixir/src/supervisor.ex` | effects | `trap_exit`, `start_link` as `spawnLink`, `EXIT` typing, `{:stop, :boom, s}` and `{:stop, :normal, s}` as `exit` |
| `elixir/src/task.ex` | effects | `GenServer.start` as `spawn`, `Process.monitor`, `DOWN` typing and the `downMsg` codec, a send before `{:stop, :normal, _}` |
| `elixir/src/watchdog.ex` | effects | `{:noreply, s, t}` as a self-timer, `Process.exit(w, :kill)` as `signal`, send to a registered name, booleans, named wildcards, pid-narrowed `Option` patterns |

The generated files are 43 to 47 lines each; the sources are 54 to 73.

## 4. The proof recipe

Every example after the bank follows the same recipe, and the observation
at node 115 says so explicitly: bounded check, then a frame lemma, a
termination lemma, and one example-specific shape. The line counts below
are from the files at this commit.

**Bounded check first.** Each example file defines `checkInv` (a `Bool`
version of the invariant) and an `explore` function that enumerates every
interleaving of actor steps, signal deliveries, timer firings and
environment stimulus up to a depth, returning the number of configurations
visited and the first violating path if any. `#eval explore ...` runs at
`lake build` time. Recorded counts: the lock invariant on 77,925 and 23,281
configurations (nodes 71, 78); the supervisor on 236,220 (node 90); the task
on 243,526 (node 112); the watchdog on 10,365 (node 123). Node 29 and node
96 both make the same point in their post-mortems: none of the proof
iterations were about the invariant, because the checker had already
validated it. The iterations were about Lean plumbing.

**Frame lemma.** `Inv.frame` states the invariant is preserved by any step
that only adds: deliveries, spawns, no-op runs, a signal turning into a
mailbox message. It is stated with monotonicity hypotheses (`a.next ≤ b.next`,
`(a.cfg.get c).isSome → (b.cfg.get c).isSome`, counts do not decrease) so
that most cases of `Inv.step` are `apply Inv.frame` plus trivial side goals.
`SupervisorProof.lean` lines 27-49 (23 lines), `TaskProof.lean` 19-43 (25),
`WatchdogProof.lean` 18-39 (22; this one lets the watchdog's boolean flag
change as long as the child does not, which covers the `:timeout` step),
`LockProof.lean` 145-257 (113, because the lock's invariant has nine fields).

**Termination lemma.** `Inv.terminate_ne` says that when an actor other than
the one at pid 0 dies from an intermediate system that has the parent's
links, state and pending signals, the invariant holds afterwards: if the
dead actor was the current child, its link produces exactly the pending
signal the invariant's disjunction needs. Asynchronous signals make this a
plain record computation (node 96). `SupervisorProof.lean` 50-85 (36 lines),
`TaskProof.lean` 52-94 (43), `WatchdogProof.lean` 40-74 (35).

**One example-specific shape.** The task has `Inv.cleared` (`TaskProof.lean`
44-51, 8 lines): the caller moving to a state with no pending job makes the
obligation vacuous. The watchdog's specific shape is the three-effect spawn
(`spawnLink`, `send`, `sendAfter` in one step). The lock's is
`relBeforeAcq_head` for the reorder case (section 5).

**The case split.** `Inv.step` then cases on `SysStep` (or `Step`), on the
actor's state constructor and on the message, and each case is one of the
shapes. `SupervisorProof.lean` 95-366 (272 lines), `TaskProof.lean` 104-371
(268), `WatchdogProof.lean` 84-408 (325), `LockProof.lean` 258-627 (370).
Node 96 counts 20 of 22 supervisor cases as `apply frame` or
`apply terminate_ne`.

**Closing.** `init_inv`, `reach_inv := hr.inv Inv.step init_inv`, and the
named property as a projection: `supervisor_alive` and `restart_in_flight`
(`SupervisorProof.lean` 376-392), `job_never_lost` (`TaskProof.lean` 383),
`watchdog_alive` and `restart_in_flight` (`WatchdogProof.lean` 418-431),
`mutex_forever` (`LockProof.lean` 706) and `progress_forever` (775).

The bank is the degenerate case. Its invariant is per-actor, so
`beh_preserves` (`Bank.lean` 65-83, 19 lines) discharges every clause with
`simp` and `omega`, and `Reach.preserves` lifts it. Note that the bank's
state is `Int`, not `Nat`: non-negativity is proven, not baked into the type.

## 5. Findings that were surprising

**FIFO is not needed for safety; it is needed for FCFS.** Node 26, written
while designing the lock invariant: "I expected to need `Step.prefix` (FIFO).
Instead the `a + qn = w` equation handles the out-of-order case." The
out-of-order case is a client's next `acquire` reaching the server while its
previous `release` is still in flight. Node 57, after deadlock freedom went
through: "For this protocol FIFO is not needed for safety or deadlock
freedom. It would only matter for a fairness argument (bounded waiting)."
Node 81, after FCFS: "FIFO is finally load-bearing, and in exactly the place
predicted three sessions ago: the reorder 'acquire h while h holds' is
harmless for safety and deadlock freedom but breaks rank accounting."
The fix was two invariant fields over the server's mailbox as a list,
`ordered` (`relBeforeAcq`: no `acquire h` ahead of a `release h`) and
`holder_not_queued`, both inductive only because sends append at the tail.
That is the one place `Step.chars`' mailbox clause is used. The property is
`fcfs` in `LockFcfs.lean`: a client with `r` clients ahead sees at most `r`
handovers, and its rank drops by exactly one per handover.

**The invariant is stronger than the property.** `LockMutants.lean` has
three mutants. Mutant A (grant while held) violates mutual exclusion and is
caught with a trace. Mutant B (a blocked client re-sends `acquire` on every
tick) never violates mutual exclusion: it gets queued twice, granted a
second time while idle, ignores the grant, and the server believes it holds
the lock forever. Only `Inv` catches it, at the moment `a + qn = w` fails.
Mutant C (no check that the releaser is the holder) is not caught, and the
graph records this as the correct answer: node 36 says the first two mutants
written were both unreachable under honest clients and explored the same
state space as the original, and the invariant had predicted this
(`r c p = 0` for non-holders). The sender check is defensive against
misbehaving clients, not load-bearing for this protocol.

**Blocking calls are a compilation detail.** Node 72, after the lock's
clients were rewritten to block in `GenServer.call`: "Predicted the mutex
proof would need rework for the await state; in practice the six counters
and two equations were untouched." Only `locOf`, the view that maps the
generated `client_await0` to `waiting`, changed. The deferral clause (a
popped message re-sent to self) is a frame case because it touches no
counted message. The cost of keeping the core unchanged is in node 66: the
re-enqueue spins under an unfair scheduler, which is harmless for safety
proofs, blows up bounded exploration depth, and would need a fairness
assumption for liveness.

**The GenServer timeout reset.** Node 124, seen while writing
`elixir/watchdog.exs`: "any message resets a GenServer timeout, including
`:sys.get_state` polls. The driver never saw the timeout until it stopped
polling." The driver now sleeps past the timeout instead of polling. In the
model timers are untimed, so a `:timeout` may fire even after a `:pong`
arrived and the watchdog may kill a healthy worker. The property (a dead
worker always has its restart in flight) does not care why the worker died,
so the over-approximation costs nothing. Liveness of the watchdog (a hung
worker is eventually replaced) would need the timer to actually fire, that
is, a fairness assumption on timers plus a quiet mailbox.

**The crash-on-unhandled-cast gap.** Node 127 lists the remaining fidelity
gaps as "semantic, not syntactic": crash-on-unhandled-cast, real time,
selective receive beyond call/reply, non-identity `init`, multi-node. The
first is the one most likely to matter. On the BEAM an unmatched
`handle_cast` raises `FunctionClauseError` and the process exits with an
error reason; its links and monitors fire. The generated catch-all keeps
the process alive with its state unchanged. For the five current sources
the gap is not reachable: every `@type msg` alternative is either handled
or covered by an explicit `handle_info(_, s)` catch-all, and messages
outside `@type msg` are outside the model altogether. But a sixth source
could hit it, and the direction is the unsound one (section 6).

## 6. Known approximations and their direction

Over-approximations admit behaviours the BEAM does not have. A safety
property proven over the model then also holds on the BEAM (for the
modelled behaviours); liveness is where they hurt.

* Any scheduler, including unfair ones. `Reach` and `SysReach` quantify
  over all interleavings. Sound for safety; liveness would need fairness.
* Untimed timers (decision at node 119). Any pending timer may fire at any
  step, in any order, regardless of messages that arrived since it was
  armed. The BEAM under-fires when the mailbox is busy.
* Environment stimulus at any time (`EnvStep` in the lock, the `ticks`
  budget in every `explore`).
* Re-enqueue deferral for blocking calls adds self-message steps the BEAM
  does not take (it uses a save queue). Extra steps, same reachable states
  for the counted messages.
* Exit reasons collapse to `normal | error`. Anything non-normal, including
  `:kill`, is `error`. On the BEAM `:kill` is untrappable; in the model a
  trapping target would receive it as a message. None of the current
  sources send `:kill` to a trapping process, but this is the one place the
  collapse is an under-approximation rather than an over-approximation.

Under-approximations omit behaviours the BEAM has. A safety proof over the
model says nothing about the omitted paths.

* Unhandled casts do not crash (section 5). Direction: the BEAM has a
  crash-and-propagate path the model lacks.
* Closed message world: only `@type msg` alternatives exist. `:sys` messages,
  stray sends and typos are not modelled.
* Handler bodies are pure and total. No exceptions, no `raise`, no side
  effects beyond the recognised calls. The translator rejects anything
  outside its subset with a hard error rather than approximating.
* `init` must be the identity (`{:ok, pid} = GenServer.start_link(Mod, arg)`
  becomes `spawnLink (.mod arg)`); `Process.flag(:trap_exit, true)` in
  `init` is read as a static property of the module.
* Registered names are constant pids fixed by `--pid` (no registry, no
  registration races); monitor refs are dropped (no `demonitor`, `DOWN`
  matched on pid); timers cannot be cancelled; single node.

The equivalence theorems do not close any of these: `beh_eq_gen` shows the
hand model equals the generated model, not that either equals the BEAM. The
drivers are the only check in that direction, and they are property tests.

## 7. What to try first

1. `./check.sh` from the repo root (with `export PATH="$HOME/.elan/bin:$PATH"`).
   It regenerates the five `Gen/` files and diffs them, runs `lake build`
   (which runs every `#eval explore`), greps for `sorry`, and runs the five
   drivers on the BEAM. First build takes a few minutes.
2. Read `elixir/src/lock.ex` next to `Leanactors/Gen/Lock.lean` and then
   `Leanactors/Examples/Lock.lean`. The three files are short enough to hold
   in your head at once, and the invariant `Inv` with `Inv.mutex` (an
   eleven-line proof) is the clearest statement of what the model buys.
3. Break something. Change `q ++ [from]` to `[from | q]` in `lock.ex`
   (LIFO instead of FIFO queueing), run `check.sh`, and watch it fail at
   the diff. Regenerate with the command from `check.sh`, run `lake build`,
   and watch `beh_eq_gen` fail. Update the hand model to match and build
   again: the token invariant does not depend on queue order (its fields
   use `q.count`), so `Inv.step` is repairable where its `simp` calls
   mention `q ++ [p]`, but `Step.rank_step` in `LockFcfs.lean` cannot be:
   a newly queued client now raises everyone's rank without a handover.
   That is the whole chain, and the FIFO finding, in one edit.
4. Run the mutants: `Leanactors/Examples/LockMutants.lean` prints a witness
   path for A and B and `none` for C at build time.
5. Read `docs/graph-data.json` top to bottom, or `deciduous serve` if you
   have it. The observation nodes (16, 26, 29, 36, 47, 50, 57, 65, 66, 72,
   81, 96, 97, 104, 115, 124, 127) are the honest record, including the
   predictions that turned out wrong.
6. To extend it: a sixth `elixir/src/*.ex` within the subset listed in the
   header of `elixir/to_lean.exs`, two lines in `check.sh`, a hand model
   with `beh_eq_gen`, `checkInv` and `explore`, and only then the proof.
