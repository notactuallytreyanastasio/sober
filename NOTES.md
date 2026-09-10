# leanactors: design notes

These notes are for someone who knows Elixir and Lean 4 but has not opened
this repository. They explain what was built, why it has the shape it has,
and what was learned along the way. The README is the reference; this is
the narrative. Node ids in parentheses refer to the decision graph exported
in `docs/graph-data.json` (127 nodes when these notes were written; the
workflow that merged the pieces described below added its own subtree
under node 138, and the second round (section 7) its own under node 219;
types goal/option/decision/action/outcome/observation), which was kept in
real time as the work was done. Line counts and spans in sections 2-4
were re-measured after round 2; section 7 lists what that round changed.

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

### Sys (`Leanactors/Sys.lean`, about 328 lines)

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

### SysProps (`Leanactors/SysProps.lean`, about 1,079 lines)

The example proofs each re-derived the same `Sys`-level facts by hand:
steps that only add preserve everything, a termination touches only the
dead pid's row plus the link and monitor lists, a step changes at most one
actor's state. `SysProps.lean` states them once, over any `EBehavior`:
`Grows a b` (every field monotone, pids below `a.next` keep their state)
and `Frame p a b` (the same with `p` exempt), both reflexive and
transitive with `Grows.frame` embedding; `applyEffects_grows` and its
projections; `terminate_frame` and the exact contents of the signal and
DOWN queues after a death; `runE_frame`, `runE_of_no_exit`,
`signalE_frame`, `downE_grows`, `timerE_grows` with `_cases` unpackings;
`SysStep.stateOf_cases`; and `Sys.Fresh` (every live pid is below `next`),
preserved by every step, which turns the `q < next` side conditions of a
frame into "q is alive". Round 2 added `Effect.isolated` (everything but
`link`, `spawnLink`, `signal`) with `applyEffects_links_signals_of_isolated`,
`deliver_of_get_none`, `downE_of_codec` and the `links`/`signals`
projections of `downE` and `timerE` (node 250). `Examples/SysPropsDemo.lean`
shows three supervisor cases in one line each as `example`s (nodes
151-161; since round 2 the lemmas themselves live in `SupervisorProof`).
Writing it exposed a
core bug (node 159): `Sys.terminate` never set `timers`, so the structure
default `[]` dropped every pending timer whenever any actor died; a worker
crash silently disarmed the watchdog's timeout. `terminate` now keeps
them, `Frame` has a `timers` clause, and the watchdog checker grew from
10,365 to 10,411 configurations (nodes 206-208). One toolchain note from
that file: `omega` does not see through `abbrev Pid := Nat` on Lean
v4.33.1, so pid arithmetic there uses `Nat.lt_of_lt_of_le` and
`Nat.le_trans` explicitly (node 160).

## 3. The translator

`elixir/to_lean.exs` (about 1,340 lines, one module `ToLean`) reads a file
of `GenServer` modules and emits one Lean file per source into
`Leanactors/Gen/`. The invocation is fixed by `check.sh`, for example

```
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server
```

where `--pid Lock=server` says that the registered name `Lock` is the
constant pid `server` (0 in the generated file). Without any `--pid` flag
the names are derived from the source (`name: __MODULE__`,
`Process.register/2`; section 7), which is how `ttl.ex` is translated. The
generated files are committed, and `check.sh` regenerates all six and
fails if any differs; it then runs the 25 translator fixtures under
`elixir/test/` (section 7).

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
* `beh` ends with a global catch-all `| _, _, s, _ => (s, [])`, annotated
  "GenServer would crash (cast) or ignore (info). Modelled as ignore.",
  unless every module is already covered. Since the workflow merge (node
  138) three things narrow it: a cast or call tag the module's clauses do
  not cover gets a crash arm `(state, [.exit .error])` and a module's
  `handle_info` clauses are emitted after its cast/call and crash arms
  (nodes 173-187); a raw `receive` loop without a catch-all arm gets a
  defer arm `| me, _, .mod s_0 .., m => (.mod s_0 .., [.send me m])` as its
  last clause, so the global catch-all no longer covers it (nodes 188-199);
  and `def init(p), do: {:ok, e}` is translated at spawn sites (nodes
  162-172). Since round 2, coverage is a usefulness check over the rendered
  Lean patterns (Bool, Option, list and enum splits count), and a module
  whose every tag is covered or crashes gets neither a defer arm nor the
  catch-all (nodes 252, 284-287). See the README paragraphs on initial
  state, unhandled messages and raw processes.

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

Every file emits an `EBehavior St Msg` over `Leanactors.Sys` (there is one
output shape; decision at node 228 replaced the per-file "effects mode" of
node 101). Clauses bind `me` and `fresh`, sends are `.send` effects,
`{:ok, pid} = GenServer.start_link(Worker, arg)` becomes `.spawnLink
(.worker <arg>)` with `pid` aliased to `fresh`, exit reasons collapse to
`.normal` or `.error`, `{:EXIT, pid(), term()}` is typed `EXIT (Pid)
(Reason)`, `{:DOWN, ref, :process, pid, reason}` is typed `DOWN (Pid)
(Reason)` with the `ref` dropped, and a `sig : Signals St Msg` record is
always generated: `traps` from which modules call `Process.flag`, `exitMsg`
as `.EXIT p r` when some module declares it and otherwise a placeholder
(the first nullary message constructor) that is never consulted. A file
that only sends is a message-only `EBehavior`; its hand model stays a
plain `Behavior` and proves `Gen.X.beh = lift beh`, so the bank and lock
proofs did not move (node 242; the guarded withdraw/release clauses need
`simp only [..., lift]; split <;> rfl`, node 244).

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

| Source | Names | Translator features |
|---|---|---|
| `elixir/src/bank.ex` | `--pid Bank=bank` | casts, guard fallthrough, `handle_call` server side, `Option Int` state, one and two nested blocking calls on the client; message-only, hand model via `lift` |
| `elixir/src/lock.ex` | `--pid Lock=server` | `handle_call` with deferred `GenServer.reply/2`, non-linear pattern with equality guard, `[n \| rest]`, pattern-LHS blocking call (`:ok = GenServer.call(...)`), enum state; message-only, hand model via `lift` |
| `elixir/src/supervisor.ex` | `--pid Sup=sup` | `trap_exit`, `start_link` as `spawnLink`, `EXIT` typing, `{:stop, :boom, s}` and `{:stop, :normal, s}` as `exit`, a raw `receive` worker with a defer clause |
| `elixir/src/task.ex` | `--pid Caller=caller` | `GenServer.start` as `spawn`, `Process.monitor`, `DOWN` typing and the `downMsg` codec, a send before `{:stop, :normal, _}`, non-identity `init` |
| `elixir/src/watchdog.ex` | `--pid Watchdog=watchdog` | `{:noreply, s, t}` as a self-timer, `Process.exit(w, :kill)` as `signal`, send to a registered name, booleans, named wildcards, pid-narrowed `Option` patterns |
| `elixir/src/ttl.ex` | derived (`Process.register`) | `receive ... after` as the self-timer `after_run` armed on every re-entry and at the spawn site, `raise` in tail position as `.exit .error`, a raw process with an `Option Nat` state |

The generated files are 42 to 56 lines each; the sources are 55 to 85.

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
on 243,526 (node 112); the watchdog on 10,365 (node 123; 10,411 since
`Sys.terminate` keeps pending timers, see section 5). Node 29 and node
96 both make the same point in their post-mortems: none of the proof
iterations were about the invariant, because the checker had already
validated it. The iterations were about Lean plumbing.

**Frame lemma.** `Inv.frame` states the invariant is preserved by any step
that only adds: deliveries, spawns, no-op runs, a signal turning into a
mailbox message. It is stated with monotonicity hypotheses (`a.next ≤ b.next`,
`(a.cfg.get c).isSome → (b.cfg.get c).isSome`, counts do not decrease) so
that most cases of `Inv.step` are `apply Inv.frame` plus trivial side goals.
`SupervisorProof.lean` lines 33-54 (22 lines), `TaskProof.lean` 26-51 (26),
`WatchdogProof.lean` 26-48 (23; this one lets the watchdog's boolean flag
change as long as the child does not, which covers the `:timeout` step),
`LockProof.lean` 145-257 (113, because the lock's invariant has nine fields).
Since round 2 the `Sys` files mostly use it through `Inv.grows` (the
invariant is monotone along `SysProps.Grows`), one line each.

**Termination lemma.** `Inv.terminate_ne` says that when an actor other than
the one at pid 0 dies from an intermediate system that has the parent's
links, state and pending signals, the invariant holds afterwards: if the
dead actor was the current child, its link produces exactly the pending
signal the invariant's disjunction needs. Asynchronous signals make this a
plain record computation (node 96). Since round 2 it is a one-line
corollary of `Inv.terminate_core`, which also yields `Inv.terminate_frame`
(the same conclusion from a `Frame p` of the invariant system):
`SupervisorProof.lean` 91-133 (43 lines for the three), `TaskProof.lean`
96-146 (51), `WatchdogProof.lean` 85-127 (43).

**One example-specific shape.** The task has `Inv.cleared` (`TaskProof.lean`
87-95, 9 lines): the caller moving to a state with no pending job makes the
obligation vacuous. The watchdog's specific shape is the three-effect spawn
(`spawnLink`, `send`, `sendAfter` in one step). The lock's is
`relBeforeAcq_head` for the reorder case (section 5).

**The case split.** `Inv.step` then cases on `SysStep` (or `Step`), on the
actor's state constructor and on the message, and each case is one of the
shapes. `LockProof.lean` 258-627 (370 lines). The three `Sys` files used to
do the same (272, 268 and 325 lines; node 96 counted 20 of 22 supervisor
cases as `apply frame` or `apply terminate_ne`). Since round 2 they split
by pid instead (node 249, 274): `Inv.run_ne` handles any step of any pid
other than 0 without looking at the message, as `Inv.set_ne` then
`Inv.grows` (`applyEffects_grows`) or `Inv.terminate_frame`, via
`runE_cases`; `Inv.run` handles pid 0's spawn and no-op shapes; `Inv.signal`,
`Inv.down` and `Inv.timer` are `signalE_cases` plus `Inv.pop_signal`, and
one-line `Grows`. `SupervisorProof.lean` 134-263 (130 lines from the
supervisor lemmas to `Inv.step`), `TaskProof.lean` 147-289 (143),
`WatchdogProof.lean` 128-261 (134).

**Closing.** `init_inv`, `reach_inv := hr.inv Inv.step init_inv`, and the
named property as a projection: `supervisor_alive` and `restart_in_flight`
(`SupervisorProof.lean` 274-289), `job_never_lost` (`TaskProof.lean` 302),
`watchdog_alive` and `restart_in_flight` (`WatchdogProof.lean` 272-286),
`mutex_forever` (`LockProof.lean` 706) and `progress_forever` (775).

The bank is the degenerate case. Its invariant is per-actor, so
`beh_preserves` (`Bank.lean` 66-83, 18 lines) discharges every clause with
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

Closed since: the crash piece of the workflow (nodes 173-187) emits a
crash arm per uncovered cast/call tag in effects mode, and the watchdog
promptly demonstrated why it matters. With `:pong` accepted only while a
pong is expected, `explore` found after 742 configurations a late pong
(sent after the timeout had already fired the kill) that crashed the
watchdog; the fix is one `handle_cast(:pong, s)` ignore clause (nodes
179-181). The init piece (nodes 162-172) and the receive piece (nodes
188-199) closed non-identity `init` and selective receive beyond
call/reply. Round 2 removed message mode altogether, so the crash arm is
emitted for every file (section 7). Real time and multi-node remain.

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

* Closed message world: only `@type msg` alternatives exist. `:sys` messages,
  stray sends and typos are not modelled. A tag no callback of a module
  mentions is not classified and gets no crash arm (node 246).
* Handler bodies are pure. The only exception the model knows is an
  uncaught one in tail position: `raise`/`throw` as the last statement is
  `.exit .error` with the state unchanged (round 2). A `raise` anywhere
  else, `rescue`, `catch` and side effects beyond the recognised calls are
  hard errors rather than approximations.
* `init/1` must be a pure expression of its parameter (`{:ok, e}`, with
  `Process.flag(:trap_exit, true)` the only other statement allowed);
  `{:ok, pid} = GenServer.start_link(Mod, arg)` becomes `spawnLink` of `e`
  with the parameter bound to `arg`. `trap_exit` in `init` is read as a
  static property of the module.
* Raw processes: exactly one `receive` loop per module, one parameter, at
  most one `after` clause; a guard that fails re-enqueues the message to
  self, which adds self-message steps the BEAM does not take (same as the
  call deferral). An `after` timeout is an untimed self-timer armed on
  every re-entry and never cancelled, so timers accumulate and a stale one
  may fire late (an over-approximation: the BEAM resets the timeout on any
  message); the bounded checkers keep the depth modest because of it.
* Registered names are constant pids, fixed by `--pid` or derived from
  `name: __MODULE__` / `Process.register/2` (no registry, no registration
  races); monitor refs are dropped (no `demonitor`, `DOWN` matched on pid);
  timers cannot be cancelled; single node.

The equivalence theorems do not close any of these: `beh_eq_gen` shows the
hand model equals the generated model, not that either equals the BEAM. The
drivers are the only check in that direction, and they are property tests.

## 7. Round 2

Four builders worked in parallel on worktrees, writing into one decision
graph under node 219, and an integrator merged them in a fixed order
(proofs, fixtures, uniform output, features; nodes 276-289). What changed:

* **One output shape** (goal 222, decision 228). `to_lean.exs` always emits
  `EBehavior St Msg` over `Leanactors.Sys` with a `sig` record; the
  `effects` flag, `effects_in?` and every message-mode branch are gone.
  `Gen/Bank.lean` and `Gen/Lock.lean` changed shape (no crash clauses
  appeared: every cast/call tag has a covering clause); the other Gen files
  are byte-identical. The hand models keep `beh : Behavior` and prove
  `Gen.X.beh = lift beh` (node 244), so no lock or bank proof moved.
* **`receive ... after`, derived registration, `raise`** (goal 231,
  decisions 234/237/238) with `elixir/src/ttl.ex`, `Gen/Ttl.lean`
  (translated with no `--pid` flag), `Examples/Ttl.lean` (hand `beh`,
  `beh_eq_gen`, checker: the cache never holds 0, 17,206 configurations at
  depth 7/3, the store-0 mutant caught) and `elixir/ttl.exs`. The after
  timer's accumulation is the new approximation (node 265, section 6).
  Explicit `--pid` flags replace the derived map entirely (node 269).
* **Translator fixtures** (goal 221, decision 227). `elixir/test/` has 25
  fixtures with directives in their leading comment block, expected
  outputs, `run_fixtures.exs` (diff, stderr checks, `lake env lean` on the
  ok ones, `--regen`) and `regen_expected.sh`; `check.sh` runs them after
  the translation diff. Writing them found four translator bugs (node 251:
  the `.go` exitMsg placeholder, a redundant catch-all for single-module
  sources, `some (some p')` for a whole-state alias, a tuple-of-variables
  pattern not recognised as general), fixed in node 252.
* **Exhaustiveness** (nodes 281-287). After the merges two fixtures that
  split a `Bool` in a cast/call clause got a crash clause Lean rejected as
  redundant: the gap the fixtures builder had recorded at node 268, which
  message mode used to hide behind a warning. `insert_crashes` now decides
  coverage with a usefulness check over the rendered Lean patterns
  (`covered_tags`, `exhaustive?`: complete signatures for `Bool`, `Option`,
  `List` and the generated enums, opaque heads for literals and anything
  else, so it can only err towards an extra crash clause). The six Gen
  files did not change; a new fixture `enum_split.ex` shows an enum and a
  list split with no crash clause and no catch-all.
* **`Sys` proofs on `SysProps`** (goal 220, decision 249). Every theorem
  statement kept; `SupervisorProof.lean` 396 to 290 lines, `TaskProof.lean`
  394 to 313, `WatchdogProof.lean` 433 to 287, `SysProps.lean` 985 to 1,079
  (additive: `Effect.isolated`, `applyEffects_links_signals_of_isolated`,
  `deliver_of_get_none`, `downE_of_codec`, `downE_links`/`signals`,
  `timerE_links`/`signals`). The case split is by pid (section 4, node
  274); `SysPropsDemo.lean` states its three demonstrations as `example`s.
  One Lean gotcha: `case EXIT who r =>` after a bare `cases m` bound the
  names in the wrong order; `cases m with | EXIT who r => ... | _ => ...`
  is what the files use.

Counts after the round: 4,924 lines of hand-written Lean in 20 files, 288
generated lines in six, 275 theorems, no `sorry`, no `axiom`; the
translator is about 1,340 lines; `check.sh` runs six translations, 25
fixtures, `lake build` and six drivers.

## 8. What to try first

1. `./check.sh` from the repo root (with `export PATH="$HOME/.elan/bin:$PATH"`).
   It regenerates the six `Gen/` files and diffs them, runs the 25
   translator fixtures, runs `lake build` (which runs every `#eval
   explore`), greps for `sorry`, and runs the six drivers on the BEAM.
   First build takes a few minutes.
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
6. To extend it: a seventh `elixir/src/*.ex` within the subset listed in
   the header of `elixir/to_lean.exs`, two lines in `check.sh`, a hand
   model with `beh_eq_gen`, `checkInv` and `explore`, and only then the
   proof. A translator change starts with a fixture under
   `elixir/test/fixtures/`, then `elixir/test/regen_expected.sh` and a
   look at `git diff elixir/test/expected`.
