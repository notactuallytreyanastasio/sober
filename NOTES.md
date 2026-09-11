# leanactors: design notes

These notes are for someone who knows Elixir and Lean 4 but has not opened
this repository. They explain what was built, why it has the shape it has,
and what was learned along the way. The README is the reference; this is
the narrative. Node ids in parentheses refer to the decision graph exported
in `docs/graph-data.json` (127 nodes when these notes were written; the
workflow that merged the pieces described below added its own subtree
under node 138, the second round (section 7) its own under node 219,
the third (section 8) under node 300, the fourth (section 9) under
node 369 and the fifth (section 10) under node 436; types
goal/option/decision/action/outcome/observation), which was kept in real
time as the work was done. Line counts and spans in sections 2-4 were
re-measured after round 2 and the file totals after round 5; sections 7
to 10 list what each round changed.

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

### Sys (`Leanactors/Sys.lean`, about 355 lines)

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
signals, and a `kill` terminates its target whether or not it traps, its
links and monitors seeing `error` (round 3; `Reason.kill`,
`Reason.propagated`, and `signalE` matches the reason before the trap
flag). No recursion, every step is a plain function. `SysStep` has four
constructors (`run`, `signal`, `down`, `timer`), `SysReach.inv` is the
induction principle, and `runSys_sound` is the executable counterpart.

The conservativity theorem `runE_lift` says that on a system with no
links, signals, monitors, downs or timers, running the lifted message-only
behaviour is exactly the old `step`. The bank and lock results never had to
be touched when `Sys` arrived (node 88).

### SysProps (`Leanactors/SysProps.lean`, about 1,437 lines)

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
projections of `downE` and `timerE` (node 250). Round 3 added the kill
case (`signalE_cases` five-way, `signalE_stateOf`, `runE_cases` with
`reason.propagated`), the provenance lemmas `applyEffects_mem_signals_cases`
and `Effect.init?` / `applyEffects_stateOf_cases` /
`SysStep.stateOf_spawn_cases`, and `Sys.NoKillTo p` with its per-step
preservation (nodes 320-322). `Examples/SysPropsDemo.lean`
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
`Nat.le_trans` explicitly (node 160). Round 5 added the `timers` append
group (`runE_timers_append`, `signalE_timers`, `downE_timers`), hoisted
from the two timer-driven liveness files that had each written it.

### Fair (`Leanactors/Fair.lean`, about 1,600 lines)

Everything above is about `Reach`: what never happens. Round 4 added
what must happen. A run is `st : Nat → _` with the choice taken at each
time, `ch t : Option _`, where `none` is an idle step (the state repeats):
`CRun beh env` over `Config` with an environment relation, `SysRun beh
sig` over `Sys`. Weak fairness of a choice (`WeakFair c`: disabled
infinitely often or taken infinitely often) and environment fairness
(`EnvFair P e`: if `P` holds from some time on, an `e`-step eventually
happens) are the assumptions; `Eventually`/`Always`/`LeadsTo` the
vocabulary; `stable_until` and `rank_leads_to`, proved once over any
`ρ : Nat → α`, the workhorses, with per-layer wrappers whose hypotheses
need only hold on configurations reachable from `ρ.st 0`, so the safety
invariants plug in unchanged. `LeadsTo.rank_induction` is well-founded
leads-to over a `Nat` measure. Section 9 says why the idle step is there.
Round 5 added the open `Sys` layer, `SysRunE beh sig env` (a system
choice or one `env` step at each time, `Sys.Deliver` for the examples),
with `SysReachE`, `EnvFair`, the same four workhorses and `SysRun.toE`;
section 10 says why the task needed it.

## 3. The translator

`elixir/to_lean.exs` (about 1,990 lines, one module `ToLean`) reads a file
of `GenServer` modules and emits one Lean file per source into
`Leanactors/Gen/`. The invocation is fixed by `check.sh`, for example

```
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server
```

where `--pid Lock=server` says that the registered name `Lock` is the
constant pid `server` (0 in the generated file). Without any `--pid` flag
the names are derived from the source (`name: __MODULE__`,
`Process.register/2`; section 7), which is how `ttl.ex` is translated. The
generated files are committed, and `check.sh` regenerates all seven and
fails if any differs; it then runs the 37 translator fixtures under
`elixir/test/` (section 7).

### Conventions

* `@type msg` is a union of atoms and tagged tuples; each alternative is a
  `Msg` constructor. `@type call` alternatives become constructors with a
  leading `caller : Pid`; `@type reply` becomes the single constructor
  `Msg.reply`. All modules in one file share one `Msg` and one `St`.
  Optional `@type cast` and `@type info` unions declare a tag's kind
  directly (a cast/call tag with no clause crashes, an info tag with no
  clause is ignored; a tag in two of msg/cast/info/call or a clause of
  the wrong kind is an error); `msg` stays cast-or-info by handling
  callback (round 3).
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
* `{:noreply, e, {:continue, x}}` and `{:reply, r, e, {:continue, x}}`
  are inlined: the matching `handle_continue` body follows the clause's
  sends and reply, with its patterns bound to `x` and `e` (round 4,
  section 9). `{:reply, r, e, t}` arms the `:timeout` self-timer after
  the reply, `{:stop, reason, r, e}` replies and exits, `:hibernate` is
  no timeout.
* `%{K => V}` is the association list `List (K × V)` of `AssocList.lean`
  and the `Map.*` calls are its functions; a map pattern with literal
  keys is a variable plus guards, with a fresh value variable bound by a
  `match get?` around the body; a named union of atoms and tagged tuples
  (`@type reply :: :ok | {:error, err()} | ...`) is a generated inductive
  (round 5, section 10).

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
| `elixir/src/ttl.ex` | derived (`Process.register`) | `receive ... after` as the generation-counted self-timer `after_run g` (hidden `gen` state field, re-armed at every re-entry with `gen + 1`, stale generations consumed and ignored), `raise` in tail position as `.exit .error`, a raw process with an `Option Nat` state |
| `elixir/src/registry.ex` | derived (`name: __MODULE__`) | a `%{name() => pid()}` state as an association list, `Map.has_key?`/`put`/`fetch`/`delete`/`reject`, a tagged-union `@type reply`, `Process.monitor` of the caller of a `handle_call`, `@type cast`/`info` kinds, a client whose blocking call is followed by an `if` |

The generated files are 42 to 68 lines each; the sources are 55 to 85.

## 4. The proof recipe

Every example after the bank follows the same recipe, and the observation
at node 115 says so explicitly: bounded check, then a frame lemma, a
termination lemma, and one example-specific shape. The line counts below
are from the files at this commit.

**Bounded check first.** Each example file defines `checkInv` (a `Bool`
version of the invariant) and calls the shared `Sys.explore`
(`Leanactors/Explore.lean`, round 3; the lock and the TTL cache keep a
local one), which enumerates every interleaving of actor steps, signal
and DOWN deliveries, timer firings and environment stimulus up to a
depth, returning the number of configurations visited and the first
violating path if any. `#eval explore ...` runs at
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
assumption for liveness. Round 4 supplied that assumption and the
liveness proof: `LockLive.eventually_holds` (section 9), where the
re-enqueue is exactly what makes the index of the awaited `reply ok`
drop at every step of the blocked client.

**The GenServer timeout reset.** Node 124, seen while writing
`elixir/watchdog.exs`: "any message resets a GenServer timeout, including
`:sys.get_state` polls. The driver never saw the timeout until it stopped
polling." The driver now sleeps past the timeout instead of polling. In the
model timers are untimed, so a `:timeout` may fire even after a `:pong`
arrived and the watchdog may kill a healthy worker. The property (a dead
worker always has its restart in flight) does not care why the worker died,
so the over-approximation costs nothing. Liveness of the watchdog (a hung
worker is eventually replaced) needs the timer to actually fire, that
is, a fairness assumption on timers. `Fair.lean` (round 4) can state
that assumption (`WeakFair (.timer i)`) and round 5 proved it
(`WatchdogLive.worker_replaced`, section 10): the assumption is
`TimerFair 0 .timeout` (a pending `(0, timeout)` timer eventually fires),
derived from weak fairness of every timer index by a non-increasing
`findIdx` rank on the first matching timer, and no quiet mailbox is
needed, since the rank on the position of the first `timeout` in the
watchdog's mailbox absorbs any number of pongs ahead of it. The
over-approximation reappears as the theorem's strength: along a fair run
every worker the watchdog waits on is eventually killed and replaced,
hung or not.

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
emitted for every file (section 7). Round 3 closed the last syntactic
corner, a `@type msg` tag no clause mentions, by letting `@type cast` and
`@type info` declare the kind (section 8). Real time and multi-node
remain.

## 6. Known approximations and their direction

Over-approximations admit behaviours the BEAM does not have. A safety
property proven over the model then also holds on the BEAM (for the
modelled behaviours); liveness is where they hurt.

* Any scheduler, including unfair ones. `Reach` and `SysReach` quantify
  over all interleavings. Sound for safety; liveness needs fairness,
  which round 4 added as a separate layer of runs (`Fair.lean`, section
  9) without touching the safety theorems.
* The `Sys` layer's reachability is closed: `SysReach` has no
  environment step, so the supervisor, task, watchdog and TTL theorems
  are about the system's own steps from `init`, and the environment
  stimulus the checkers explore (`:crash`, `hang`, `put 0`) enters the
  proofs only through the start system (`SysReachEnv`, round 4). The
  lock's `ReachEnv`/`CRun` interleave environment ticks throughout, and
  since round 5 so does the task's live-worker liveness theorem
  (`SysRunE` with `Sys.Deliver`); the other `Sys` liveness theorems are
  still over closed runs.
* Untimed timers (decision at node 119). Any pending timer may fire at any
  step, in any order, regardless of messages that arrived since it was
  armed. The BEAM under-fires when the mailbox is busy.
* Environment stimulus at any time (`EnvStep` in the lock, the `ticks`
  budget in every `explore`).
* Re-enqueue deferral for blocking calls adds self-message steps the BEAM
  does not take (it uses a save queue). Extra steps, same reachable states
  for the counted messages.
* Exit reasons are `normal`, `error` and `kill` (round 3).
  `Process.exit(p, :kill)` is the untrappable kill it is on the BEAM: the
  target dies whatever it traps and its links and monitors see `error`
  (`:killed`). A remote `Process.exit(p, :normal)` is ignored by a
  non-trapping target and is an `EXIT` message to a trapping one. Any
  other reason is `error`, so a trapping process cannot tell `:shutdown`
  from `:boom`; that collapse is harmless for the properties proved so far
  (no handler inspects the reason). One remaining approximation: a process
  that exits *itself* with `:kill` (`exit(:kill)`, `{:stop, :kill, s}`)
  is reported to its links as `error`; on the BEAM such a link-propagated
  kill is trappable and a trapping link sees `{:EXIT, p, :kill}`, a
  non-trapping one dies with `:killed`. The model agrees on who dies and
  differs only in the reason atom a trapping link would see.

Under-approximations omit behaviours the BEAM has. A safety proof over the
model says nothing about the omitted paths.

* Closed message world: only `@type msg` alternatives exist. `:sys` messages,
  stray sends and typos are not modelled. A tag no callback of a module
  mentions is not classified and gets no crash arm (node 246) unless it
  is declared under `@type cast` or `@type info` (round 3).
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
  call deferral). An `after` timeout is an untimed self-timer with a
  generation: the state carries `gen`, every re-entry arms `gen + 1`, and
  only the current generation runs the after body, so a processed message
  cancels the timeout as on the BEAM (round 3); what remains approximate
  is timing (the live timer may fire at any step) and that a skipped
  message re-arms instead of keeping the old timeout. Stale entries stay
  in `timers` until they fire and are ignored. `gen` is a reserved name
  in such a module and a blocking call inside the loop is rejected.
* Registered names are constant pids, fixed by `--pid` or derived from
  `name: __MODULE__` / `Process.register/2` (no registry, no registration
  races; the round 5 registry example is an ordinary GenServer holding a
  map, itself at a constant pid); monitor refs are dropped (no
  `demonitor`, `DOWN` matched on pid); timers cannot be cancelled; single
  node. Maps have one `K => V` pair per type and literal keys in
  patterns; `Map.merge`, `Map.update` and `Enum` over a map are outside
  the subset.

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

## 8. Round 3

Four builders again, each on a worktree and a `wf3/*` branch, writing
into the graph under node 300; the integrator merged explore, kill,
kinds and after in that order with `--no-ff` (nodes 347-360). No merge
had a textual conflict, and the six regenerated `Gen/` files and the
regenerated fixture expectations were byte-identical to the merge
result; the only hand fix was in `TtlProof.lean`, whose `rcases` on
`signalE_cases` and `runE_cases` had been written against the pre-kill
shapes (one more alternative, `reason` becomes `_`). What changed:

* **Exact `:kill` and remote `:normal`** (goal 303, decision 320).
  `Reason` gains `kill`; `Reason.propagated` sends `kill` to `error`;
  `signalE` matches the reason before consulting `traps` (kill: terminate
  the live target with `error` whatever it traps; normal: `EXIT` message
  if trapping, else no-op; error: message if trapping, else terminate);
  `runE` reports a self-exit as `reason.propagated`. The translator's only
  change is `reason_str(:kill) -> .kill`; `Gen/Watchdog.lean` now reads
  `.signal w .kill`. The decision was to keep `Sys.terminate` general and
  normalise at the callers (option 319 over 318) and to prove
  kill-freedom as a separate `Sys.NoKillTo 0` conjunct beside `Inv`
  rather than an `Inv` field, which would have re-threaded every `Grows`
  call: `SupervisorProof` adds `beh_no_signal`, `WatchdogProof` adds
  `ChildNe` (no watchdog at any pid names 0 as its worker, carried through
  the new `SysStep.stateOf_spawn_cases`). Every theorem statement is
  unchanged; `SysProps.lean` 1,079 to 1,373 lines, `SupervisorProof` 290
  to 315, `WatchdogProof` 287 to 361, `TaskProof` 313. The checkers
  enumerate `[.normal, .error, .kill]` and no count moved (a kill to a
  non-trapping worker was already a termination). Fixtures
  `process_exit.ex` (now `.signal p .kill` and `.signal p .normal`) and
  `stop_kill.ex` (`.exit .kill`, `:shutdown` as `error`). The self-kill
  reason atom is the one approximation kept (section 6).
* **Exact `receive ... after` and the Ttl proof** (goal 304, decision
  326). `to_lean.exs` gives an after-loop's state a hidden trailing
  `gen : Nat`, makes `after_<loop>` carry a generation, bumps and re-arms
  on every re-entry (loop tail, defer clause, failed guard, after body),
  starts a spawned child at generation 0, and renders the after clause as
  `if gen' = gen then <body> else (<state>, [])`. Scheme A (state `gen` =
  generation of the live timer, node 324) was chosen over an off-by-one
  variant (node 325). `Gen/Ttl.lean` and `Examples/Ttl.lean` changed
  accordingly (16,723 configurations at depth 7/3, the store-0 mutant
  caught in 29 after two live expiries and a `put 0`); the other five Gen
  files are byte-identical; fixture `receive_after.ex` covers the guard,
  the exit, the defer clause, the after arm and the spawn site. The old
  accumulation approximation (a stale expiry firing after later messages)
  is gone; timers remain untimed and a skipped message re-arms where the
  BEAM keeps the old timeout (node 344). `TtlProof.lean` (266 lines, 17
  theorems) states `Inv` for every pid (no cache holds `some 0`, no
  mailbox or timer carries `value (some 0)`), proves `Inv.run` clause by
  clause from the concrete effect lists and the rest from
  `signalE_cases`/`downE_cases`/`timerE_cases`, and ends in
  `cache_never_zero`, `no_zero_in_flight` and `cache_never_zero_gen`. One
  Lean note: with `export Leanactors.Gen.Ttl (St)` the spelling `St.cache
  v g` in a `have` does not resolve; `(.cache v g : St)` does. All six
  examples are now proved.
* **Declared message kinds** (goal 302, decision 307). Optional `@type
  cast` and `@type info` unions; `classify/2` seeds `ctx.kinds` from the
  declarations (call, cast, info) before the clause scan, so an
  uncovered cast or call tag gets a crash clause through the existing
  `insert_crashes` path and an uncovered info tag is ignored via the
  catch-all; `@type msg` keeps its cast-or-info-by-callback semantics and
  may be omitted when another union is declared. The alternative of
  defaulting every unclassified `msg` tag to cast (node 306, the node 246
  suggestion) was rejected as guessing. Errors: a tag under two of
  msg/cast/info/call, a clause of the wrong declared kind, a msg tag
  handled by two kinds, `@type cast`/`call` in a raw process. The six Gen
  files are byte-identical; fixtures `kind_cast_uncovered.ex`,
  `kind_info_uncovered.ex`, `error_kind_conflict.ex`,
  `error_kind_mismatch.ex`. Constructor order per module is msg, cast,
  info, `after_<loop>`, call, reply (node 329).
* **Generic explorer** (goal 301, decision 311). `Leanactors/Explore.lean`
  in namespace `Leanactors.Sys`: `livePids`, `exploreWith` (`envMsgs :
  Pid -> List μ`) and `explore` (one list for every live pid), steps in
  the order runs, signal, down, timers, env with labels `run p`,
  `signal`, `down`, `timer i`, `env <repr m> -> p`. Supervisor, Task and
  Watchdog call it with byte-identical `#eval` output (the watchdog's
  env label changed from the hand-written `env hang` to the `repr`, but
  no recorded witness has an env step). Ttl and Lock keep local
  explorers: the current namespace beats the opened `Sys` one, so no
  ambiguity (node 315). (Ttl moved to `exploreWith` in round 4.)

Counts after the round: 5,610 lines of hand-written Lean in 20 files
under `Leanactors/`, 288 generated lines in six, 322 theorems, no
`sorry`, no `axiom`; the translator is about 1,445 lines; `check.sh` runs
six translations, 31 fixtures (25 ok, 6 error), `lake build` and six
drivers.

## 9. Round 4

Four builders on `wf4/*` branches, writing into the graph under node
369: the fairness framework (goal 371) first, the two liveness proofs
(goals 387, 388) branched from it, and the translator piece (goal 370)
independent. The integrator (goal 408) merged translator, fair, sup-live
and lock-live in that order with `--no-ff` (nodes 412-415). No merge had
a textual conflict, the six regenerated `Gen/` files and the regenerated
fixture expectations were byte-identical to the merge result, and
`check.sh` was green on it. Two things were nevertheless wrong with the
merged result, neither visible from inside any one piece; both were
found while checking the theorem statements for this section and fixed
on `main` (nodes 417-426):

* **Runs could not idle.** `CRun` and `SysRun` took a labelled step at
  every time, so a closed system in which nothing is enabled had no
  infinite run at all. From `Supervisor.init` the only step is `run 0`
  on `:start`, after which nothing is enabled: `restart_eventually`
  quantified over an empty set of runs and was vacuously true (node
  417). A run now takes a labelled step or an idle step (`ch t = none`,
  the state repeats: `CStepI`/`SysStepI`), weak fairness compares
  `ch t = some c`, and every wrapper kept its statement, so both liveness
  files compiled unchanged. `CRun.idle`/`SysRun.idle` are the constant
  runs, the witness that a run exists from every configuration. This is
  the usual stuttering convention and should have been in the framework
  from the start; the lesson for a framework builder is to prove, in the
  file, that the objects the theorems quantify over exist.
* **The supervisor's premise was unreachable.** A `SysRun` is closed,
  and in a closed run from `init` nobody sends the worker `:crash`, so
  "the current child is dead at `t`" never held along any run from
  `init` (node 424). The theorem is now stated from any `Good` system
  (`Inv` and `NoKillTo 0`, preserved by every step and by every
  environment delivery, `Good.deliver` via `Inv.grows` and
  `grows_deliver`), with `restart_eventually_env` for any system the
  environment can drive the supervisor to (`SysReachEnv`, new in
  `Fair.lean`: `SysReach` plus arbitrary deliveries),
  `restart_eventually_init` as the vacuous `init` form, and
  `dead_child_reachable` as the three-step witness (run 0, deliver
  `:crash` to 1, run 1, by `rfl`). The same closedness has always been
  true of the `Sys` safety theorems: `restart_in_flight` from `init`
  never meets a dead child either; the checkers explore the environment,
  the proofs do not (section 6). Environment steps inside `SysRun` are
  the obvious next step and would let `restart_eventually` cover runs in
  which the environment keeps sending; the stage lemmas already treat
  every other actor's step as "only appends to the supervisor's
  mailbox", which is what a delivery does.

What the round added:

* **Fairness framework** (goal 371, decision 374). A generic temporal
  core over `ρ : Nat → α` (`Eventually`, `Always`, `LeadsTo` with
  `trans`/`mono`/`or`/`rank_induction`; `WeakFairOn en tk` in the
  disjunction form, with `WeakFairOn.iff` for the enabled-from-`t`-on
  form; `stable_until`, `stable_until_leadsTo`, `rank_leads_to`) proved
  once and instantiated for both layers (`CRun` with `CChoice`/`CStepL`/
  `ReachE`/`CEnabled`/`WeakFair`/`EnvFair`, `SysRun` with `SysStepL`/
  `SysEnabled`/`WeakFair`), rather than one copy per layer (option 373
  rejected: the environment-fairness case would have been a third copy).
  The wrappers guard their hypotheses by reachability from `ρ.st 0`, so
  `Inv.step`/`Inv.env` and the `SysReach.inv` facts apply without
  folding `Inv` into the predicate. `FairDemo` (a light that any message
  switches on) is the sanity check: `off` leads to `on` under
  `WeakFair (.run 0)` and an `EnvFair` delivering to pid 0.
* **Supervisor liveness** (goal 388, decision 393). Two `rank_leads_to`
  stages, on the position of the pending `(0, c, _)` signal in the FIFO
  signal queue and on the position of `EXIT c _` in the supervisor's
  mailbox, through `SysRun.rank_leads_to_of_step`, whose single
  hypothesis is one labelled-step lemma returning `Q b ∨ (P b ∧ f b ≤ f
  a ∧ (ch = c → f b < f a))`. The wrapper proves `LeadsTo (P ∧ ¬Q) Q`
  internally because `rank_leads_to`'s hypotheses quantify over `P b`
  even when `Q b` also holds (the `EXIT` delivered while a second
  `(0, c, _)` signal is still queued), which would otherwise have needed
  a proof that signals to `c` are unique (node 402). The generic
  mailbox/signal append lemmas (`mboxOf_runE_append`,
  `runE_signals_append`, `mboxOf_downE_append`, `mboxOf_timerE_append`)
  and the two `findIdx` facts live in the file in namespaces
  `Leanactors`/`Leanactors.Sys` and are candidates for `SysProps.lean`.
  Stronger than asked: no `WeakFair .down`, and `NoKillTo 0` derived.
* **Lock liveness** (goal 387, decision 397). A staged `LeadsTo` chain
  with one measure family, `idxOf c q m` (the index of the first `m` in
  `q`'s mailbox; `Has.append`/`Has.pop` are the two mailbox lemmas),
  instead of one global measure (option 395 rejected: the stages need
  different fair choices, server run, holder tick, holder run, `x` run).
  The queued phase is `LeadsTo.rank_induction` on the FCFS rank, and per
  rank a four-lemma chain moves the holder's token (grant in flight,
  holding, ticked, release in flight) until the handover, where
  `Step.rank_step` from `LockFcfs` says the rank drops by one or `x` is
  granted. Fairness is exactly weak fairness of every actor's `run` plus
  the holder-tick `EnvFair`; `Inv (ρ.st 0)` is the only fact used from
  `initCfg n`. Nothing in `LockProof`, `LockFcfs` or `Fair` changed.
* **Translator** (goal 370, decision 378). `handle_continue` is inlined
  at the Elixir AST level (option 376, a self-message, rejected: on the
  BEAM the continue runs before any queued message), reply-with-timeout
  and stop-with-reply are new body tails, `:hibernate` is a no-op, and
  `@type continue` is accepted and ignored. The exit-reason piece needed
  no change (`reason_str` already rendered `:normal`/`:kill`; node 389),
  only a fixture. `Ttl.lean` moved to `Sys.exploreWith` with per-pid
  environment messages; the count went from 16,723 to 16,093 because the
  local explorer had counted no-op deliveries to the dead cache (node
  380, verified by restricting the old explorer to live pids). Fixtures
  `continue.ex`, `error_continue_deep.ex`, `reply_timeout.ex`,
  `stop_reply.ex`; `stop_kill.ex` gains a GenServer `exit(:kill)`.

Lean notes from the round (nodes 382, 403, 407): `cases` naming on the
labelled inductives `CStepL`/`SysStepL` is positional over *all*
constructor fields (`| run _ p s m rest h`), whereas for `Step`/`SysStep`
the first field is skipped; `obtain ⟨rfl, rfl⟩` on `q = 0 ∧ src = c`
substitutes the theorem's `c` away (use `subst q; subst src`);
`fun _ h => nomatch h, ?_` inside `⟨…⟩` parses the comma as a second
`nomatch` discriminant; `Msg.EXIT` does not resolve through the `export`
alias (`(.EXIT c r : Msg)` does); dot-notation with a leading explicit
argument (`hh.srv hi`) must be parenthesised as an argument; a local
config named `a` shadows the counter `a` (`unfold Lock.a`); lemmas meant
for dot-notation on library types from inside `Examples.Lock` are
declared `_root_.Leanactors.X.y`; `subst` with `p = server` replaces
`p`. And one about the graph itself: with four agents writing
concurrently, capture the id `deciduous add` prints rather than assuming
`N+1` (two wrong edges were made and unlinked).

Counts after the round: 8,411 lines of hand-written Lean in 23 files
under `Leanactors/` (`Fair.lean` 1,145, `SupervisorLive.lean` 631,
`LockLive.lean` 1,037), 288 generated lines in six, 487 theorems, no
`sorry`, no `axiom`; the translator is about 1,680 lines; `check.sh`
runs six translations, 35 fixtures (28 ok, 7 error), `lake build` and
six drivers.

## 10. Round 5

Five builders on `wf5/*` branches, writing into the graph under node
436: the three remaining liveness proofs (task, goal 440; watchdog, goal
438; ttl, goal 441), differential fuzzing of the interpreters against
the BEAM (goal 442) and Elixir maps in the translator with a registry
example (goal 437). The integrator (goal 501) merged maps, diff-fuzz,
task-live, watchdog-live and ttl-live in that order with `--no-ff`.
Two textual conflicts (`check.sh`: the registry driver line against the
fuzz stage; `Leanactors.lean`: the registry imports against the
`TtlLive` import), both trivial. The real overlap was invisible to git:
`WatchdogLive.lean` and `TtlLive.lean` had each written the same generic
lemmas under the same names in namespace `Leanactors`
(`List.mem_eraseIdx_of_ne`, `List.findIdx_eraseIdx_le`, the `Sys.timers`
append group up to `runE_timers_append`, `signalE_timers`,
`downE_timers`), and Lean refuses to import two modules that declare one
constant. The fix (decision 504) hoists one copy: the timers group into
`SysProps.lean`, the erase/`findIdx` list facts into `Fair.lean` (the
ttl builder's orientation of the `≠`, so the watchdog's one call takes
`Ne.symm`); the watchdog's `findIdx_eraseIdx_le` was a different
statement (by index, not by element) and is renamed
`findIdx_eraseIdx_le_of_ne`. No theorem statement changed. The seven
regenerated `Gen/` files and the regenerated fixture expectations were
byte-identical to the merge result and `check.sh` was green on the
first run after the hoist. What the round added:

* **Task liveness** (goal 440, decision 457). The honest theorem is
  conditional by nature: a live worker acts only on `compute` or
  `crash`, which only the environment sends, and a closed `SysRun` from
  a live worker may idle forever. The builder therefore added the open
  `Sys` layer to `Fair.lean` first (`SysRunE`, `SysReachE`, `Sys.Deliver`,
  `EnvFair`, the four workhorses, `SysRun.toE`; purely additive, 398
  lines) and stated `job_eventually_settles` over it with `WeakFair (.run
  w)` and `EnvFair (Alive w) (Kick w)`: if the caller keeps waiting on a
  live monitored `w`, the environment eventually delivers `compute` or
  `crash` to `w`, and nothing else is assumed of it. The dead-worker
  half (`job_eventually_settles_dead`) needs only `WeakFair .down` and
  `.run 0` and is stated on a closed run through `SysRun.toE`. Four
  `LeadsTo` stages, ranks = queue positions (`findIdx`) in `w`'s mailbox,
  `downs`, the caller's mailbox. `Good` = `Inv` + `Fresh` + `Shape`.
  Witnesses `deadRun_witness` (settles at time 2) and `liveRun_witness`
  (all hypotheses including `EnvFair`, settles at time 5). The draft was
  cut off mid-way by a usage limit and resumed with its 16 elaboration
  errors fixed and no statement changed (node 472 lists them: dot-notation
  on an ascribed anonymous constructor infers the unfolded `Exists`; an
  `armed_deliver` with an implicit target unifies wrongly under `rfl`;
  witness lemmas must be stated on `ρ.st (t+k)`, not on the underlying
  sequence, for `rw` to find them).
* **Watchdog liveness** (goal 438, decision 455). `restart_eventually`
  as for the supervisor (new invariants `Armed` and `ChildLt`, and
  `dog_run_cases` because a non-restart `run 0` may ping, re-arm or
  queue the kill), and the timer-driven `worker_replaced`. The design
  point was the fairness form: `WeakFair (.timer i)` for a fixed `i` is
  the wrong assumption because indices shift when an earlier timer
  fires (option 454), so `SysRun.TimerFair to m` is a derived notion
  (option 453): the `findIdx` of the first `(to, m)` timer never
  increases, so it stabilises, and weak fairness of that index fires it
  (`timerFair_of_weakFair_timers`). `hung_worker_replaced` states the
  requested hypotheses (worker alive and hung, fair `run w`) and uses
  neither, because the kill is untrappable (node 497); that is the
  untimed-timer over-approximation stated as a theorem. The fair witness
  run is built by the new generic `SysRun.exists_of_inv` from a
  five-phase invariant `Cyc` rather than written state by state. Generic
  pieces still living in the file: `TimerFair`, `stable_until_timer`,
  `exists_of_inv`, `exists_stable_of_nonincreasing`.
* **Ttl liveness** (goal 441, decision 477). The safety file said the
  cache never holds 0; the liveness file says a held value does not
  stay: the timer of the current generation is always in flight
  (`Armed`, half of `Good`; the safety invariant `Inv` is not needed at
  all), it fires under fairness of the oldest timer (rank = its position
  in `timers`), then `run 0` pops it (rank = its position in the mailbox,
  stale timers ahead are consumed with the state unchanged), and
  `exists_last` plus `cache_run_cases` classify the step that leaves the
  generation: cleared, re-armed by a message, or dead. The honesty point
  (node 478): the corollary "if the generation never changes then the
  value clears" is not stated, because the after body itself moves to
  `g + 1`, so its premise is unsatisfiable along any fair run;
  `value_eventually_expires` assumes "no message processed at `g` and
  the cache does not die" instead, witnessed by `wit_quiet`. Fairness
  form A (`WeakFair (.timer 0)`, the oldest pending timer) was kept over
  the watchdog's `TimerFair` (options 475/476), with the `∀ i` corollary
  `gen_advances_or_clears_timers` so the two pieces unify by one
  instantiation.
* **Differential fuzzing** (goal 442, decision 449): a `replay`
  executable over `run`/`runSys` (`Leanactors/Replay.lean`, a lakefile
  `lean_exe` and default target) and `elixir/fuzz.exs`. The BEAM cannot
  be told which process to run next, so a script is only comparable if
  every phase has one outcome under any scheduling (option 448 over
  driving the BEAM scheduler with `:sys.suspend`/`resume`, option 447);
  the fuzzer's header documents each phase shape and why, and the lock
  needed a protocol simulation in the generator to expand a tick into
  the Lean cascade plus the exact server receives (decision 468). Three
  things surfaced while building it (nodes 483, 484): the ttl comparison
  must treat stale timers as Lean-only (the model over-approximates the
  BEAM's cancelled timeouts, section 6) and a stalled driver as a
  possible spurious expiry (retried, counted, zero so far); a lock client
  blocked in a call cannot answer a system message, so its phase is read
  off the server's queue; and killing a client linked to the driver
  killed the driver, so the twin unlinks first. Sensitivity was checked
  with BEAM mutants that are not committed (withdraw `n < b`, a `get`
  ignored for one value, LIFO grant), each caught in the first runs
  (node 459). `check.sh` runs 200 scripts in about 14 s.
* **Maps and the registry** (goal 437, decision 464). The choice was
  association lists `List (K × V)` with plain definitions and lemmas
  (option 462) over `Std.HashMap` or functions `K → Option V` (option
  463): a structural list keeps `beh_eq_gen` an `rfl`/`simp` matter and
  the checkers executable, and the lemmas hold for any list, so
  uniqueness never has to be carried. The translator renders `%{K => V}`
  types, `%{}` and pair literals, every `Map.*` call the registry needs,
  map patterns with literal keys (a variable plus guards, fresh value
  variables bound by `match get?` with guard-style fallthrough, an
  optional `= m` alias), and named tagged unions as generated
  inductives. Four translator limits found by the example (node 493):
  the reply is one type per file, so lookup answers `{:found, pid} |
  :not_found` rather than `pid | nil`; message tags are global across
  the modules of a file, so the client's message is `{:claim, name()}`;
  a map pattern's whole map is unreachable without the alias; `from` is
  a Lean keyword. Two more fixes fell out: `bare?`/`general?` must treat
  a map pattern as a variable or Lean rejects the fallback clause as
  redundant, and an `if`/`case` may follow a blocking call.
  `Examples/Registry.lean` has the hand model, `beh_eq_gen`, `checkInv`
  on 19,677 configurations, the no-monitor mutant and two run-case
  lemmas; the invariant proof is deferred.

Lean notes from the round (nodes 471, 472, 487, 499): an exported
constructor alias (`Msg.after_run` through `export Gen.Ttl (Msg)`,
`Msg.compute` through the task's) does not resolve, write the qualified
name; `nomatch h, x, y` parses `x y` as extra discriminants, so
parenthesise inside anonymous constructors; inside `theorem Good.init`
the bare name `init` is `Good.init`; an `rcases rfl` after `subst`
re-introduces older hypotheses, so name intermediate equations
distinctly; `if ph = 4 then k+1 else k` stays unreduced in `refine`
goals and is discharged with explicit `show` forms; `by_contra` without
Mathlib is `Classical.byContradiction`; a `cache_run_cases`-style lemma
with implicit `v g` needs `(v := v) (g := g)` before a `by` block. And
one for the integrator: two builders who never see each other's files
will write the same generic lemma, and Lean only notices at the
top-level import; grep the generic namespaces of every liveness file
before merging.

Counts after the round: 13,130 lines of hand-written Lean in 29 files
under `Leanactors/` (`Fair.lean` 1,599, `SysProps.lean` 1,437,
`TaskLive.lean` 1,064, `WatchdogLive.lean` 1,516, `TtlLive.lean` 949,
`AssocList.lean` 200, `Registry.lean` 160, `Replay.lean` 312 of
executable code), 356 generated lines in seven, 724 theorems, no
`sorry`, no `axiom`; the translator is about 1,990 lines; `check.sh`
runs seven translations, 37 fixtures (29 ok, 8 error), `lake build`
(proofs, checkers and the `replay` binary), seven drivers and 200 fuzz
scripts.

## 11. What to try first

1. `./check.sh` from the repo root (with `export PATH="$HOME/.elan/bin:$PATH"`).
   It regenerates the seven `Gen/` files and diffs them, runs the 37
   translator fixtures, runs `lake build` (which runs every `#eval
   explore` and builds the `replay` binary), greps for `sorry`, runs the
   seven drivers on the BEAM, and fuzzes the interpreters against the
   BEAM with 200 seeded scripts. First build takes a few minutes.
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
   81, 96, 97, 104, 115, 124, 127, and 417 and 424 for round 4) are the
   honest record, including the predictions that turned out wrong; for
   round 5 add 478 (why the ttl corollary is not stated), 484 (what the
   fuzzer may not compare and why), 493 (translator limits the registry
   found) and 497 (why the watchdog theorem needs nothing of the worker).
6. Read `Leanactors/Fair.lean`'s header, then `FairDemo` at its end, then
   `SupervisorLive.restart_eventually`: the liveness recipe is two
   `rank_leads_to` stages, and the file is short enough to read whole.
   `TtlLive.lean` is the next shortest liveness file and adds a timer.
7. To extend it: an eighth `elixir/src/*.ex` within the subset listed in
   the header of `elixir/to_lean.exs`, two lines in `check.sh`, a hand
   model with `beh_eq_gen`, `checkInv` and `explore`, and only then the
   proof. A translator change starts with a fixture under
   `elixir/test/fixtures/`, then `elixir/test/regen_expected.sh` and a
   look at `git diff elixir/test/expected`.
