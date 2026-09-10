# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib. This file is the
reference; `NOTES.md` is the narrative (what was built, why, what was
learned).

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Sys.lean` | Spawn, links, monitors, exits, timers, remote exit signals: effects, fresh-pid counter, link and monitor lists, asynchronous exit signals and DOWN notifications, untimed timers; `runE_lift` shows message-only behaviours are unchanged |
| `Leanactors/SysProps.lean` | Reusable `Sys` metatheory: `Grows`/`Frame` relations, `applyEffects` projections, `terminate` lemmas, `runE`/`signalE`/`downE`/`timerE` case and frame lemmas, `SysStep.stateOf_cases`, the `Fresh` predicate |
| `Leanactors/Examples/SysPropsDemo.lean` | The supervisor's timer, DOWN and no-exit-worker cases re-proved in one line each from `SysProps` |
| `Leanactors/Examples/Supervisor.lean` | One-for-one supervisor translated from `elixir/src/supervisor.ex`; bounded checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/SupervisorProof.lean` | The supervisor never dies and a missing child always has its restart in flight |
| `Leanactors/Examples/Task.lean` | Async task translated from `elixir/src/task.ex`: caller spawns and monitors a worker; checker; the no-monitor mutant |
| `Leanactors/Examples/TaskProof.lean` | A pending job is never lost: the reply or the DOWN is always on its way |
| `Leanactors/Examples/Watchdog.lean` | Watchdog translated from `elixir/src/watchdog.ex`: GenServer timeout, `Process.exit/2`, restart on EXIT; checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/WatchdogProof.lean` | The watchdog never dies and a dead worker always has its restart in flight |
| `Leanactors/Examples/Bank.lean` | Per-actor invariant: a bank's balance never goes negative under any scheduler |
| `Leanactors/Examples/Lock.lean` | Cross-actor invariant: lock server + clients blocking in `GenServer.call`, token invariant, bounded model checker |
| `Leanactors/Examples/LockProof.lean` | The invariant is inductive; `mutex_forever` and `progress_forever` under any scheduler and any environment ticks |
| `Leanactors/Examples/LockFcfs.lean` | Bounded waiting: rank drops by exactly one per handover while queued; `fcfs` in reachable configurations |
| `Leanactors/Examples/LockMutants.lean` | Three protocol bugs: two caught with witness traces, one shown unreachable |
| `Leanactors/Gen/*.lean` | Generated from `elixir/src/*.ex` by the translator; do not edit |
| `elixir/src/*.ex` | The Elixir source of truth (bank, lock, supervisor, task, watchdog): executed on the BEAM and translated to Lean |
| `elixir/to_lean.exs` | The translator: `@type`-directed, small subset, unverified |
| `elixir/bank.exs` | Driver: casts plus two clients blocking in `GenServer.call`; checks the trace matches Lean |
| `elixir/lock.exs` | Driver: clients block in `GenServer.call` under chaos ticks; event log checked for overlapping critical sections |
| `elixir/supervisor.exs` | Driver: crashes the worker on the BEAM and checks the supervisor survived and restarted it |
| `elixir/task.exs` | Driver: one job completes, one worker crashes; the caller clears both |
| `elixir/watchdog.exs` | Driver: hangs the worker, lets the timeout kill it, checks the replacement is running |
| `NOTES.md` | Design narrative: the thesis, the layers, the translator, the proof recipe, findings, approximations and their direction |

## Pipeline: Elixir source to Lean theorem

```
elixir/src/lock.ex          ordinary GenServer modules with @type msg / @type state
      │
      ├── elixir/lock.exs     runs them on the BEAM under chaos ticks (property test)
      │
      └── elixir/to_lean.exs  reads the @types, emits Leanactors/Gen/Lock.lean:
                              inductive Msg / St / Phase and `def beh : Behavior St Msg`
                                    │
                                    ▼
Leanactors/Examples/Lock.lean       `theorem beh_eq_gen : Gen.Lock.beh = beh` (funext + cases + rfl)
Leanactors/Examples/LockProof.lean  `Inv.step`, `mutex_forever` about `beh`
```

The `@type` declarations are the type oracle for the translation. They
decide when a pattern variable at a `pid() | nil` position needs `some`,
when `nil` is `none`, that `[pid()]` is `List Pid`, that an atom union is an
enum, and how the non-linear pattern `{:release, p}, {p, [n | rest]}`
becomes a Lean pattern plus an equality guard. Nothing in the translator
inspects values; every decision is type-directed. That is the division of
labour the original question asked about: Elixir's set-theoretic types fix
the shapes, Lean proves the interleavings.

**Process effects.** When a file uses `Process.flag(:trap_exit, true)`,
`{:ok, pid} = GenServer.start_link(Mod, arg)`, `{:stop, reason, state}` or
`exit/1`, the translator switches to effects mode: it emits an `EBehavior`
whose clauses bind `fresh`, turns `start_link` into `spawnLink` with the
child's initial state (see below), binds the
pid variable to `fresh`, maps any non-`:normal` reason to `error`, types
`{:EXIT, pid(), term()}` as `EXIT (Pid) (Reason)`, and generates the
`Signals` record from which modules trap. Files without effects keep
producing a plain `Behavior`, byte for byte as before.

**Monitors.** `{:ok, pid} = GenServer.start(Mod, arg)` becomes `spawn`,
`Process.monitor(pid)` becomes `monitor`, and `{:DOWN, ref, :process, pid,
reason}` is typed `DOWN (Pid) (Reason)` with the `ref` and `:process` atoms
dropped. Termination queues one DOWN per watcher; a separate step delivers
it as a message. The task example's invariant has four disjuncts (alive
and monitored, DOWN queued, reply in mailbox, DOWN in mailbox) and the
mutant that forgets `Process.monitor` loses the job at the crash.

**Timers and remote exits.** `{:noreply, state, t}` arms a self-timer for
`:timeout`, `Process.send_after(p, m, t)` arms a timer for `m` at `p`, and
`Process.exit(p, reason)` queues an exit signal to `p`. Timers are untimed:
any pending timer may fire at any step, so a GenServer timeout may fire in
the model even though a message arrived first. That over-approximates the
BEAM, which is the sound direction for safety. The watchdog example may
therefore kill a healthy worker, and its property does not care why a
worker died. One thing the untimed model hides: on the BEAM *any* message
resets a GenServer timeout, including `:sys.get_state` polls, which is why
the driver sleeps instead of polling.

**Synchronous calls.** `handle_call/3` is supported on both sides. On the
server, `@type call` alternatives become message constructors with a leading
`caller : Pid`, and `{:reply, r, s}` sends `reply r` to the caller. On the
client, a blocking `v = GenServer.call(Mod, m)` splits the clause: the part
before it runs and sends the request, the actor enters a generated
`<mod>_await<i>` state carrying whatever the rest of the body needs, a
second clause resumes on `reply v`, and any other message arriving in the
await state is re-enqueued to self. That re-enqueue is the standard encoding
of selective receive in a FIFO mailbox model and keeps the core untouched.
`Bank.deferred` in the Lean example shows a tick arriving mid-call being
processed after the call, not lost. Awaits nest: `Bank.audited` makes two
calls in one handler and the second await state carries the first result.
The lock uses this for real: clients block in `GenServer.call(Lock, :acquire)`,
the server replies immediately or queues the caller and answers later with
`GenServer.reply/2`, and the mutual-exclusion and deadlock-freedom proofs go
through against that translation with the await state playing `waiting`.

**Initial state.** `def init(p), do: {:ok, e}` (or the block form whose
other statements are all `Process.flag(:trap_exit, true)`) is read as a
pure state expression of its parameter. At `{:ok, pid} =
GenServer.start[_link](Mod, arg)` the child is spawned in `e` with `p`
bound to `arg`, positionally when both are tuples, and rendered in the
parent's environment by the same type-directed `state_expr` as any other
state. A module without `init/1` keeps the `use GenServer` default, the
identity, so the older sources translate byte for byte. `task.ex` uses it:
`Worker.init(parent)` returns `{:ok, {parent, 0}}` and the caller spawns
`GenServer.start(Worker, self())`.

**Unhandled messages.** On the BEAM an unmatched `handle_cast` or
`handle_call` raises `FunctionClauseError` and the process exits with an
error reason; an unmatched `handle_info` is ignored. In effects mode the
translator classifies every message tag by the callback that handles it
and emits, for each cast or call tag with no clause whose Lean pattern is
total (every message argument and state field a plain variable), a crash
clause `| _, _, .mod s_0 .., .tag _ .. => (state, [.exit .error])`; a
guarded cast/call clause whose guard fails with nothing to fall through to
crashes the same way. Totality is judged on the rendered Lean pattern, not
the Elixir one, because a pid-narrowed variable renders as `(some w)`.
Clauses are emitted per module with `handle_info` clauses after the
cast/call clauses and the crash clauses, so an info catch-all cannot
shadow a crash. The watchdog example found a real bug this way: with
`:pong` handled only while a pong is expected, a late pong after a timeout
crashed the watchdog after 742 explored configurations; the fix is one
`handle_cast(:pong, s)` ignore clause. In message mode (plain `Behavior`,
no exit effect) an uncovered cast or call tag only produces a warning on
stderr and stays modelled as ignored.

**Raw processes and selective receive.** A module whose body is exactly
one `def run(state) do receive do ... end end` is a raw process, not a
GenServer. Each receive arm is translated as an info clause with the
parameter as the state pattern; a body ending in `run(e)` continues with
state `e`, `exit(r)` exits, and any other last expression means the loop
returns (`exit :normal`). If the receive has no catch-all arm, a defer
clause `| me, _, .mod s_0 .., m => (.mod s_0 .., [.send me m])` is added
after the module's last clause and re-enqueues any other message to self;
a receive arm whose guard fails re-enqueues the same way. That is the
BEAM's selective receive (the message stays in the mailbox) in the same
encoding the call-reply await states use. `pid = spawn(Mod, :run, [a])`,
`spawn_link` and `{pid, _ref} = spawn_monitor(Mod, :run, [a])` map to
`spawn`/`spawnLink`/`spawnMonitor` with `Mod`'s state constructor applied
to `a`. The supervisor's worker is such a loop
(`:job -> run(n + 1)`, `:crash -> exit(:boom)`, `:stop -> :ok`), and the
supervisor proof frames the defer clause with `mcount_deliver`.

**`Sys` metatheory.** `Leanactors/SysProps.lean` collects what every
`Sys`-level proof needs and the example proofs used to re-derive by hand:
`Grows a b` (everything monotone) and `Frame p a b` (the same with `p`
exempt: `p` may change state, die, or lose its links and monitors),
reflexive and transitive; `applyEffects_grows` with per-field projections;
the `terminate` lemmas (`terminate_frame`, exactly which signals and DOWNs
are queued); `runE_frame`, `runE_of_no_exit`, `signalE_frame`,
`downE_grows`, `timerE_grows` and their `_cases` unpackings;
`SysStep.stateOf_cases` (a step changes at most one actor's state) and the
`Fresh` predicate (every live pid is below `next`, preserved by every
step). `SysPropsDemo.lean` re-proves three supervisor cases in one line
each. Writing it found a core bug: `Sys.terminate` never set `timers`, so
the structure default dropped every pending timer whenever any actor died
(a worker crash silently disarmed the watchdog's timeout). It now keeps
them; the watchdog checker grew from 10,365 to 10,411 configurations and
every proof still goes through.

The translator is unverified and supports a small subset (see its header).
The equivalence theorem is what makes that acceptable: if the translation
is wrong, `beh_eq_gen` fails to typecheck.

## Build

```sh
./check.sh              # regenerate Gen/, verify it is unchanged, lake build, run the five drivers
```

or piecewise:

```sh
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > Leanactors/Gen/Lock.lean
lake build              # checks every proof and runs the bounded checkers
elixir elixir/bank.exs  # exits 1 on mismatch with the Lean trace
elixir elixir/lock.exs 20 20000   # exits 1 if two clients ever hold at once
```

## What has been shown so far

**Per-actor invariants are cheap.** The bank's non-negativity is eight
lines per handler clause plus one line to lift to every reachable state.
Elixir's `@spec` checks each clause in isolation; Lean checks the
interleaving.

**Cross-actor invariants are tractable.** Mutual exclusion is a property
of the whole configuration, including messages in flight. The invariant is
six per-pid counters (pending acquire, queue position, grant in flight,
holding, release in flight, waiting) and two linear equations. The
inductive proof is about 450 lines, and almost all of the cost is Lean
plumbing rather than protocol reasoning. The bounded model checker
validated the invariant before any proof was attempted.

**The invariant is stronger than the property.** Mutation testing showed it
catches a lost-token bug that mutual exclusion alone would miss, and it
identifies which defensive checks are load-bearing. The release-sender
check is not, with honest clients.

**Deadlock freedom comes from the same invariant.** `progress_forever`
says a waiting client always has either an enabled actor step or a holder
in the critical section that only the environment can move. About fifty
lines, no new machinery.

**Safety does not need FIFO; bounded waiting does.** Mutual exclusion and
deadlock freedom never use `Step.queue`: the out-of-order case (a client's
`acquire` processed while its `release` is still in flight) is absorbed by
the equation `acquire + queued = waiting`. First-come-first-served is
different. `fcfs` says a client with `r` clients ahead of it sees at most
`r` handovers before it holds the lock, and its rank drops by exactly one
per handover. That accounting breaks if the server can enqueue the current
holder, which is exactly the reorder above. Two invariant fields exclude it:
`ordered` (no `acquire h` ahead of a `release h` in the server's mailbox) and
`holder_not_queued`. Both are inductive only because sends append at the
tail of a mailbox, which is the per-pair FIFO guarantee the BEAM makes.

**Spawn, links and exits are a layer, not a rewrite.** `Sys` wraps a
`Config` with a fresh-pid counter, a link list and a FIFO of pending exit
signals. A behaviour returns effects (`send`, `spawn`, `spawnLink`, `link`,
`exit`) and receives the next fresh pid so a parent knows its child's pid.
Exits propagate the way the BEAM does it: terminating an actor queues one
signal per link, and a separate step delivers the oldest signal, either as
a message to a trapping target or by terminating a non-trapping one, which
queues more signals. No recursion, every step is a function, and
`runE_lift` proves the old `step` is exactly the new one for behaviours
that only send, so the bank and lock results carry over untouched.

The supervisor example is translated from Elixir and uses every new
effect. Its invariant says the parent
is alive and its current child is either alive and linked, or has an exit
signal pending, or has its `EXIT` message already in the parent's mailbox.
The checker validates it on 236,220 configurations, catches the mutant
that forgets `Process.flag(:trap_exit, true)` in 40, and the proof is two
reusable lemmas: a monotone frame for steps that only add, and a
termination lemma for the two places an actor dies.

## Not modelled yet

Real time (timers are untimed and cannot be cancelled), multi-node
delivery, `receive` with `after`, registration races (registered names are
constant pids), `:kill` as untrappable, and exceptions inside handler
bodies (the translator rejects anything outside its subset rather than
approximating it). In message mode an unhandled cast or call is still
modelled as ignored, with a warning; only effects mode has the crash.
