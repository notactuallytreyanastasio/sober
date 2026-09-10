# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib. This file is the
reference; `NOTES.md` is the narrative (what was built, why, what was
learned).

## Status

4,924 lines of hand-written Lean across 20 files (plus 288 generated
lines in six `Gen/` files), 275 `theorem`s, zero `sorry` and zero `axiom`.
Six worked examples (bank, lock, supervisor, task, watchdog, ttl), each
translated from a real Elixir/BEAM module by the same type-directed
translator and checked equal to it by `beh_eq_gen`. The first five have
their safety property proved for arbitrary reachable configurations
(unbounded scheduling, unbounded environment ticks), each independently
validated by a bounded model checker before the proof was attempted; the
sixth is bounded-checked only so far. The translator itself has a suite of
25 regression fixtures.

| Example | Property | Checker configurations |
|---|---|---|
| Bank | balance never negative | — (per-actor, no interleaving needed) |
| Lock | mutual exclusion, deadlock freedom, bounded (FCFS) waiting | mutation-tested, 3 mutants |
| Supervisor | parent never dies, dead child always has a restart in flight | 236,220 |
| Task | a pending job is never lost across a crash | mutation-tested (no-monitor mutant) |
| Watchdog | watchdog never dies, dead worker always has a restart in flight | 10,411 |
| Ttl | the cache never holds 0 and never has a `value 0` in flight (checked, not yet proved) | 17,206, mutation-tested (store-0 mutant) |

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Sys.lean` | Spawn, links, monitors, exits, timers, remote exit signals: effects, fresh-pid counter, link and monitor lists, asynchronous exit signals and DOWN notifications, untimed timers; `runE_lift` shows message-only behaviours are unchanged |
| `Leanactors/SysProps.lean` | Reusable `Sys` metatheory: `Grows`/`Frame` relations, `applyEffects` projections, `terminate` lemmas, `runE`/`signalE`/`downE`/`timerE` case and frame lemmas, `SysStep.stateOf_cases`, the `Fresh` predicate |
| `Leanactors/Examples/SysPropsDemo.lean` | Three supervisor proof shapes (monotone along `Grows`, the timer case, the DOWN case) as `example`s spelled out against `SysProps` directly |
| `Leanactors/Examples/Supervisor.lean` | One-for-one supervisor translated from `elixir/src/supervisor.ex`; bounded checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/SupervisorProof.lean` | The supervisor never dies and a missing child always has its restart in flight; the case split is by pid, not by message (`Inv.run_ne`, `Inv.run`) |
| `Leanactors/Examples/Task.lean` | Async task translated from `elixir/src/task.ex`: caller spawns and monitors a worker; checker; the no-monitor mutant |
| `Leanactors/Examples/TaskProof.lean` | A pending job is never lost: the reply or the DOWN is always on its way |
| `Leanactors/Examples/Watchdog.lean` | Watchdog translated from `elixir/src/watchdog.ex`: GenServer timeout, `Process.exit/2`, restart on EXIT; checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/WatchdogProof.lean` | The watchdog never dies and a dead worker always has its restart in flight |
| `Leanactors/Examples/Bank.lean` | Per-actor invariant: a bank's balance never goes negative under any scheduler |
| `Leanactors/Examples/Lock.lean` | Cross-actor invariant: lock server + clients blocking in `GenServer.call`, token invariant, bounded model checker |
| `Leanactors/Examples/LockProof.lean` | The invariant is inductive; `mutex_forever` and `progress_forever` under any scheduler and any environment ticks |
| `Leanactors/Examples/LockFcfs.lean` | Bounded waiting: rank drops by exactly one per handover while queued; `fcfs` in reachable configurations |
| `Leanactors/Examples/LockMutants.lean` | Three protocol bugs: two caught with witness traces, one shown unreachable |
| `Leanactors/Examples/Ttl.lean` | TTL cache translated from `elixir/src/ttl.ex`: `receive ... after`, `Process.register`, `raise`; hand `beh`, `beh_eq_gen`, bounded checker, the store-0 mutant |
| `Leanactors/Gen/*.lean` | Generated from `elixir/src/*.ex` by the translator; do not edit |
| `elixir/src/*.ex` | The Elixir source of truth (bank, lock, supervisor, task, watchdog, ttl): executed on the BEAM and translated to Lean |
| `elixir/to_lean.exs` | The translator: `@type`-directed, small subset, unverified |
| `elixir/test/run_fixtures.exs` | Translator regression runner: translates every `test/fixtures/*.ex`, diffs against `test/expected/*.lean`, compiles the ok ones with `lake env lean`, checks the error ones fail as declared; `--regen` rewrites the expectations |
| `elixir/test/fixtures/*.ex` | 25 small sources, one translator feature each (21 `expect: ok`, 4 `expect: error`); directives in the leading comment block |
| `elixir/test/expected/*.lean` | Their expected translations, committed; regenerate with `elixir/test/regen_expected.sh` and review the diff |
| `elixir/bank.exs` | Driver: casts plus two clients blocking in `GenServer.call`; checks the trace matches Lean |
| `elixir/lock.exs` | Driver: clients block in `GenServer.call` under chaos ticks; event log checked for overlapping critical sections |
| `elixir/supervisor.exs` | Driver: crashes the worker on the BEAM and checks the supervisor survived and restarted it |
| `elixir/task.exs` | Driver: one job completes, one worker crashes; the caller clears both |
| `elixir/watchdog.exs` | Driver: hangs the worker, lets the timeout kill it, checks the replacement is running |
| `elixir/ttl.exs` | Driver: put, get, let the TTL expire, get again, a reader asks, then `put 0` and the cache dies with `ArgumentError` |
| `NOTES.md` | Design narrative: the thesis, the layers, the translator, the proof recipe, findings, approximations and their direction |

## Pipeline: Elixir source to Lean theorem

```
elixir/src/lock.ex          ordinary GenServer modules with @type msg / @type state
      │
      ├── elixir/lock.exs     runs them on the BEAM under chaos ticks (property test)
      │
      └── elixir/to_lean.exs  reads the @types, emits Leanactors/Gen/Lock.lean:
                              inductive Msg / St / Phase, `def sig : Signals St Msg`
                              and `def beh : EBehavior St Msg`
                                    │
                                    ▼
Leanactors/Examples/Lock.lean       `theorem beh_eq_gen : Gen.Lock.beh = lift beh` (funext + cases + rfl/split)
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

**One output shape.** Every file is translated to an `EBehavior St Msg`
over `Leanactors.Sys`: clauses have the shape `| me, fresh, state, msg =>
(state, [effects])`, sends are `.send` effects, and a `sig : Signals St
Msg` record is always emitted (`traps` false everywhere and a placeholder
`exitMsg`, the first nullary message constructor, when no module traps or
declares `{:EXIT, ...}`). When a file uses `Process.flag(:trap_exit,
true)`, `{:ok, pid} = GenServer.start_link(Mod, arg)`, `{:stop, reason,
state}` or `exit/1`, the translator turns `start_link` into `spawnLink`
with the child's initial state (see below), binds the pid variable to
`fresh`, maps any non-`:normal` reason to `error`, types `{:EXIT, pid(),
term()}` as `EXIT (Pid) (Reason)`, and fills in which modules trap. A file
that only sends is a message-only `EBehavior`; its hand model keeps a
plain `Behavior` and proves `Gen.X.beh = lift beh`, so `runE_lift` carries
the bank and lock results over unchanged. (Until this round such files
produced a plain `Behavior` from a separate "message mode" of the
translator; that mode and its warnings are gone.)

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
error reason; an unmatched `handle_info` is ignored. The translator
classifies every message tag by the callback that handles it and emits,
for each cast or call tag that the module's clauses do not cover, a crash
clause `| _, _, .mod s_0 .., .tag _ .. => (state, [.exit .error])`; a
guarded cast/call clause whose guard fails with nothing to fall through to
crashes the same way. Coverage is a usefulness check over the rendered
Lean patterns, not the Elixir ones: a pid-narrowed variable renders as
`(some w)` and leaves `none` uncovered, while `true`/`false`,
`none`/`some`, `[]`/`::` and the alternatives of a generated enum together
cover a field (integer literals never do). A module all of whose tags are
covered or crash needs neither a defer clause nor the global catch-all,
which Lean would reject as redundant. Clauses are emitted per module with
`handle_info` clauses after the cast/call clauses and the crash clauses,
so an info catch-all cannot shadow a crash. The watchdog example found a
real bug this way: with `:pong` handled only while a pong is expected, a
late pong after a timeout crashed the watchdog after 742 explored
configurations; the fix is one `handle_cast(:pong, s)` ignore clause.

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

**`receive` with `after`.** A receive loop may have one `after t -> body`
clause (`t` is ignored: timers are untimed). The module gets a model-only
message constructor `after_<loop>`; every clause that re-enters the
receive (a `loop(e)` tail, the defer clause, a failed guard) also arms
`.sendAfter me .after_<loop>`, a `spawn` of the module arms it at the
child, and the after body becomes the clause for that message with the
loop parameter as its state. Timers are never cancelled and every
re-entry arms a new one, so they accumulate and a stale `after_<loop>` may
fire late, after other messages have been handled. That over-approximates
the BEAM, where any message resets the timeout, and is sound for safety
(a stale expiry can only lose a cached value) but not for liveness. The
TTL cache in `elixir/src/ttl.ex` is the example: `explore` visits 17,206
configurations at depth 7 with 3 environment stimuli and finds no state
in which the cache holds 0; the mutant that stores 0 instead of raising is
caught after two stale expiries and one `put 0`.

**Registered names.** `send(Mod, m)`, `GenServer.cast(Mod, m)` and
`GenServer.call(Mod, m)` need a constant pid for `Mod`. With `--pid` flags
the map is exactly those flags (the five older sources keep theirs, so
their generated files are byte-identical). Without any flag it is derived
from the source: `GenServer.start_link/start(_, _, name: N)` and
`Process.register(_, N)` anywhere in a module register `N` (`__MODULE__`,
an alias or an atom) as the Lean constant `N` lowercased, and atom names
work as send and cast targets (`send(:cache, m)`). `ttl.ex` is translated
with no flags: `Process.register(pid, __MODULE__)` in `Cache.start` makes
`cache` pid 0. Registration is still static: no registry, no races.

**Exceptions.** A body whose last statement is `raise ...` or `throw ...`
(any arguments) exits the process with reason `error` and the state
unchanged, exactly like `exit/1`: an uncaught exception kills the process
and its links and monitors fire. A `raise` or `throw` anywhere else, and
any `rescue`/`catch`, is still a hard error. `ttl.ex` uses it: `{:put, 0}
-> raise ArgumentError, ...` is the clause `| _, _, .cache v, .put 0 =>
(.cache v, [.exit .error])`.

**Translator fixtures.** `elixir/test/fixtures/*.ex` are 25 small
sources, one translator feature each: guard fallthrough and deferral,
nested and pattern-LHS blocking calls, deferred replies, spawn and
monitor, tuple `init`, DOWN and EXIT typing, timeouts, `send_after`,
`Process.exit`, registered sends, keyword-named variables, booleans,
wildcards, pid narrowing, `case`/`if`, non-linear patterns, enum and list
splits, the crash clauses, and four sources the translator must reject
(no pid mapping, unknown tag, a tag in two callback kinds, trapping
without `{:EXIT, ...}`). Each fixture's leading comment block carries its
directives (`translate:` flags, `expect: ok` or `expect: error SUBSTRING`,
`lean: check`); `elixir/test/run_fixtures.exs` translates each one, diffs
it against `elixir/test/expected/*.lean` byte for byte, compiles the ok
ones with `lake env lean` (no errors, no warnings) and checks the error
ones fail with the declared text. `check.sh` runs it between the
translation diff and `lake build`. Writing the fixtures found four
translator bugs (an `exitMsg` placeholder that only `task.ex` could
typecheck, a redundant catch-all for single-module sources, `some (some
p')` for a whole-state alias through `Option`, and a tuple-of-variables
state pattern not recognised as general), and the uniform output shape
exposed a fifth: clauses that split a `Bool` field were exhaustive to Lean
but not to the translator, which is why coverage is now a usefulness
check. After any intentional translator change run
`elixir/test/regen_expected.sh` and review `git diff elixir/test/expected`.

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
step); since this round also `Effect.isolated` (everything but `link`,
`spawnLink` and `signal`) with `applyEffects_links_signals_of_isolated`,
`downE_of_codec`, and the `links`/`signals` projections of `downE` and
`timerE`. Writing it found a core bug: `Sys.terminate` never set `timers`,
so the structure default dropped every pending timer whenever any actor
died (a worker crash silently disarmed the watchdog's timeout). It now
keeps them; the watchdog checker grew from 10,365 to 10,411 configurations
and every proof still goes through.

**The `Sys` proofs on `SysProps`.** The three `Sys` example proofs were
rewritten on the library with every theorem statement unchanged (`Inv`,
`Inv.frame`, `Inv.terminate_ne`, `Inv.cleared`, `Inv.step`, `init_inv`,
`reach_inv`, `supervisor_alive`, `restart_in_flight`, `job_never_lost`,
`watchdog_alive`): `SupervisorProof.lean` 396 to 290 lines,
`TaskProof.lean` 394 to 313, `WatchdogProof.lean` 433 to 287, with
`SysProps.lean` growing from 985 to 1,079 by the additive lemmas above.
The case analysis is now by pid instead of by message. For any `p ≠ 0`,
`runE_cases` splits a step into "set `p`'s state, then `Grows`"
(`Inv.set_ne` plus `Inv.grows`) or "terminate" (`Inv.terminate_frame`),
whatever the message was, so the five-to-seven worker message cases per
file disappear; only pid 0's step looks at the message, and even its
no-op cases are `sup_noop`/`dog_noop`/`caller_noop` plus `Grows` without
reducing `applyEffects`. Signals use `signalE_cases` and `Inv.pop_signal`,
DOWN and timer steps are one-line `Grows`, and the task's DOWN case uses
`downE_of_codec`. `SysPropsDemo.lean` keeps its three demonstrations as
`example`s; the lemmas it used to define (`Inv.grows`, `Inv.timer`,
`Inv.down`) now live in `SupervisorProof.lean`.

The translator is unverified and supports a small subset (see its header).
The equivalence theorem is what makes that acceptable: if the translation
is wrong, `beh_eq_gen` fails to typecheck.

## Build

```sh
./check.sh              # regenerate Gen/, verify it is unchanged, run the translator fixtures,
                        # lake build, run the six drivers
```

or piecewise:

```sh
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > Leanactors/Gen/Lock.lean
elixir elixir/to_lean.exs elixir/src/ttl.ex Leanactors.Gen.Ttl > Leanactors/Gen/Ttl.lean   # names derived from the source
elixir elixir/test/run_fixtures.exs         # 25 translator fixtures; --regen rewrites the expectations
lake build              # checks every proof and runs the bounded checkers
elixir elixir/bank.exs  # exits 1 on mismatch with the Lean trace
elixir elixir/lock.exs 20 20000   # exits 1 if two clients ever hold at once
elixir elixir/ttl.exs   # exits 1 unless put 0 kills the cache and the expiry matches the model
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

Real time (timers are untimed and cannot be cancelled, so `after` timers
accumulate and may fire late), multi-node delivery, registration races
(registered names are constant pids, whether derived from the source or
given with `--pid`), `:kill` as untrappable, and exceptions that are
caught (`rescue`, `catch`, `try`) or raised anywhere but in tail position
(the translator rejects anything outside its subset rather than
approximating it). A `@type msg` tag that no callback of a module mentions
gets no crash clause (only tags seen in some clause or in `@type call` are
classified); the fixture `crash_uncovered.ex` covers the classified case.
