# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib. This file is the
reference; `NOTES.md` is the narrative (what was built, why, what was
learned).

## Status

5,610 lines of hand-written Lean across 20 files under `Leanactors/`
(plus 288 generated lines in six `Gen/` files), 322 `theorem`s, zero
`sorry` and zero `axiom`. Six worked examples (bank, lock, supervisor,
task, watchdog, ttl), each translated from a real Elixir/BEAM module by
the same type-directed translator and checked equal to it by
`beh_eq_gen`. All six have their safety property proved for arbitrary
reachable configurations (unbounded scheduling, unbounded environment
ticks), each independently validated by a bounded model checker before
the proof was attempted. The translator itself has a suite of 31
regression fixtures.

| Example | Property | Checker configurations |
|---|---|---|
| Bank | balance never negative | — (per-actor, no interleaving needed) |
| Lock | mutual exclusion, deadlock freedom, bounded (FCFS) waiting | mutation-tested, 3 mutants |
| Supervisor | parent never dies, dead child always has a restart in flight | 236,220 |
| Task | a pending job is never lost across a crash | mutation-tested (no-monitor mutant) |
| Watchdog | watchdog never dies, dead worker always has a restart in flight | 10,411 |
| Ttl | the cache never holds 0 and never has a `value 0` in flight | 16,723, mutation-tested (store-0 mutant) |

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Sys.lean` | Spawn, links, monitors, exits, timers, remote exit signals: effects, fresh-pid counter, link and monitor lists, asynchronous exit signals and DOWN notifications, untimed timers; an untrappable `kill` signal terminates even a trapping target and its links see `error`; `runE_lift` shows message-only behaviours are unchanged |
| `Leanactors/SysProps.lean` | Reusable `Sys` metatheory: `Grows`/`Frame` relations, `applyEffects` projections, `terminate` lemmas, `runE`/`signalE`/`downE`/`timerE` case and frame lemmas, `SysStep.stateOf_cases`, the `Fresh` predicate, where signals and actors come from (`applyEffects_mem_signals_cases`, `Effect.init?` and the `_stateOf_spawn_cases` lemmas), the `NoKillTo` predicate |
| `Leanactors/Explore.lean` | Generic bounded explorer for `Sys`: `Sys.explore` / `Sys.exploreWith` enumerate runs, signal and DOWN deliveries, timer firings and environment messages to a depth; used by Supervisor, Task and Watchdog |
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
| `Leanactors/Examples/Ttl.lean` | TTL cache translated from `elixir/src/ttl.ex`: `receive ... after` with a generation-counted timer, `Process.register`, `raise`; hand `beh`, `beh_eq_gen`, bounded checker, the store-0 mutant, a stale-timer trace |
| `Leanactors/Examples/TtlProof.lean` | The cache never holds 0 and no `value (some 0)` is in flight: `Inv` over every pid, `Inv.run` by the concrete effect list of each clause, the other steps by the `SysProps` case lemmas |
| `Leanactors/Gen/*.lean` | Generated from `elixir/src/*.ex` by the translator; do not edit |
| `elixir/src/*.ex` | The Elixir source of truth (bank, lock, supervisor, task, watchdog, ttl): executed on the BEAM and translated to Lean |
| `elixir/to_lean.exs` | The translator: `@type`-directed (`msg`, `cast`, `info`, `call`, `reply`, `state`), small subset, unverified |
| `elixir/test/run_fixtures.exs` | Translator regression runner: translates every `test/fixtures/*.ex`, diffs against `test/expected/*.lean`, compiles the ok ones with `lake env lean`, checks the error ones fail as declared; `--regen` rewrites the expectations |
| `elixir/test/fixtures/*.ex` | 31 small sources, one translator feature each (25 `expect: ok`, 6 `expect: error`); directives in the leading comment block |
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
`fresh`, maps `:normal` to `normal`, `:kill` to `kill` and any other
reason to `error`, types `{:EXIT, pid(),
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
`Process.exit(p, reason)` queues an exit signal to `p` with the BEAM's
meaning (see the exit-signal paragraph below). Timers are untimed:
any pending timer may fire at any step, so a GenServer timeout may fire in
the model even though a message arrived first. That over-approximates the
BEAM, which is the sound direction for safety. The watchdog example may
therefore kill a healthy worker, and its property does not care why a
worker died. One thing the untimed model hides: on the BEAM *any* message
resets a GenServer timeout, including `:sys.get_state` polls, which is why
the driver sleeps instead of polling.

**Exit signals: `:kill` and remote `:normal`.** `Reason` is `normal`,
`error` or `kill`. A `kill` signal (`Process.exit(p, :kill)`, translated
to `.signal p .kill`) terminates `p` whether or not it traps, and the
`EXIT` and `DOWN` notifications `p`'s own links and monitors then receive
carry `error` (the BEAM's `:killed`). A `normal` signal from another
process is ignored by a non-trapping `p` and delivered as `{:EXIT, from,
:normal}` to a trapping one; an `error` signal is delivered to a trapping
`p` and kills a non-trapping one. `signalE` therefore matches the reason
before consulting `traps`. A process exiting itself (`{:stop, r, s}`,
`exit/1`, `raise`) notifies its links with `r.propagated`, where `kill`
is reported as `error`. The watchdog kills its worker with
`Process.exit(w, :kill)`. Since a kill would terminate the trapping
supervisor or watchdog, their proofs carry `Sys.NoKillTo 0` (no pending
kill is addressed to pid 0) beside `Inv`; see the `SysProps` paragraphs.

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

**Declared message kinds.** A tag under `@type msg` is a cast or an info
tag, decided by the callback that handles it, so a `msg` tag no clause
mentions is not classified and gets no crash clause. The optional unions
`@type cast :: ...` and `@type info :: ...` fix a tag's kind directly,
like `@type call` always has: `classify/2` seeds the kinds from the
declarations before it scans the clauses, so a cast or call tag with no
clause anywhere gets its crash clause (and a module can become exhaustive
that way, dropping the catch-all) and an info tag with no clause is
ignored through the catch-all. `@type msg` may be omitted when `cast`,
`info` or `call` is declared; the message unions are excluded from enum
rendering. A tag declared in two of `msg`/`cast`/`info`/`call`, a clause
whose callback differs from the tag's declared kind (a `handle_cast` for
an `info` tag, or the reverse), a `msg` tag handled by two kinds, and
`@type cast`/`call` in a raw process are errors. Constructor order per
module is `msg`, `cast`, `info`, `after_<loop>`, `call`, `reply`. The
fixtures `kind_cast_uncovered.ex` and `kind_info_uncovered.ex` show the
two declared cases; `crash_uncovered.ex` the inferred one.

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
clause (`t` is ignored: timers are untimed). The BEAM starts the timeout
when the receive is entered and a processed message cancels it, so the
module's state gets a hidden trailing field `gen : Nat` and the
model-only message `after_<loop> g` carries a generation: `gen` is the
generation of the timer armed by the current receive. A `spawn` of the
module starts the child at generation 0 and arms `.sendAfter child
(.after_<loop> 0)`; every clause that re-enters the receive (a `loop(e)`
tail, the defer clause, a failed guard, the after body itself) moves to
`gen + 1` and arms `.sendAfter me (.after_<loop> (gen + 1))`;
`exit`/`raise` keep the state, generation included. The after body is the
clause for `.after_<loop> gen'` guarded by `if gen' = gen then <body>
else (<state>, [])` (Lean has no non-linear patterns): a message of the
current generation runs the after body, a stale one is consumed and
ignored, never deferred. Timers are still untimed, so the live timer may
fire before or after any message, and a skipped (deferred or
guard-failed) message re-arms where the BEAM would keep the old timeout
running; both only add behaviours. Stale entries stay in `timers` until
they fire. `gen` is reserved in such a module and a blocking call inside
such a loop is a translator error. The TTL cache in `elixir/src/ttl.ex`
is the example: `explore` visits 16,723 configurations at depth 7 with 3
environment stimuli and finds no state in which the cache holds 0; the
mutant that stores 0 instead of raising is caught after two expiries and
one `put 0`. The fixture `receive_after.ex` covers the guard, the exit,
the defer clause, the after arm and the spawn site.

**The Ttl proof.** `Leanactors/Examples/TtlProof.lean` proves the
checked property for every reachable configuration. `Inv` is stated for
every pid, not only the cache at 0 and the reader at 1: no actor in a
`cache` state holds `some 0`, no mailbox contains `value (some 0)`, and
no pending timer carries one. Nobody spawns, links, monitors or traps, so
`Inv.run` is the only case that looks at a message: it goes clause by
clause through the concrete effect lists (`set`, then at most one `send`
and one `sendAfter`, or an `exit`) with `Inv.set`, `Inv.deliver`,
`Inv.arm` and `Inv.terminate`; `Inv.signal`, `Inv.down` and `Inv.timer`
are `signalE_cases`, `downE_cases` and `timerE_cases`. The generation
plays no part in safety (`stale_ignored` is one `simp`), and
`cache_never_zero`, `no_zero_in_flight` and `cache_never_zero_gen` (the
same through `beh_eq_gen`) close the file, 17 theorems in 266 lines.

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

**Translator fixtures.** `elixir/test/fixtures/*.ex` are 31 small
sources, one translator feature each: guard fallthrough and deferral,
nested and pattern-LHS blocking calls, deferred replies, spawn and
monitor, tuple `init`, DOWN and EXIT typing, timeouts, `send_after`,
`Process.exit` with `:kill`, `:normal` and other reasons, self-exits
with `:kill`, `receive ... after` with its generation counter, declared
`@type cast`/`@type info` kinds, registered sends, keyword-named
variables, booleans, wildcards, pid narrowing, `case`/`if`, non-linear
patterns, enum and list splits, the crash clauses, and six sources the
translator must reject (no pid mapping, unknown tag, a tag in two
callback kinds, a tag declared under two kinds, a clause of the wrong
declared kind, trapping without `{:EXIT, ...}`). Each fixture's leading comment block carries its
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
and every proof still goes through. Round 3 added `Reason.propagated` and
the kill case: `signalE_cases` is five-way (the trapped alternative
carries `r ≠ .kill`, the kill alternative is last), `signalE_stateOf`
says a target dies only of a non-normal signal, `runE_cases` reports a
self-exit as `reason.propagated`, and three new groups of lemmas:
`applyEffects_mem_signals_cases` (every signal is an old one, a `noproc`
error, or one of the step's own `signal` effects; the projection
`applyEffects_mem_signals` is unchanged), `Effect.init?` with
`applyEffects_stateOf_cases` / `runE_stateOf_spawn_cases` /
`SysStep.stateOf_spawn_cases` (every actor after a step is unchanged,
dead, the actor that ran, or spawned in the initial state of one of that
step's effects; no `q < next` bound), and `Sys.NoKillTo p` (no pending
kill is addressed to `p`) with `NoKillTo.runE`/`signalE`/`downE`/`timerE`,
`SysStep.noKillTo` and `SysReach.noKillTo_of_no_signal`. `SysProps.lean`
is 1,373 lines.

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
`Inv.down`) now live in `SupervisorProof.lean`. Since a kill can now
terminate the trapping supervisor or watchdog, their `Inv.signal` and
`Inv.step` take `NoKillTo 0` as an extra hypothesis and `reach_inv`
inducts on `Inv` together with it: the supervisor emits no `signal` at
all (`beh_no_signal`); the watchdog's only signal is the kill to its own
worker, which is never pid 0 because every worker is spawned at a fresh
positive pid, the `ChildNe` invariant carried through
`SysStep.stateOf_spawn_cases`. Every named theorem keeps its statement
(`SupervisorProof.lean` 315 lines, `WatchdogProof.lean` 361,
`TaskProof.lean` 313). Checker counts did not move: 236,220 / 40,
10,411 / 749, 243,526.

**The generic explorer.** `Leanactors/Explore.lean` defines
`Sys.livePids`, `Sys.exploreWith beh sig check envMsgs s depth env`
(`envMsgs : Pid → List μ`) and `Sys.explore` (one fixed list of
environment messages for every live pid). From a start configuration it
enumerates depth-first every interleaving of `run p` for every live pid,
`signal`, `down`, `timer i` for every pending timer, and `env m -> p`
(each environment message spends one unit of `env`), checking a `Bool`
invariant at every configuration and returning the count and the first
violating path as labels (`"run 0"`, `"signal"`, `"timer 0"`, `"env
<repr m> -> p"`; `[Repr μ]` is required). Steps that are not enabled cost
nothing, so Supervisor, Task and Watchdog now call it with the same
counts and witnesses as their deleted local copies. `Ttl.lean` and
`Lock.lean` keep local explorers (the lock's core is `Config`, not
`Sys`).

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
elixir elixir/test/run_fixtures.exs         # 31 translator fixtures; --regen rewrites the expectations
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
signal per link, and a separate step delivers the oldest signal: as a
message to a trapping target, by ignoring a `normal` one or terminating a
non-trapping target on `error`, or by terminating the target regardless
on `kill`, which queues more (`error`) signals. No recursion, every step
is a function, and
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

Real time (timers are untimed; a `receive ... after` timeout is exact up
to timing through its generation counter, while a GenServer `{:noreply,
s, t}` timeout is still never cancelled and may fire late; stale `after`
entries stay in `timers` until they fire and are ignored), multi-node
delivery, registration races (registered names are constant pids,
whether derived from the source or given with `--pid`), a process that
exits *itself* with `:kill` (its links see `error`, where the BEAM sends
a trappable `:kill` to them; who dies is the same), and exceptions that
are caught (`rescue`, `catch`, `try`) or raised anywhere but in tail
position (the translator rejects anything outside its subset rather than
approximating it). A `@type msg` tag that no callback of a module
mentions is not classified and gets no crash clause; declare it under
`@type cast` (crash clause even with no clause) or `@type info` (ignored)
to fix its kind.
