# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib. This file is the
reference; `NOTES.md` is the narrative (what was built, why, what was
learned).

## Status

15,034 lines of hand-written Lean across 40 files under `Leanactors/`
(plus 612 generated lines in thirteen `Gen/` files), 813 `theorem`s, zero
`sorry` and zero `axiom`. Thirteen worked examples (bank, lock,
supervisor, task, watchdog, ttl, registry, feed, ringlog, table registry,
log store, logs live, radio live), each translated from a real
Elixir/BEAM module by the same type-directed translator and checked equal
to it by `beh_eq_gen`. Four of the thirteen were not written for this
repository: `elixir/real/table_registry.ex`, `log_store.ex`,
`logs_live.ex` and `radio_live.ex` are byte-for-byte copies of
`Loom.Teams.TableRegistry`, `Ensemble.LogStore`, `EnsembleWeb.LogsLive`
and `BobsBroadcastWeb.RadioLive`, translated with no annotations and no
edits (see **Untyped mode**) — and that they are *still* byte-for-byte is
checked on every run of `check.sh` (`elixir/real_provenance.exs` against
`elixir/real/MANIFEST.json`), not asserted here. Eight have a safety
property proved for every configuration reachable under unbounded
scheduling (the lock also under unbounded environment ticks; the `Sys`
examples are proved as closed systems, see **Liveness** below), each
independently validated by a bounded model checker before the proof was
attempted; the registry and the feed have theirs checked but not proved
(the feed has the weaker `subs_feed_only` proved instead), and the three
newest — the log store and the two LiveViews — have theirs checked, the
radio view also with a one-step invariant of the behaviour
(`agrees_step`) proved. The supervisor, the lock, the task, the
watchdog and the ttl cache also have a liveness property proved along
fair runs, each with a witness that its premise is reachable and its
fairness assumptions are satisfiable. The two interpreters the checkers
and traces run on are fuzzed against the BEAM (`elixir/fuzz.exs`, 200
seeded scripts per `check.sh`). The translator itself has a suite of 81
regression fixtures (57 `expect: ok`, 24 `expect: error`), and
`elixir/readiness.exs` measures the subset against real code, with the
numbers committed as a baseline `check.sh` re-measures (**Readiness**).

| Example | Property | Checker configurations |
|---|---|---|
| Bank | balance never negative | — (per-actor, no interleaving needed) |
| Lock | mutual exclusion, deadlock freedom, bounded (FCFS) waiting; liveness: a blocked client eventually holds | mutation-tested, 3 mutants |
| Supervisor | parent never dies, dead child always has a restart in flight; liveness: a dead child is eventually replaced | 236,220 |
| Task | a pending job is never lost across a crash; liveness: a pending job eventually settles (unconditionally once the worker is dead; for a live worker, provided the environment eventually gives it work) | mutation-tested (no-monitor mutant) |
| Watchdog | watchdog never dies, dead worker always has a restart in flight; liveness: a dead worker is eventually replaced, and a worker the watchdog is waiting on is eventually killed and replaced | 10,411 |
| Ttl | the cache never holds 0 and never has a `value 0` in flight; liveness: a held value is cleared by its timer unless a message is processed first (or `put 0` kills the cache) | 16,093, mutation-tested (store-0 mutant) |
| Registry | a registered name maps to a live pid or its DOWN is in flight (checked, not yet proved) | 19,677, mutation-tested (no-monitor mutant) |
| Feed | every subscriber has received a prefix of the published sequence (checked); every subscription is to `"feed"` and never the publisher's (proved) | 53,845, mutation-tested (no-unsubscribe and stale-number mutants) |
| Ringlog | `count` equals the queue's length and never exceeds `max_entries` | 9,348, mutation-tested, 2 mutants |
| Table registry | a team maps to at most one ETS table, and distinct teams never share one | 11,737, mutation-tested (no counter bump) |
| Log store | the entry count never exceeds `max_entries` | 11,737, mutation-tested (counter bumped on both branches) |
| Logs live | message handling is append-only: what the view shows stays, in order, at the front of what it shows next | 809, mutation-tested (prepend instead of append) |
| Radio live | the Play/Stop button agrees with the track | 809, mutation-tested (the mutant that forgets the second link of the assign chain); also a one-step invariant proved |

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Sys.lean` | Spawn, links, monitors, exits, timers, remote exit signals: effects, fresh-pid counter, link and monitor lists, asynchronous exit signals and DOWN notifications, untimed timers; PubSub subscriptions (`subs : List (String × Pid)` with `subscribe`/`unsubscribe`/`broadcast`, a death dropping the dead pid's subscriptions); an untrappable `kill` signal terminates even a trapping target and its links see `error`; `runE_lift` shows message-only behaviours are unchanged |
| `Leanactors/SysProps.lean` | Reusable `Sys` metatheory: `Grows`/`Frame` relations, `applyEffects` projections, `terminate` lemmas, `runE`/`signalE`/`downE`/`timerE` case and frame lemmas, `SysStep.stateOf_cases`, the `Fresh` predicate, where signals and actors come from (`applyEffects_mem_signals_cases`, `Effect.init?` and the `_stateOf_spawn_cases` lemmas), the `NoKillTo` predicate, and (round 5) the `timers` append lemmas `runE_timers_append`/`signalE_timers`/`downE_timers`; (round 6) the subscription family: `Effect.keepsSubs` with `applyEffect`/`applyEffects`/`runE_subs_of_keepsSubs`, the `_mem_subs` and `_mem_subs_cases` lemmas up to `SysStep.mem_subs_cases` (the induction workhorse), `applyEffect_broadcast`, `broadcast_stateOf`/`broadcast_mcount` and the `terminate`/`signalE`/`downE`/`timerE` subscription lemmas |
| `Leanactors/Explore.lean` | Generic bounded explorer for `Sys`: `Sys.explore` / `Sys.exploreWith` enumerate runs, signal and DOWN deliveries, timer firings and environment messages to a depth; used by Supervisor, Task, Watchdog and Ttl |
| `Leanactors/Fair.lean` | Fairness and liveness for both layers: infinite runs that may idle (`CRun` over `Config` with an environment relation, `SysRun` over a closed `Sys`, `SysRunE` over an open `Sys` with an environment relation such as `Sys.Deliver`), labelled steps `CStepL`/`SysStepL`/`SysStepLE`, `ReachE`/`SysReachEnv`/`SysReachE`, `CEnabled`/`SysEnabled`, `WeakFair`/`EnvFair`, `Eventually`/`Always`/`LeadsTo`, the workhorses `stable_until` and `rank_leads_to` for each layer, `LeadsTo.rank_induction`, `SysRun.toE` embedding a closed run; the erase/`findIdx` list facts the timer-driven proofs rank with; `FairDemo` two-state sanity check |
| `Leanactors/AssocList.lean` | Association lists `List (K × V)`, the model of an Elixir map: `get?`/`insert`/`erase`/`hasKey`/`keys`/`values`/`size`/`filter`/`reject` with `get?_insert_self`/`_ne`, `get?_erase_self`/`_ne`, `hasKey_iff`, `mem_of_get?`, `mem_insert`, `mem_erase`, `mem_filter`, `mem_reject`, `mem_erase_of_ne`; the uniqueness group `Uniq` (no two entries share a key, no two share a value) with `uniq_nil`/`uniq_cons`, the extraction lemmas `Uniq.key_inj`/`Uniq.val_inj` and the preservation steps `Uniq.insert_fresh`/`Uniq.erase`; first-match semantics, no uniqueness assumed by the rest, no Mathlib |
| `Leanactors/Str.lean` | Elixir binaries as Lean `String`s: the `ToStr` class with faithful instances for `String`, `Nat`, `Int` and `Bool` and a low-priority one through `Repr`, `Str.toStr` (what an interpolation and `inspect`/`to_string` render with), and the append lemmas |
| `Leanactors/SetList.lean` | `MapSet` as a duplicate-free list in insertion order: `contains`/`insert`/`erase`/`size`/`toList`/`ofList`/`union`/`difference`/`intersection` with 14 lemmas |
| `Leanactors/Time.lean` | The clock, deliberately trivial: a one-constructor `inductive Instant` whose only value is `now`, with `DecidableEq` and `Repr`, `Instant.eq_now`/`all_eq`, and no `LT`, `LE` or arithmetic — a module whose behaviour depends on time passing is refused by the translator rather than modelled wrongly |
| `Leanactors/Replay.lean` | The `replay` executable (`lake build`, `.lake/build/bin/replay`): a line script on stdin (`example bank\|ttl\|lock`, then `deliver <pid> <msg>`, `run <pid>`, `signal`, `down`, `timer <i>`), replayed with `run` (bank, lock) or `runSys` (ttl), printing the final observables in a canonical text form; a choice the model cannot follow is an error, not a silent stop |
| `Leanactors/Examples/SysPropsDemo.lean` | Three supervisor proof shapes (monotone along `Grows`, the timer case, the DOWN case) as `example`s spelled out against `SysProps` directly |
| `Leanactors/Examples/Supervisor.lean` | One-for-one supervisor translated from `elixir/src/supervisor.ex`; bounded checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/SupervisorProof.lean` | The supervisor never dies and a missing child always has its restart in flight; the case split is by pid, not by message (`Inv.run_ne`, `Inv.run`) |
| `Leanactors/Examples/SupervisorLive.lean` | Liveness: under weak fairness of the `signal` step and of `run 0`, a dead child is eventually replaced (`restart_eventually`, from any `Good` system; `_env` and `_init` corollaries); two `rank_leads_to` stages on the position of the pending signal in the FIFO signal queue and of the `EXIT` in the supervisor's mailbox |
| `Leanactors/Examples/Task.lean` | Async task translated from `elixir/src/task.ex`: caller spawns and monitors a worker; checker; the no-monitor mutant |
| `Leanactors/Examples/TaskProof.lean` | A pending job is never lost: the reply or the DOWN is always on its way |
| `Leanactors/Examples/TaskLive.lean` | Liveness: `job_eventually_settles_dead` (closed `SysRun`, weak fairness of `down` and `run 0`: a caller waiting on a dead worker eventually has no pending job) and `job_eventually_settles` (open `SysRunE` with `Sys.Deliver`, plus `WeakFair (.run w)` and `EnvFair (Alive w) (Kick w)`: the environment eventually sends the awaited live worker `compute` or `crash`); `Good` = `Inv` + `Fresh` + `Shape`; four `LeadsTo` stages; witnesses `deadRun_witness`, `liveRun_witness` |
| `Leanactors/Examples/Watchdog.lean` | Watchdog translated from `elixir/src/watchdog.ex`: GenServer timeout, `Process.exit/2`, restart on EXIT; checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/WatchdogProof.lean` | The watchdog never dies and a dead worker always has its restart in flight |
| `Leanactors/Examples/WatchdogLive.lean` | Liveness: `restart_eventually` (a dead worker is eventually replaced, as for the supervisor) and `worker_replaced`/`hung_worker_replaced` (a worker the watchdog waits on is eventually replaced by a live pid other than it, under fairness of the `(0, timeout)` timer, `signal` and `run 0`); `SysRun.TimerFair` derived from `∀ i, WeakFair (.timer i)`; `SysRun.stable_until_timer` and `SysRun.exists_of_inv` (a run from a phase invariant) are generic; witnesses `hung_worker_reachable`, `hung_fair_run` |
| `Leanactors/Examples/Bank.lean` | Per-actor invariant: a bank's balance never goes negative under any scheduler |
| `Leanactors/Examples/Lock.lean` | Cross-actor invariant: lock server + clients blocking in `GenServer.call`, token invariant, bounded model checker |
| `Leanactors/Examples/LockProof.lean` | The invariant is inductive; `mutex_forever` and `progress_forever` under any scheduler and any environment ticks |
| `Leanactors/Examples/LockFcfs.lean` | Bounded waiting: rank drops by exactly one per handover while queued; `fcfs` in reachable configurations |
| `Leanactors/Examples/LockLive.lean` | Liveness: `eventually_holds` along a fair `CRun`; three phases (request in the server's mailbox, queued with rank induction over handovers, grant in the client's own mailbox), each a `LeadsTo` from the `Fair.lean` workhorses; one measure family `idxOf` (index of a message in a mailbox) handles deferral by re-enqueue |
| `Leanactors/Examples/LockMutants.lean` | Three protocol bugs: two caught with witness traces, one shown unreachable |
| `Leanactors/Examples/Ttl.lean` | TTL cache translated from `elixir/src/ttl.ex`: `receive ... after` with a generation-counted timer, `Process.register`, `raise`; hand `beh`, `beh_eq_gen`, bounded checker, the store-0 mutant, a stale-timer trace |
| `Leanactors/Examples/TtlProof.lean` | The cache never holds 0 and no `value (some 0)` is in flight: `Inv` over every pid, `Inv.run` by the concrete effect list of each clause, the other steps by the `SysProps` case lemmas |
| `Leanactors/Examples/TtlLive.lean` | Liveness: under weak fairness of the oldest pending timer and of `run 0`, a held value does not stay at its generation (`gen_advances_or_clears`: the after body clears it, a message re-arms at `g + 1`, or `put 0` kills the cache; `value_eventually_expires` when no message is processed); two `rank_leads_to_of_step` stages on the timer's position in `timers` and on `after_run g`'s position in the cache's mailbox; `Good` = links and signals empty, pid 0 a cache, the current generation's timer in flight (`Armed`), kept by every step and delivery; explicit fair witness run `wit` |
| `Leanactors/Examples/Registry.lean` | Name registry translated from `elixir/src/registry.ex`: state `%{name() => pid()}` as an association list, monitored clients; hand `beh`, `beh_eq_gen`, bounded checker over every map entry, the no-monitor mutant, `taken`/`freed` traces, two run-case lemmas toward the invariant proof |
| `Leanactors/Examples/Feed.lean` | PubSub feed translated from `elixir/src/feed.ex`: a publisher broadcasting `post n` on the topic `"feed"`, two subscribers that subscribe in `init/1` and count posts, one leaving; hand `beh`, `beh_eq_gen`, the bounded check that each subscriber has seen a prefix of the published sequence and is owed exactly the rest in order, two mutants, and `subs_feed_only` proved through `SysStep.mem_subs_cases` |
| `Leanactors/Examples/Ringlog.lean` | Ring buffer of log entries translated from `elixir/src/ringlog.ex`: hand `beh`, `beh_eq_gen`, the bounded check of `count = entries.length` and `count ≤ max_entries` (two mutants caught in 7 configurations), and the proof — `ok_step` for one behaviour step, `beh_no_spawn`, `count_invariant` for every reachable configuration |
| `Leanactors/Examples/TableRegistry.lean` | `Loom.Teams.TableRegistry` with no annotations at all: hand `beh`, `beh_eq_gen`, the bounded uniqueness check, the no-counter-bump mutant and two traces |
| `Leanactors/Examples/TableRegistryProof.lean` | The proof for the first file copied unmodified out of a real project: the `Bounded`/`Uniq` invariant over every reachable configuration, `Inv.step` over all four `SysStep` cases, and `team_has_one_ref`, `refs_unique`, `refs_distinct` (distinct team ids, distinct ETS references) and `refs_below_counter`, each also through `beh_eq_gen`; the docstring says what the abstraction does not cover — ETS itself is opaque fresh values and `:ets.delete/1` is dropped, so these are properties of the registry's map |
| `Leanactors/Examples/LogStore.lean` | `Ensemble.LogStore` with no annotations: hand `beh`, `beh_eq_gen`, the bounded check that the entry count never exceeds `max_entries`, the runaway-counter mutant and one trace |
| `Leanactors/Examples/LogsLive.lean` | `EnsembleWeb.LogsLive`, the LiveView that shows what the store broadcasts: hand `beh`, `beh_eq_gen`, the append-only check and the prepend mutant; the docstring names `handle_event/3` as the transition the model does not carry |
| `Leanactors/Examples/RadioLive.lean` | `BobsBroadcastWeb.RadioLive` with no annotations: hand `beh`, `beh_eq_gen`, the bounded check that `playing` is true exactly when `now_playing` holds a track, the mutant that keeps the old `playing`, `agrees_step` proved of every state the behaviour produces, and one trace. The property is of the mailbox, not of the running view: `handle_event("play", ..)` sets `playing` on its own, and that transition is not in the model |
| `Leanactors/Term.lean` | An opaque term: a structure over `Nat` with `DecidableEq` and `Repr`, the type of every field whose Elixir type the translator does not know (untyped mode, `term()`/`any()`/`reference()`, the reference `:ets.new` returns), with `Term.fresh` and the `id` lemmas |
| `Leanactors/Gen/*.lean` | Generated from `elixir/src/*.ex` and `elixir/real/*.ex` by the translator; do not edit |
| `elixir/src/*.ex` | The Elixir source of truth (bank, lock, supervisor, task, watchdog, ttl, registry, feed, ringlog): executed on the BEAM and translated to Lean |
| `elixir/src/pubsub.ex` | A 44-line local stand-in for `Phoenix.PubSub` (`subscribe/2`, `unsubscribe/2`, `broadcast/3`, `subscribers/2`) so the drivers run without the `phoenix_pubsub` dependency; not translated — it is the transport, and PubSub is an effect of `Sys` rather than an actor |
| `elixir/real/*.ex` | Real modules copied verbatim from other projects and translated as they stand; `elixir/real/MANIFEST.json` records each one's origin path and its md5 at landing |
| `elixir/land_real.exs` | Lands a real module in one command: translates it at its ORIGINAL path (an error there is the answer), copies it in and checks the copy is byte-identical, regenerates the Lean from the copy, appends the `check.sh` translate and diff lines, writes a skeleton `Leanactors/Examples/<Name>.lean` and adds the imports, and records the origin. Idempotent. The skeleton's `beh` is the generated clauses *copied*, so `beh_eq_gen` holds at once and says nothing: rewriting it by hand, and writing `init` and a bounded check of a property that is true of the module, is the part the script prints as TODO and cannot do |
| `elixir/real_provenance.exs` | Checks every file under `elixir/real/` against `MANIFEST.json`: an edited copy, a file with no entry and a landed file `check.sh` does not translate all fail; an origin that is not on this machine is skipped, an origin that moved on upstream is reported (`--strict-origin` makes it fatal). `check.sh` runs it first |
| `elixir/real_manifest.exs` | The manifest module the three scripts share (defines a module, runs nothing) |
| `elixir/test/land_real_test.exs` | Self-test: runs the landing tooling against a scratch repository under `$TMPDIR` and removes it, checking the copy, the generated Lean against the committed `Gen/TableRegistry.lean`, the two `check.sh` lines, the two imports, the skeleton, idempotence file by file, and four failure paths |
| `elixir/to_lean.exs` | The translator: `@type`-directed (`msg`, `cast`, `info`, `call`, `reply`, `state`), small subset, unverified; `handle_continue` is inlined, not sent; the pure fragment is compiled as a language, so any sub-expression may be an `if`, a `case`, a block or a binding (pipes, `cond` and `unless` are desugared away first), module-local helpers become Lean definitions, and one `@remote` table says what each standard-library call becomes |
| `elixir/test/run_fixtures.exs` | Translator regression runner: translates every `test/fixtures/*.ex`, diffs against `test/expected/*.lean`, compiles the ok ones with `lake env lean`, checks the error ones fail as declared; `--regen` rewrites the expectations |
| `elixir/test/fixtures/*.ex` | 81 small sources, one translator feature each (57 `expect: ok`, 24 `expect: error`); directives in the leading comment block |
| `elixir/test/expected/*.lean` | Their expected translations, committed; regenerate with `elixir/test/regen_expected.sh` and review the diff |
| `elixir/bank.exs` | Driver: casts plus two clients blocking in `GenServer.call`; checks the trace matches Lean |
| `elixir/lock.exs` | Driver: clients block in `GenServer.call` under chaos ticks; event log checked for overlapping critical sections |
| `elixir/supervisor.exs` | Driver: crashes the worker on the BEAM and checks the supervisor survived and restarted it |
| `elixir/task.exs` | Driver: one job completes, one worker crashes; the caller clears both |
| `elixir/watchdog.exs` | Driver: hangs the worker, lets the timeout kill it, checks the replacement is running |
| `elixir/ttl.exs` | Driver: put, get, let the TTL expire, get again, a reader asks, then `put 0` and the cache dies with `ArgumentError` |
| `elixir/registry.exs` | Driver: two clients claim names through a blocking call, one crashes and its DOWN frees the name, unregister and re-claim |
| `elixir/feed.exs` | Driver: a publisher broadcasts three posts over the local PubSub twin, one subscriber leaves, two more posts; states and the subscriber list checked against Lean's `script` |
| `elixir/ringlog.exs` | The BEAM twin of `Examples/Ringlog.lean`: pushes past the cap, reads every entry and the entries of one level |
| `elixir/table_registry.exs` | Driver: the real module with real ETS tables, one per team, re-create gives a fresh reference, delete is idempotent, the rescue keeps the registry alive |
| `elixir/readiness.exs` | Readiness harness: runs the translator dry and walks each module's AST against an allowlist, reporting every unsupported construct with file, line and kind; `--markdown` writes `docs/readiness.md`, `--strict` is `check.sh`'s self-check over `elixir/src`, `--json --update-baseline` writes `docs/readiness-baseline.json` and `--check-baseline` re-measures and fails on a regression; every module gets a *distance*, the number of distinct blocker families it still hits |
| `docs/readiness.md` | Generated readiness report over the lib trees of loom, ensemble, blinks_backend, big_bill and bobs_broadcast |
| `docs/readiness-baseline.json` | The same numbers per project as `check.sh` reads them; the gate fails on a regression and prints the refresh command when a round beats them |
| `elixir/fuzz.exs` | Differential fuzz: seeded random scripts replayed in Lean (the `replay` binary) and on the BEAM (the real modules in `elixir/src`), observables compared byte for byte; `--seed S --only N` reproduces a failure |
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

**`handle_continue`.** On the BEAM `{:noreply, s, {:continue, x}}` and
`{:reply, r, s, {:continue, x}}` run `handle_continue(x, s)` before the
next mailbox message is looked at, so a continue is not a message, and a
self-send would be wrong: it would queue behind whatever the mailbox
already holds. The translator inlines it. The clause is rewritten before
translation: the first `handle_continue` clause whose argument pattern
matches `x` (decided from the source; `x` is an atom or a tagged tuple,
the pattern's literals are compared and its variables bound) is spliced
in after the clause's own sends and its reply, with the continue clause's
argument and state patterns bound to `x` and to the new state (a variable
takes the whole state; a tuple of variables binds positionally to a tuple
literal, or to the fields of the clause's whole-state variable, which the
rewritten clause then destructures, pruning unused fields to `_`). The
inlined body's tail becomes the clause's tail and may time out, stop, or
continue again, up to three deep. Effects keep the BEAM order: the
clause's sends, the reply, the continue body's sends. A guard on
`handle_continue`, a literal in its pattern against a non-literal `x`, a
body variable that shadows a clause variable, no matching clause, and a
chain deeper than three are errors; `@type continue` is accepted and
generates nothing (a continue never enters a mailbox). The fixture
`continue.ex` shows a chain (`{:fetch, k}` continues into `:warm`), a
branching continue body whose reply is pushed into both branches, a state
pattern bound to the fields of the whole-state variable, and a continue
that times out; `error_continue_deep.ex` is a continue loop.

**Reply with timeout, stop with reply.** `{:reply, r, s, t}` sends the
reply and then arms the untimed self-timer for `:timeout`, exactly like
`{:noreply, s, t}`; `t = :hibernate` in either form is no timeout and
nothing the model can see. `{:stop, reason, r, s}` from `handle_call`
sends the reply and then exits with the reason (`:normal` stays `normal`,
`:kill` is `kill`, anything else is `error`). Fixtures `reply_timeout.ex`
and `stop_reply.ex`; `stop_kill.ex` also pins `exit(:kill)` from a
GenServer callback as `.exit .kill`, like `{:stop, :kill, s}`, and
`process_exit.ex` pins `Process.exit(p, :normal)` as `.signal p .normal`.

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
is the example: `explore` visits 16,093 configurations at depth 7 with 3
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
`cache` pid 0. Registration is still static: no registry, no races. (The
registry example is an ordinary GenServer holding a map of names to pids;
it is not the BEAM's name registry, and `Reg` itself is a constant pid.)

**Exceptions.** A body whose last statement is `raise ...` or `throw ...`
(any arguments) exits the process with reason `error` and the state
unchanged, exactly like `exit/1`: an uncaught exception kills the process
and its links and monitors fire. A `raise` or `throw` anywhere else, and
any `rescue`/`catch`, is still a hard error. `ttl.ex` uses it: `{:put, 0}
-> raise ArgumentError, ...` is the clause `| _, _, .cache v, .put 0 =>
(.cache v, [.exit .error])`.

**Maps.** A `@type ... :: %{K => V}` (exactly one pair) is the
association list `List (K × V)` of `Leanactors/AssocList.lean`, imported
by the generated file when a map type occurs: `%{}` is `[]`, a literal
`%{k => v, ..}` a list of pairs, `Map.get/2` and `Map.fetch/2` are `get?`
(an `Option`, used as a `case` scrutinee with `nil`/variable arms or
`{:ok, v}`/`:error` arms, or at an `Option` position), `Map.get/3` is
`getD`, `Map.put` is `insert` (replace the first pair at the key or
append), `Map.delete` is `erase`, `Map.has_key?`/`is_map_key` are
`hasKey`, `map_size` is `size`, `Map.keys`/`Map.values` are
`keys`/`values`, and `Map.filter`/`Map.reject` with a literal `fn {k, v}
-> e end` are `filter`/`reject`. The map's type is the expected type or
the type of the map variable, so with no expected type the argument must
be a pattern-bound variable. A map pattern with literal keys, optionally
`= m` to name the whole map, is a variable plus guards (`_` is `hasKey m
k`, a literal or an already-bound variable is `get? m k = some v`) and a
fresh value variable is bound by a `match get? m k with` around the body,
falling through to the next clause like a failing guard; a variable key
is a translator error (`error_map_key_var.ex`). Enum keys get
`DecidableEq` for free. A named `@type` whose alternatives mix atoms and
tagged tuples (`@type reply :: :ok | {:error, err()} | {:found, pid()} |
:not_found`) becomes a generated inductive (`Reply`), which the registry
needs because a file has one reply type. After a blocking call the rest
of a body may be a single `if`/`case`. `AssocList` assumes nothing about
key uniqueness: `get?` finds the first pair, `insert` replaces the first,
`erase` and `reject` drop every match, and the lemmas hold for any list.
The registry (`elixir/src/registry.ex`, `Examples/Registry.lean`) is the
example: `checkInv` (every registered pid alive and monitored, or its DOWN
queued, or the DOWN in the registry's mailbox) holds on 19,677
configurations at depth 7 with 3 stimuli; the mutant that forgets
`Process.monitor` is caught by `checkInv` in 10 configurations and by the
weaker `nameNotLost` in 2,052 (claim `a`, register, crash: `a` maps to a
dead pid with no DOWN coming). The fixture `maps.ex` covers every `Map.*`
form. The full invariant proof would follow `TaskProof.lean` with
`mem_insert`/`mem_erase`/`mem_reject` in the run case
(`register_monitors`, `entry_of_run` are the two run-case facts so far).

**Structs, `Enum` and `:queue`.** `defstruct f: d, ..` with `@type t ::
%__MODULE__{f: T, ..}` becomes a Lean `structure` whose fields carry the
defstruct defaults, so `%Mod{f: e}` is `({ f := e } : Mod)`, `x.f` is the
projection and `%Mod{f: p}` a pattern on the anonymous constructor. When a
GenServer's `@type state` is its own struct — the shape of a real Phoenix
`LogStore` — the struct is flattened into that module's state constructor,
one Lean field per defstruct field: `state.f` is the part the clause's
pattern bound to `f`, and `%{state | f: e}` rebuilds the constructor with
the named parts replaced. Nothing else in the translator changes, which is
the point of the flattening: field coverage, the crash clauses, the
whole-state alias and the hidden `gen` field of a receive loop all keep
working. `Enum` over lists is the `List` API
(`filter`/`map`/`reject`/`count`/`any?`/`all?`/`member?`/`reverse`/`take`/`drop`/`at`/`empty?`,
`length`, `hd`/`tl`, `++` and the comprehension `for x <- l, c, do: e`),
with `fn x -> e end` and the capture `&(&1.f == v)` as Lean lambdas; `hd`
is `List.headD` at the element type's default, because it raises on the
BEAM and an expression in the model cannot. An Erlang queue is the list,
oldest first: `:queue.in` appends, `{_, q} = :queue.out(q0)` is `let q :=
List.tail q0`, `:queue.to_list` is the identity and `case :queue.out(q)`
matches head and rest at once. A local binding `v = e` is a Lean `let`
around the clause's result (a binding that reuses a name the clause
pattern already bound — `refs = Map.put(refs, k, v)` — is substituted at
its uses instead, because a `let` would shadow the part the rest of the
clause reads). The ring buffer (`elixir/src/ringlog.ex`,
`Examples/Ringlog.lean`) is the example; its `count_invariant` is proved
the cheap way, by `ok_step` for one behaviour step plus `beh_no_spawn` and
`SysStep.stateOf_spawn_cases`.

**PubSub.** A `Sys` carries `subs : List (String × Pid)`, subscriptions
oldest first. `Effect.subscribe q t` appends, `Effect.unsubscribe q t`
filters, and `Effect.broadcast t m` is one `deliverAll` of `m` to every
subscriber of `t` in subscription order, so a broadcast changes no state
and adds one mailbox copy per subscription; a death drops the dead pid's
subscriptions. The subscriber pid is explicit in the effect because a
`Phoenix.PubSub.subscribe` inside `init/1` belongs to the child, whose pid
is `fresh` at the parent's spawn site — which is also why a module that
subscribes in `init/1` and that nothing in the file spawns is a warning:
there is no spawn site to hang the effect on. Topics are strings, resolved
by the translator from a literal or a string-valued module attribute; a
computed topic is an error. `Sys.Grows` and `Sys.Frame` were deliberately
not extended with a `subs` clause, because an `unsubscribe` shrinks the
list: monotonicity is stated separately under `Effect.keepsSubs`, and
`SysStep.mem_subs_cases` (every subscription in a reachable system is an
old one or a `subscribe` effect of the message just popped) is the
induction workhorse.

**Untyped mode.** A module that declares no `@type` has its declarations
inferred from its own source before anything else runs, so every decision
downstream is still type-directed. Message unions come from the
`handle_cast`/`handle_info`/`handle_call` clause patterns (a tag at the
arity it is matched with, the callback fixing the kind) and from the
literal messages the module sends that nobody handles; the reply type from
every `{:reply, r, _}` in the file when all of them are literal atoms or
tagged tuples (a tag at two arities, `:ok` and `{:ok, ref}`, names the
tuple form `ok1`), and `term()` otherwise; the state from the literal of
`init/1`, where a map with atom keys is a record. Every inferred field is
`term()`, rendered as the opaque `Term` of `Leanactors/Term.lean`, which
carries a number and nothing else: enough for `DecidableEq`, which every
map key needs, and for fresh references. A `@type` declaration, where
there is one, refines those fields exactly as before — which is what
gradual typing means here, and why the eight annotated sources translate
byte for byte.

**Record-shaped state.** A `@type state` or an `init/1` literal `%{k: e,
..}` with atom keys becomes one `St` constructor with *named* fields. A
whole-state variable binds the fields the body reads (`state.f` is the
field, `%{state | f: e}` rebuilds the constructor with that field
replaced, a bare `state` is the whole constructor) and the others are `_`;
a map pattern `%{f: p, ..} = state` binds the named fields to their
sub-patterns. Those are real Lean patterns, unlike an association-list map
pattern, which is a variable plus inlined guards — a difference the
clause-subsumption test had to learn, because it had been treating a
record state pattern as a bare variable and dropping the later general
clause as unreachable, silently turning an ignore into an exit.

**External resources.** `:ets.new(..)` on the right of a binding is a
fresh opaque reference. The state gets a hidden trailing counter (`ets :
Nat`) like the after-timer generation, the k-th table a body creates is
`Term.mk (ets + k)`, and the continuing state advances the counter.
`:ets.delete(ref)` and the `try .. rescue .. end` around it are dropped
before translation: what happens inside ETS is not modelled at all, so
what is proved about the table registry is a property of its map of
references, not of ETS. A `try` with any other body is an error. Public
`def`s that are not callbacks (the module's own API wrappers around
`GenServer.call`, `raise` included) are not translated; the generated file
names them in a comment. This is the price of taking a real file as it
stands, and the BEAM driver (`elixir/table_registry.exs`) covers the other
direction by running the real module against real ETS tables.

**Control flow and expressions.** The pure fragment is compiled as a
language rather than recognised as a body shape. Any sub-expression may be
an `if`, a `case`, a block `(a; b; c)` or a binding: a block is nested
`let`s, `x = e` is `let x := e`, and `some`/`none` is inserted per branch
rather than around the whole form. Before anything else looks at a module,
a desugaring pass rewrites `a |> f(b)` to `f(a, b)`, `cond` to nested
`if`s and `unless` to `if`, so nothing downstream ever sees a pipe. The
constraint that shapes the rest is totality: Lean's `let` has nothing to
fall through to, so a pattern binding is accepted only when the pattern is
total at its type (a variable, `_`, a pair at a product type, a struct
pattern) and `{:ok, v} = Map.fetch(m, k)` is a clear error telling you to
match instead; a `cond` must end in `true ->`, because falling off the end
raises `CondClauseError` and an expression in the model cannot raise; an
`if` with no `else` is `nil`, which the model has only at an `Option`
type. The Kernel type tests fall out of the same discipline from the other
side: a value of the model has exactly one type, so `is_pid` on a `pid()`
is the constant `true`, and where the test is genuinely undecidable — an
opaque `Term`, a tagged union with both atom and tuple alternatives — the
translator says so rather than guessing. `elem/2`, `tuple_size/1`, `abs`,
`min`, `max`, `div`, `rem`, `in`, `&&`, `||`, `!`, `*`, `===`, `!==` and
unary `-` are supported on the types the model has (`div`/`rem` on
`non_neg_integer()` only: Elixir's `div` truncates toward zero and Lean's
integer division does not). A statement with an effect before an
`if`/`case` body is now pushed into every branch — its effect prepended to
whichever leaf runs — instead of being refused.

**Values and remote calls.** Elixir binaries are Lean `String`s: a
`String.t()` or `binary()` in a `@type`, a string literal, `<>` as `++`, a
literal string pattern, and an interpolation `"a#{e}b"` as `"a" ++
Str.toStr e ++ "b"`. `Str.toStr` is the `ToStr` class of
`Leanactors/Str.lean`; its instances for `String`, `Nat`, `Int` and `Bool`
are the BEAM's own rendering and everything else goes through a derived
`Repr`, which is deterministic but is not what `to_string` would print, so
no property should depend on the bytes of an interpolated string. A
keyword list is the association list `List (Atom × V)` over an `Atom`
inductive the generated file builds from the keys used, so `Keyword.*`,
`Access.get/2` and `opts[:k]` are the same `AssocList` a map is. A
`MapSet` is a duplicate-free list in insertion order
(`Leanactors/SetList.lean`); its `to_list` is in that order and not the
BEAM's term order, the one place the model is coarser than `MapSet`. A
module name used as a value becomes a constant of a generated `Module`
inductive, so it can be stored, sent and compared. Time is not modelled at
all: `DateTime.utc_now/0`, `System.monotonic_time/1` and their neighbours
are the single opaque `Instant.now` of `Leanactors/Time.lean`, which has
equality and nothing else — ordering or subtracting two instants is
refused with a message saying the model has no clock, rather than modelled
wrongly. And logging is not an effect: every `Logger` call is dropped,
arguments included, before anything is translated, which is why a
`Logger.info("x #{y}")` needs no string support at all. Standard-library
calls are one table: `@remote` at the top of `elixir/to_lean.exs` maps a
module, function and arity to what the call becomes — a rendering, `:noop`
(dropped) or `{:error, why}` (refused, with the reason). Teaching the
translator another standard-library function is adding a row.

**Module-local functions and `init/1` statements.** A `def`/`defp` that is
not a callback and that a callback reaches, directly or through another
helper, becomes a Lean definition emitted before `beh`, named
`<module>_<function>`; a call to it renders as a call. Its body must be in
the pure fragment above. A helper that sends, spawns or logs has no effect
the model could carry, so it is an error naming the helper — once, not
once per call site. Argument and result types come from a `@spec` when the
module gives one and otherwise from the types the helper is called at,
inferred over three rendering rounds, with the definition fixing its own
result type before any use does. A helper that recurses on the tail of a
list argument is an ordinary `def`; any other self-recursion takes a
leading `fuel : Nat`, returns its result type's default at zero, and is
called with the constant `localFuel` (64), which makes it an
approximation of the Elixir function beyond that depth and says so in the
generated file. Mutual recursion is an error naming both. `init/1` may now
be a block: `Process.flag(:trap_exit, true)`, a PubSub subscribe, a
`Logger` call (dropped), a call to a local helper, and bindings `v = e` of
pure expressions, which are substituted into the state expression, since
`init/1` has no Lean binder of its own — the state is built at the spawn
site. The option list a real `init/1` is handed is not modelled: a
parameter used as one is the empty keyword list, so `Keyword.get(opts, :k,
d)` is its literal default and the translator warns (the same rule now
reads a registered name out of `name: Keyword.get(opts, :name,
__MODULE__)`). And a module with neither `@type state` nor an `init/1` to
infer one from reads the shape off its callbacks' state patterns: a map
pattern anywhere makes it a record whose fields are the keys the patterns
match and the keys the bodies update or return, tuple patterns of one size
make it positional, and patterns that only bind the state whole leave it
the opaque `Term`.

**Translator fixtures.** `elixir/test/fixtures/*.ex` are 81 small
sources, one translator feature each: guard fallthrough and deferral,
nested and pattern-LHS blocking calls, deferred replies, spawn and
monitor, tuple `init`, DOWN and EXIT typing, timeouts, `send_after`,
`Process.exit` with `:kill`, `:normal` and other reasons, self-exits
with `:kill`, `handle_continue` inlining (chained, branching, binding
the whole-state variable's fields), reply with a timeout, stop with a
reply, `receive ... after` with its generation counter, declared
`@type cast`/`@type info` kinds, registered sends, keyword-named
variables, booleans, wildcards, pid narrowing, `case`/`if`, non-linear
patterns, enum and list splits, the crash clauses, maps (every `Map.*`
call, map literals and patterns with an alias), structs, `Enum` over
lists, `:queue`, PubSub (including a root module that subscribes with no
spawn site), untyped mode, a record-shaped state and ETS resources, a
reply type probed from the clause bodies, LiveView assigns and a chain of
them folded into one record update, a `defp` receive loop, and sixteen
sources the translator must reject (no pid mapping, unknown tag, a
tag in two callback kinds, a tag declared under two kinds, a clause of the
wrong declared kind, trapping without `{:EXIT, ...}`, a `handle_continue`
chain deeper than three, a map pattern with a variable key, a struct field
that does not exist, a capture with more than one argument, a computed
PubSub topic, a `try/rescue` that is not a resource no-op, an assign with
a computed key, the same key assigned twice in one chain, a `nil`
comparison at a type that is not an `Option`, a receive loop called
outside tail position). Each
fixture's leading comment block carries its
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
`SysStep.noKillTo` and `SysReach.noKillTo_of_no_signal`. Round 5 added
the `timers` group (`timers_applyEffect_append` up to
`runE_timers_append`, `signalE_timers`, `downE_timers`: a run only appends
timers and a death keeps them, signals and DOWNs leave them alone), which
both timer-driven liveness proofs rank with. `SysProps.lean` is 1,437
lines.

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
counts and witnesses as their deleted local copies. `Ttl.lean` calls
`exploreWith` with per-pid environment messages (`put 0`/`put 1` to the
cache, `ask` to the reader) and counts 16,093 configurations where its
deleted local explorer counted 16,723: the 630 dropped ones were
environment deliveries to the dead cache after a `put 0` crash, which
`Config.deliver` makes a no-op and the generic explorer does not offer
(it only stimulates live pids); the store-0 mutant witness is
byte-identical. `Lock.lean` keeps a local explorer (its core is
`Config`, not `Sys`).

**Differential testing.** The interpreters `run` and `runSys` are also
tested against the BEAM. `Leanactors/Replay.lean` is an executable that
replays a script of scheduler choices (environment deliveries, actor
runs, signal, DOWN and timer firings) on one example from its own `init`
and prints the observable part of the final configuration;
`elixir/fuzz.exs` generates such scripts at random from a seed and a run
number, replays each through the binary and drives the same messages
into the real modules of `elixir/src`, and compares the two outputs byte
for byte. The BEAM has its own scheduler, so a script whose result
depends on the interleaving would compare an interleaving Lean took with
one the BEAM may not have taken; the generator therefore builds scripts
only from *phases* that have a single outcome under any scheduling, one
target per phase, and the BEAM twin waits for the causal end of each
phase before the next (`:sys.get_state` queued behind the message, a
receive trace on the reader or the lock server, a DOWN). Bank: casts,
ticks, audits and a second tick arriving during a blocking call
(deferred, served after the reply). Ttl: puts, asks, the live timer
expiring (a real 300 ms sleep with no message in between), `put 0`
killing the cache; a stale timer firing is replayed in Lean only, since
the BEAM cancelled it, which is the over-approximation of section
**`receive` with `after`** made visible. Lock: ticks to three clients,
expanded by a simulation of the protocol into the Lean cascade plus the
exact messages the server will receive, with at most one deferred tick
per waiting client. Observables: the bank's balance, each client's last
seen value and pending messages; the cache's value, the reader's count,
every value the reader received and pending; the lock's holder and
queue, each client's phase and pending. Where the two sides legitimately
differ (untimed timers, real time, scheduling), the generator is
constrained rather than the comparison relaxed; a mismatch after a
measured stall of the driver is retried and counted. Mutants of the BEAM
modules (a withdraw off by one, a `get` ignored, LIFO grant) are caught
within the first runs. `check.sh` runs `elixir elixir/fuzz.exs --seed 1
--runs 200` (67 bank, 67 ttl, 66 lock scripts, about 14 s).

**Fair runs (`Leanactors/Fair.lean`).** Safety theorems quantify over
`Reach`/`ReachEnv`/`SysReach` and say nothing about what *must* happen.
`Fair.lean` adds infinite runs. A `CRun beh env` (`Config` layer: actor
steps interleaved with an environment relation such as the lock's
`EnvStep`) or a `SysRun beh sig` (`Sys` layer: `run p`, `signal`,
`down`, `timer i`) is a sequence of configurations `st : Nat → _`
together with the choice taken at each time, `ch t : Option _`, where
`none` is an idle step: the state repeats. Idle steps are what make every
finite execution an infinite run, so a theorem over runs is never
vacuous (`CRun.idle`/`SysRun.idle` are the constant runs); a closed
`Sys` in which nothing is enabled, the supervisor once its worker has
nothing to do, has no other infinite run. Weak fairness of a choice,
`ρ.WeakFair c`, says the choice is disabled infinitely often or taken
infinitely often: an actor with a message waiting is not ignored forever,
a pending exit signal is not left in the queue forever, and a run cannot
idle forever while something is enabled. `ρ.EnvFair P e` says that if
`P` holds from some time on, the environment eventually takes an
`e`-step. The temporal vocabulary is `Eventually`, `Always` and `LeadsTo`
(with `trans`, `mono`, `or` and `rank_induction`, well-founded leads-to
over a `Nat` measure), and two workhorses proved once over any
`ρ : Nat → α`: `stable_until` (from a stable predicate, a fair choice
establishes the goal) and `rank_leads_to` (a measure that never increases
while the goal is pending and strictly drops at every fair-taken step).
The layer wrappers (`CRun.stable_until_run`/`stable_until_env`/
`rank_leads_to_run`/`rank_leads_to_env`, `SysRun.stable_until`/
`rank_leads_to`) take state-level hypotheses that need only hold on
configurations reachable from `ρ.st 0` (`ReachE`, `SysReach`), so the
safety invariants plug in unchanged. `SysReachEnv` is `SysReach` plus
arbitrary environment deliveries, the systems the environment can drive
a closed `Sys` to. Round 5 added the open `Sys` layer: a `SysRunE beh
sig env` takes at each time a system choice or one step of a relation
`env` (`Sys.Deliver`, any message to any pid, for the examples), with
`SysReachE`, `EnvFair`, the same four workhorses
(`stable_until_sys`/`_env`, `rank_leads_to_sys`/`_env`) and `SysRun.toE`
embedding a closed run as one that never takes an environment step; the
task's live-worker theorem is stated over it. Timers live in a list whose
indices shift when an earlier one fires, so `WatchdogLive` defines
`SysRun.TimerFair to m` (a pending `(to, m)` timer eventually fires) and
derives it from `∀ i, WeakFair (.timer i)`; `TtlLive` needs only
`WeakFair (.timer 0)`, the oldest pending timer. `FairDemo` at the end of
the file is a two-state sanity check.

The translator is unverified and supports a small subset (see its header).
The equivalence theorem is what makes that acceptable: if the translation
is wrong, `beh_eq_gen` fails to typecheck.

## Readiness

`elixir elixir/readiness.exs PATH...` answers "what would it take to
translate this file?" for any Elixir source, where `PATH` is a `.ex` file
or a directory. For every module that uses `GenServer` or contains a
`receive` it runs the translator with its output discarded (retrying with
`--pid` when the only complaint is an unregistered send target, or with
`--pubsub` when a PubSub goes by another name, since both are
configuration rather than constructs) and, independently, walks the
module's AST against `@supported`, an allowlist at the top of the harness
that mirrors the header of `elixir/to_lean.exs`. The walk is what makes
the report complete: the translator stops at its first error, while the
walker reports every unsupported construct with its file, line and a
stable kind (`Map.merge/2`, `pipe |>`, `string interpolation / binary`,
`call to a helper in the same module`). Findings are blockers or notes — a
note is something the translator ignores silently, or that only needs a
flag, or that untyped mode now infers. `--markdown` renders the report as
`docs/readiness.md`, `--strict` exits non-zero if any candidate module is
not translatable, and `check.sh` uses that over `elixir/src` so a
translator change that narrows the subset is caught. The walker types
nothing, so a construct the translator rejects for a type reason alone is
not reported; kinds are meant to be read by frequency, not as a proof.
Cross-checking it against the fixture corpus is what keeps it honest: no
`expect: ok` fixture is flagged, and the walker independently catches 14 of
the 24 `expect: error` fixtures (the other ten are kind and type errors
the walker does not model).

`docs/readiness.md` is that report over the lib trees of five real
applications: 373 files, 55 GenServer or receive-loop modules, 738
blocking constructs in 188 families, grouped both by kind and by the
translator feature each group would need. It also carries a generated
**Landed** section: every file under `elixir/real/` with the project and
path it came from, its length, and whether it has a hand model proved
equal to the translation, a bounded check and a proof. Those three
columns are read off the Lean files, so that table cannot drift from the
tree. Round 6 took that from 2,838 to
1,621 and made `Loom.Teams.TableRegistry` the first real module the
harness reports as translatable — the same module
`Leanactors/Examples/TableRegistry.lean` proves its properties of. Round 7
took it from 1,621 to 848, roughly halving it. Twenty-three families left
the table outright: every string literal (147) and interpolation (85),
every keyword list (67), every `Logger` (40), `Keyword` (37), `Access`
(24) and `MapSet` (11) call, every pipe (38), `cond`, `&&`, `||`, `in`
and `<>`, every `if`/`case` below body level (98) and every plain binding
(36). Twelve narrower families replaced them, which is the point of the
exercise: `call to a helper in the same module` (271 occurrences in 41
modules, the largest family in the round-6 report) is now `local helper is
not a pure expression` (242/40), which names a helper and the construct
that stops it instead of naming a call site. That is what leads the
remaining table, ahead of imported and macro calls (144/17, 123 of them
Phoenix `assign/2` and `assign/3`), `Enum` calls (24/14), an `if`/`case`
used as a statement with its value discarded (23/12) and message patterns
that are neither an atom nor a tagged tuple (22/9). The round is planned from that
table rather than from guesses.

Those numbers are committed as `docs/readiness-baseline.json`, and
`check.sh` re-measures the five projects and fails if any of them
translates fewer modules or carries more blockers than the baseline
records, naming every module whose verdict changed; a run that *beats* the
baseline prints the refresh command and passes, and a machine without
those checkouts skips the step rather than failing it. The report also
ranks the untranslatable modules by *distance* — the number of distinct
blocker families each still hits, which is what a round can plan against.
Round 8 emptied the top of that list — `Ensemble.LogStore`,
`EnsembleWeb.LogsLive` and `BobsBroadcastWeb.RadioLive` are landed — and
in doing so changed what the list *means*. A blocker found inside a
module-local helper used to be filed under `local helper is not a pure
expression`, which reads as though the translator were one feature away;
it is now filed under the family of what the helper actually calls, and a
module's distance counts every family inside it. `LoomWeb.TeamCostComponent`
read distance 2 and is really 8; `EnsembleWeb.SentryLive` read 2 and is
13. The blocker *count* is deliberately left on the old definition (one
blocker is one helper, call sites collapsed) so the round-to-round series
stays comparable, and the three modules now at distance 1 —
`BigBillWeb.SearchLive`, `Loom.LSP.ConfigListener`,
`LoomWeb.CostDashboardLive` — are each waiting on a call into another
application module (a SQLite full-text index, a `DynamicSupervisor` that
starts a child per config entry, four `:ets` reads of another process's
table), not on a language feature. That is a model question, not a
translator one.

### Landed modules

Four of the thirteen worked examples are modules copied verbatim out of
the projects the readiness report measures, translated as they stand with
no annotations and no edits. The generated **Landed** table in
`docs/readiness.md` is the machine-checked version of this list; what each
one exercises is:

* **`Loom.Teams.TableRegistry`** (loom, `lib/loom/teams/table_registry.ex`,
  69 lines) — untyped mode end to end, ETS tables as fresh opaque
  references with a hidden counter, and a `try/rescue` whose body is only
  `:ets` statements. It is the one with a full reachability proof
  (`Leanactors/Examples/TableRegistryProof.lean`).
* **`Ensemble.LogStore`** (ensemble, `lib/ensemble/log_store.ex`, 94
  lines) — a reply type that no declaration gives you. The only reply is
  `:queue.to_list(state.entries)`, so the file is compiled twice: once to
  find out what the replies are, once to use it. Also a struct state
  flattened into the state constructor, `:queue` as the list, and a
  PubSub broadcast on every push.
* **`EnsembleWeb.LogsLive`** (ensemble, `lib/ensemble_web/live/logs_live.ex`,
  432 lines) — the LiveView socket as the record of the assigns the
  callbacks touch, and a file whose whole translated part is one
  `handle_info` clause (the other is the catch-all that ignores everything
  else, which is already the BEAM's default). The rest is `mount/3`,
  `render/1`, three `handle_event/3` clauses and twenty-one private
  helpers, and the generated file names which of those is a real
  transition it does not carry.
* **`BobsBroadcastWeb.RadioLive`** (bobs_broadcast,
  `lib/bobs_broadcast_web/live/radio_live.ex`, 78 lines) — a chain of
  assigns folded into one record update, and a payload inferred
  `term() | nil` from the `!= nil` the body writes about it.

`elixir elixir/land_real.exs <path to the module>` does the mechanical
part of adding one: translate at the original path, copy in and verify
byte-identical, generate the Lean, append the `check.sh` lines, write an
example skeleton, add the imports, record the origin and its md5. What it
will not do is invent a property — the skeleton's `beh` is the generated
clauses copied, so `beh_eq_gen` holds at once and says nothing. Rewriting
it into a readable hand model, with `beh_eq_gen` keeping that honest, and
writing a bounded check of something actually true of the module, is the
part that matters and the part the script prints as TODO.

## Build

```sh
./check.sh              # check every elixir/real/ copy against its origin, regenerate Gen/,
                        # verify it is unchanged, run the translator fixtures and the landing
                        # tooling's self-test, the readiness self-check over elixir/src, the
                        # readiness regression gate over the five real projects, lake build
                        # (proofs, checkers, the replay binary), run the ten drivers,
                        # then the differential fuzz (200 seeded scripts)
```

`./check.sh` is the CI-shaped version: it stops at the first failure. `./verify`
(`elixir/verify.exs`) runs the exact same tools but keeps going, and renders
whatever they printed as a source frame — file, line, a caret, and, for the
Lean diagnostics it recognises, a plain-English note — instead of a raw
`file:line:col:` string:

```sh
./verify                    # every stage: translate, fixtures, prove, run
./verify translate prove    # only these stages
./verify --no-color         # plain text (also respects NO_COLOR)
```

or piecewise:

```sh
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > Leanactors/Gen/Lock.lean
elixir elixir/to_lean.exs elixir/src/ttl.ex Leanactors.Gen.Ttl > Leanactors/Gen/Ttl.lean   # names derived from the source
elixir elixir/to_lean.exs elixir/src/registry.ex Leanactors.Gen.Registry > Leanactors/Gen/Registry.lean
elixir elixir/test/run_fixtures.exs         # 81 translator fixtures; --regen rewrites the expectations
elixir elixir/readiness.exs elixir/src      # what the translator would need for a given source tree
lake build              # checks every proof, runs the bounded checkers, builds .lake/build/bin/replay
elixir elixir/bank.exs  # exits 1 on mismatch with the Lean trace
elixir elixir/lock.exs 20 20000   # exits 1 if two clients ever hold at once
elixir elixir/ttl.exs   # exits 1 unless put 0 kills the cache and the expiry matches the model
elixir elixir/registry.exs        # exits 1 unless a crash frees the name and a re-claim succeeds
elixir elixir/fuzz.exs --seed 1 --runs 200   # Lean replay vs BEAM; --only N reproduces one script
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

**Liveness.** Five properties of the form "something must happen", all
proved along fair runs (`Fair.lean`). The fairness assumed is weak
fairness of individual scheduler choices; in plain words, if a choice
stays possible from some point on, it is eventually taken: an actor that
has mail is eventually run, a pending exit signal or DOWN is eventually
delivered, a pending timer eventually fires. Nothing is assumed about the
order or speed of anything else, and no bound on the delay is claimed.
Every theorem below comes with a witness that its premise is reachable
from `init` and that a run satisfying all of its fairness assumptions
exists from such a system, so none of them is vacuous.

*Supervisor* (`SupervisorLive.restart_eventually`): along any `SysRun`
that starts in a `Good` system (the safety invariant `Inv` plus no
pending kill aimed at pid 0) and is weakly fair for the `signal` step
and for `run 0`, if the current child is dead at time `t` then at some
`t' ≥ t` the supervisor has a live current child. `restart_in_flight`
says the restart is on its way; this says it arrives. Two `LeadsTo`
stages by `rank_leads_to`: the pending `(0, c, _)` signal ranked by its
position in the FIFO signal queue (runs only append signals, a signal
step pops the head), then `EXIT c _` ranked by its position in the
supervisor's mailbox (every other step only appends there; `run 0` pops
the head and either spawns or leaves state 0 alone). Fairness of `down`
and of timers is not needed (no monitors, no timers). `NoKillTo 0` is
assumed of the start system as half of `Good` and preserved along the run;
`reachEnv_good` discharges it for every environment-reachable start. The theorem starts from a `Good` system rather than
from `init` for a reason worth knowing: a `SysRun` is closed (no
environment steps), and in a closed run from `init` nobody ever sends the
worker `:crash`, so a dead child never occurs and the `init` form
(`restart_eventually_init`) is vacuous. Every step and every environment
delivery preserve `Good`, so every system the environment can drive the
supervisor to is a valid start (`reachEnv_good`,
`restart_eventually_env`), and `dead_child_reachable` exhibits one with a
dead child: run 0, deliver `:crash` to the worker, run 1. The same
closedness has always been true of the `Sys` safety theorems (the
checkers explore the environment; the proofs are over `SysReach`).

*Lock* (`LockLive.eventually_holds`): along any `CRun beh EnvStep` from
`initCfg n` in which every actor's `run` step is weakly fair and the
environment is fair to holders (`EnvFair`: a client that holds the lock
from some time on is eventually ticked; nobody sits in the critical
section forever), every client blocked in `GenServer.call(Lock,
:acquire)` (`client_await0`) later reaches `client .holding`. Three
phases, each a `LeadsTo`: the request in the server's mailbox
(`rank_leads_to_run server`, measure the index of `acquire x`); queued
(`LeadsTo.rank_induction` on the FCFS rank; per rank, a four-lemma chain
moves the holder's token, grant in flight to holding by `run h`, holding
to ticked by `stable_until_env`, ticked to release in flight by `run h`,
release in flight to handover by `run server`, and the handover grants
`x` or drops its rank by one, `Step.rank_step`); and the grant in `x`'s
own mailbox (`rank_leads_to_run x`, measure the index of `reply ok`; a
blocked client defers everything else by re-enqueueing it at the tail,
so the index strictly drops). One measure family, `idxOf c q m` (the
index of the first `m` in `q`'s mailbox), serves every phase. Here the
environment does interleave with the run throughout, as `EnvStep`.

*Task* (`TaskLive.job_eventually_settles_dead`,
`TaskLive.job_eventually_settles`): `job_never_lost` says the reply or
the DOWN is always on its way while the caller waits on a dead worker;
these say it arrives. The closed form: along any `SysRun` from a `Good`
system (`Inv`, `Fresh`, and `Shape`: every pid but the caller is a
worker and the caller never waits on itself), weakly fair for the `down`
step and for `run 0`, if at time `t` the caller waits on `w` and `w` is
dead, then at some `t' ≥ t` the caller has no pending job. The open form
drops "`w` is dead", and needs the environment for it: a live worker
acts only on `compute` or `crash`, which only the environment sends, and
a closed run from a live worker may idle forever. It is stated along a
`SysRunE beh sig Sys.Deliver`, a run in which the environment may
deliver any message to any pid at any time, and assumes in addition weak
fairness of `run w` and `EnvFair (Alive w) (Kick w)`: if the caller keeps
waiting on a live, monitored `w` from some time on, the environment
eventually delivers `compute` or `crash` to `w`. Nothing else is assumed
of the environment; it may send anything to anyone in between. Four
`LeadsTo` stages: the kick arrives (`stable_until_env`), `w` pops it and
exits (rank = position of the first kick in `w`'s mailbox, fair `run
w`), the DOWN is delivered (rank = position of `(0, w, _)` in the FIFO
`downs`, fair `down`), the caller pops the reply or the DOWN (rank =
position of the first settling message in the caller's mailbox, fair
`run 0`). The closed theorem is the open one through `SysRun.toE`.
Witnesses: `dead_worker_reachable` and `live_worker_reachable` reach the
two premises from `init`; `deadRun_witness` and `liveRun_witness` are
explicit runs from those systems satisfying every fairness assumption
(the live one including `EnvFair`) that settle at times 2 and 5.

*Watchdog* (`WatchdogLive.restart_eventually`,
`WatchdogLive.worker_replaced`): the first is the supervisor's statement
for the watchdog (fair `signal` and `run 0`, a dead current worker is
eventually replaced by a live one; `Good` adds `Armed`, a watchdog that
expects a pong has its timeout pending or in its mailbox, and `ChildLt`,
the current worker is below the fresh counter). The second is the
timer-driven property: if at time `t` the watchdog is `.watchdog (some w)
true` (it has pinged `w` and waits for the pong or the timeout), then
under `TimerFair 0 .timeout`, fair `signal` and fair `run 0`, at some
`t' ≥ t` the current worker is a live pid other than `w`. `TimerFair to
m` says a pending `(to, m)` timer eventually fires; it is derived from
weak fairness of every timer index (`timerFair_of_weakFair_timers`: the
index of the first matching timer never increases, so it stabilises, and
weak fairness of that index fires it), and `worker_replaced_of_weakFair`
takes the `∀ i` form. Nothing is assumed about `w`: `hung_worker_replaced`
states the requested hypotheses (`w` alive and hung, fair `run w`) and
uses neither, because the kill is untrappable and does not need `w` to
run. Timers are untimed, so this is exactly the model's
over-approximation: along a fair run every worker the watchdog waits on
is eventually killed and replaced, hung or healthy, and no "quiet
mailbox" assumption is needed since the rank on the position of the
first `timeout` in the watchdog's mailbox absorbs any number of pongs
ahead of it. Four stages: the timeout fires (`stable_until_timer`),
`run 0` pops it and queues the kill (rank on the mailbox), the kill is
delivered (rank on the signal queue; `kill_head_dead` covers a live `w`
whatever it traps and a `w` already gone), then `restart_eventually`,
with `w` never resurrected (`ChildLt`). Witnesses: `dead_worker_reachable`
by closed steps (so even the `init` form is non-vacuous here);
`hung_worker_reachable`, an environment-reachable system with a hung
worker and the watchdog waiting on it; and `hung_fair_run`, a run from it
weakly fair for `signal`, `run 0`, every `timer i` and `run 1`, built by
`SysRun.exists_of_inv` from a five-phase invariant (timer, run 0, signal,
signal, run 0, killing worker `k` and spawning `k + 1` each cycle) rather
than written out state by state.

*Ttl* (`TtlLive.gen_advances_or_clears`): `TtlProof` says what the cache
never holds; this says what it holds does not stay. Along any `SysRun`
from a `Good` system (links and signals empty, pid 0 a cache, and
`Armed`: the timer of the current generation is pending or already in
the mailbox; the safety invariant `Inv` is not needed at all), weakly
fair for the oldest pending timer (`timer 0`) and for `run 0`, if the
cache holds `some v` at generation `g` at time `t`, then at some `t' ≥ t`
it still does and its `run 0` step at `t'` leaves generation `g` in one
of exactly three ways: the after-timer of `g` ran and cleared the value
(`.cache none (g + 1)`), a message was processed and re-armed (`.cache
(some x) (g + 1)`), or `put 0` killed the cache. `gen_changes_or_clears`
restates it as "the generation changes, or the value is cleared, or the
cache is dead"; `gen_advances_or_clears_timers` takes `∀ i, WeakFair
(.timer i)` (the watchdog's premise, one instantiation);
`value_eventually_expires` is the plain-words version: if no message is
processed at generation `g` and the cache does not die, the value is
cleared. The corollary "if the generation never changes then the value
clears" is deliberately not stated: the after body itself moves to
`g + 1`, so along a fair run the generation always changes and that
premise is unsatisfiable. Two `rank_leads_to_of_step` stages: the
generation's timer ranked by its position in `timers` (steps append or
erase one entry; erasing one ahead drops the rank, erasing ours fires
it), then `after_run g` ranked by its position in the cache's mailbox
(stale timers ahead of it are consumed with the state unchanged);
`exists_last` picks the step that leaves `g` and `cache_run_cases`
classifies it. Witnesses: `premise_reachable` (`.cache (some 5) 1` via
`put 5`, run 0, a stale timer, run 0) and `wit`, an explicit run from
that system alternating `timer 0` and `run 0` forever, fair for both,
satisfying the premise at time 0 and expiring the value at time 2
without processing a message (`fair_run_exists`, `wit_quiet`,
`wit_expires`).

**A real file, unannotated.** `Loom.Teams.TableRegistry` went in
verbatim — nothing annotated, nothing deleted, the dotted module name
included — and came out with two properties proved: a team maps to at most
one ETS table, and distinct teams never share one. What it cost is worth
naming, because it is the shape of every later real file: inference of the
declarations a `@type` would have given, one opaque type standing in for
every value the translator cannot name, named state fields, and a counter
standing in for the world outside the process. What it bought is a proof
about the registry's map of references — and the honesty to say that it is
about the map and not about ETS, which the BEAM driver covers instead.
The independent check is that `elixir/readiness.exs`, whose allowlist is
written from the translator's header rather than from its code, now reports
that same module as translatable on its own.

**Planning from data.** The readiness report is the first time the subset
has been measured against code nobody wrote for it. Two things in it were
surprises. The three blockers that hit all 55 real modules at once were
structural, not semantic — a dotted module name, no `@type state`, no
`@type msg` — which is why untyped mode was worth more than any library
call. And the library calls everyone expects to need (`Logger` 40
occurrences, `Enum` 31, `Keyword` 30, `:ets` 28, `Phoenix.PubSub` 23) are
a long tail next to the plain language forms: a variable binding, a field
access, a map update, a call to a helper in the same module. Round 6 built
what the table said rather than what the plan had guessed, and the count
of blocking constructs fell from 2,838 to 1,621.

*What is not proven.* No bound on how long anything takes (the FCFS
bound is a separate safety fact). The supervisor, watchdog and ttl
results are along closed `SysRun`s, so they cover the system's own
reaction after the environment has acted; only the task's live-worker
theorem runs with the environment interleaved (`SysRunE`), and porting
the others to it is mechanical (every stage lemma already treats a
foreign step as "only appends to my mailbox", which is what a delivery
does). The registry has no liveness statement and no safety proof yet.
Only weak fairness is defined; no proof needs strong fairness.

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
to fix its kind. Maps are association lists with one `K => V` pair per
type, literal keys in patterns, and the `Map.*` calls listed under
**Maps** (no `Map.merge`, `Map.update`, comprehensions or `Enum` over a
map). External resources are not modelled at all: `:ets.new` is a fresh
opaque `Term` from a counter and every other ETS call is dropped, so a
property proved about such a module is a property of the references it
keeps, not of the tables. Strings are Lean `String`s, but an
interpolated one is only as faithful as `Str.toStr` (a value with no
printable model goes through its derived `Repr`), so no property should
depend on the bytes of one. A clock read is one opaque `Instant`, so
nothing about elapsed time can be stated at all; ordering or subtracting
two instants is refused rather than approximated. A `MapSet` is a list in
insertion order, not the BEAM's term order. A state field a body sends to cannot be
inferred as a pid: in untyped mode it becomes a `Term`, and the mismatch
only surfaces as a Lean type error, so such a source still needs a `@type`
with `pid()`. A cons expression `[x | xs]` is unsupported, a blocking call
is not supported in a module that creates ETS tables, and `case
Map.pop`'s `{nil, _}` arm also matches a stored `nil` on the BEAM (the
model has no `nil` values). An `if`/`case` whose value is discarded, a
statement with an effect inside a block expression, and a `case` over a
comparison (`case x > 10 do true -> ..`, which renders the scrutinee as a
`Prop` Lean cannot match against `true`) are all still errors. A
self-recursive local helper that does not recurse on a list tail is
approximated beyond `localFuel` (64) applications. A LiveView's
`handle_event/3` is *not* modelled and *is* a real transition: the browser
channel is a second source of messages this model does not have, so a
property checked of a landed LiveView is a property of its mailbox alone,
which the generated file and the example both say in so many words. Environment steps inside the supervisor,
watchdog and ttl runs (`SysRunE` exists and the task uses it; the other
three liveness theorems are still over closed `SysRun`s), safety proofs
for the registry and the feed's prefix property, strong fairness, and any
real-time bound.
