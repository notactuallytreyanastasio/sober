# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib.

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Sys.lean` | Spawn, links, exits: effects, fresh-pid counter, link list, asynchronous exit signals; `runE_lift` shows message-only behaviours are unchanged |
| `Leanactors/Examples/Supervisor.lean` | One-for-one supervisor translated from `elixir/src/supervisor.ex`; bounded checker; the no-`trap_exit` mutant |
| `Leanactors/Examples/SupervisorProof.lean` | The supervisor never dies and a missing child always has its restart in flight |
| `Leanactors/Examples/Bank.lean` | Per-actor invariant: a bank's balance never goes negative under any scheduler |
| `Leanactors/Examples/Lock.lean` | Cross-actor invariant: lock server + clients blocking in `GenServer.call`, token invariant, bounded model checker |
| `Leanactors/Examples/LockProof.lean` | The invariant is inductive; `mutex_forever` and `progress_forever` under any scheduler and any environment ticks |
| `Leanactors/Examples/LockFcfs.lean` | Bounded waiting: rank drops by exactly one per handover while queued; `fcfs` in reachable configurations |
| `Leanactors/Examples/LockMutants.lean` | Three protocol bugs: two caught with witness traces, one shown unreachable |
| `Leanactors/Gen/*.lean` | Generated from `elixir/src/*.ex` by the translator; do not edit |
| `elixir/src/bank.ex`, `elixir/src/lock.ex` | The Elixir source of truth: executed on the BEAM and translated to Lean |
| `elixir/to_lean.exs` | The translator: `@type`-directed, small subset, unverified |
| `elixir/bank.exs` | Driver: casts plus two clients blocking in `GenServer.call`; checks the trace matches Lean |
| `elixir/lock.exs` | Driver: clients block in `GenServer.call` under chaos ticks; event log checked for overlapping critical sections |
| `elixir/supervisor.exs` | Driver: crashes the worker on the BEAM and checks the supervisor survived and restarted it |

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
child's state constructor (so `Mod.init` must be the identity), binds the
pid variable to `fresh`, maps any non-`:normal` reason to `error`, types
`{:EXIT, pid(), term()}` as `EXIT (Pid) (Reason)`, and generates the
`Signals` record from which modules trap. Files without effects keep
producing a plain `Behavior`, byte for byte as before.

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

The translator is unverified and supports a small subset (see its header).
The equivalence theorem is what makes that acceptable: if the translation
is wrong, `beh_eq_gen` fails to typecheck.

## Build

```sh
./check.sh              # regenerate Gen/, verify it is unchanged, lake build, run both drivers
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

Monitors, selective `receive` beyond the call-reply encoding, timeouts,
multi-node delivery, monitors in the translator, and `GenServer.start_link`
children whose `init` is not the identity.
