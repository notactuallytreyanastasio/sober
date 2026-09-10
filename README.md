# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib.

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, per-actor invariant induction, `run_sound` |
| `Leanactors/Count.lean` | Message counting, `Step.chars` (a step as arithmetic over counts), config-level invariant induction, FIFO corollary |
| `Leanactors/Examples/Bank.lean` | Per-actor invariant: a bank's balance never goes negative under any scheduler |
| `Leanactors/Examples/Lock.lean` | Cross-actor invariant: lock server + clients, token invariant, bounded model checker |
| `Leanactors/Examples/LockProof.lean` | The invariant is inductive; `mutex_forever` under any scheduler and any environment ticks |
| `Leanactors/Examples/LockMutants.lean` | Three protocol bugs: two caught with witness traces, one shown unreachable |
| `elixir/bank.exs` | The bank as an Elixir GenServer; runs the same stimulus and checks it matches the Lean trace |
| `elixir/lock.exs` | The lock as Elixir processes; chaos ticks; event log checked for overlapping critical sections |

## Build

```sh
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

**Safety here does not need FIFO.** The out-of-order case (a client's
`acquire` processed while its `release` is still in flight) is absorbed by
the equation `acquire + queued = waiting`. FIFO will matter for liveness.

## Not modelled yet

Spawn, links, monitors, exits, supervisors, selective `receive`, timeouts,
and multi-node delivery. Each is a new `Step` constructor; selective
receive is the one that breaks the pop-the-head mailbox lemma.
