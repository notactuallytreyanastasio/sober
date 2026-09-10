# leanactors

A shallow embedding of the actor model in Lean 4, used as a semantic target
for a pure subset of Elixir/BEAM programs. No Mathlib.

## Layout

| File | What |
|---|---|
| `Leanactors/Core.lean` | `Behavior`, `Config`, `Step` (relational), `step`/`run` (executable) |
| `Leanactors/Props.lean` | Frame rule, domain preservation, mailbox-queue lemma, invariant induction, `run_sound` |
| `Leanactors/Examples/Bank.lean` | A bank GenServer; proof its balance never goes negative under any scheduler |
| `elixir/bank.exs` | The same GenServer in Elixir; runs the same stimulus and checks it matches the Lean trace |

## Build

```sh
lake build            # checks every proof
elixir elixir/bank.exs  # runs the Elixir twin, exits 1 on mismatch
```

## The idea

Elixir's set-theoretic types check that each `handle_cast` clause returns the
right shape. They cannot check that a *state invariant* survives an arbitrary
interleaving of messages from many processes. Here the invariant is proven
in Lean once per handler clause (`beh_preserves`), and `Reach.preserves`
lifts it to every reachable configuration under every scheduler.

`run_sound` connects the executable interpreter to the relational semantics,
so any `#eval` trace is automatically covered by the theorem.

## Not modelled yet

Links, monitors, exits, supervisors, selective `receive`, timeouts, spawn,
and multi-node delivery. Each is a new `Step` constructor; selective receive
is the one that breaks the pop-the-head mailbox lemma.
