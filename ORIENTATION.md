# Orientation for an agent working on this repository

One page. Read this instead of the README before you start; open the large
documents only when your own piece needs them.

## What this is

A Lean 4 model of the BEAM actor model, plus a translator that turns real
Elixir source into that model, plus proofs about the result. The claim the
whole repo defends: you can take an unmodified GenServer out of a real
project, translate it, and prove something true about it.

## The five things you must not break

1. `lake build` ends with **zero errors and zero warnings**. No `sorry`, no
   `axiom`, no Mathlib. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
2. `./check.sh` passes end to end. It regenerates every `Leanactors/Gen/*.lean`
   and fails if one differs, runs the translator fixtures, the readiness gate,
   the proofs, the BEAM drivers, and a Lean-vs-BEAM differential fuzzer.
3. Files under `elixir/real/` are **verbatim copies** of files in other
   projects. Never edit one. `elixir/real_provenance.exs` checks their hashes
   against `elixir/real/MANIFEST.json`; add a new one with `elixir/land_real.exs`.
4. Every existing generated file must regenerate **byte-identically** unless
   you deliberately improved it, and then you say which and why.
5. **Property discipline.** A bounded check tests a *state* predicate. It
   cannot express a property about a *step* or a trace (conservation, nothing
   dropped or duplicated, eventual delivery). For every property you claim,
   either ship a mutant that the check catches, or prove the property as a
   theorem. Never weaken a property into a state predicate and then describe
   it as the strong version. A round-8 audit found two checks that a
   behaviour dropping every message passed; that is the failure mode.

## Where things are

| Path | What |
|---|---|
| `Leanactors/Core.lean`, `Props.lean`, `Count.lean` | the message-only model: `Behavior`, `Config`, `Step`, counting, `Step.chars` |
| `Leanactors/Sys.lean`, `SysProps.lean` | processes: effects, spawn, links, monitors, exit signals, timers, PubSub; and the reusable metatheory (`Grows`, `Frame`, `runE_cases`, ...) |
| `Leanactors/Fair.lean` | infinite runs, weak fairness, `LeadsTo`, `stable_until`, `rank_leads_to` |
| `Leanactors/Explore.lean` | the bounded explorer (state predicates only) |
| `Leanactors/Examples/*.lean` | one file per example: hand `beh`, `beh_eq_gen`, a bounded check, sometimes a proof |
| `Leanactors/Gen/*.lean` | generated, committed, never hand-edited |
| `elixir/to_lean.exs` | the translator; its header comment is the spec of every convention |
| `elixir/src/*.ex` | sources written for this repo |
| `elixir/real/*.ex` | unmodified files from real projects |
| `elixir/readiness.exs`, `docs/readiness.md` | what fraction of real code translates, and what blocks the rest |
| `.deciduous/` | the decision graph; log your reasoning there as you work |

## How a piece of work goes

Create your worktree, create your goal node in the decision graph, then work
in small commits. **Commit a skeleton early** — an interrupted agent that has
committed nothing loses everything, and re-reading this repository is
expensive.

```sh
cd /Users/bg/code/lean_analysis
git worktree add /Users/bg/code/lean_analysis-wf/<name> -b <branch>
```

## Where the work stands

Six examples written for the repo, four unmodified real modules translated
(a table registry, a log store and two live views), safety and liveness
proofs for the core examples, and a readiness report saying which of 55 real
candidate modules translate and why the rest do not. The frontier is whole
*applications* — a supervision tree with several processes talking to each
other — rather than single modules.
