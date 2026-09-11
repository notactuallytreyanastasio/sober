#!/bin/sh
# Full chain: regenerate Lean from Elixir, check nothing drifted, prove, run.
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

# a private scratch directory per run: two worktrees running check.sh at the
# same moment used to clobber each other's /tmp/Gen.<Name>.lean and report a
# drift that was not there
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

echo "== real provenance"
# Every file under elixir/real/ is a copy of a module from a real project.
# This checks each one is still byte-identical to the origin recorded in
# elixir/real/MANIFEST.json (written by elixir/land_real.exs), so "we translate
# real, unmodified code" is a checked claim and not a sentence in the README.
# An origin that is not on this machine is reported and skipped, like the
# readiness gate's project paths; an EDITED COPY always fails.
elixir elixir/real_provenance.exs --quiet

echo "== translate"
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > $OUT/Gen.Lock.lean
elixir elixir/to_lean.exs elixir/src/bank.ex Leanactors.Gen.Bank --pid Bank=bank > $OUT/Gen.Bank.lean
elixir elixir/to_lean.exs elixir/src/supervisor.ex Leanactors.Gen.Supervisor --pid Sup=sup > $OUT/Gen.Supervisor.lean
elixir elixir/to_lean.exs elixir/src/task.ex Leanactors.Gen.Task --pid Caller=caller > $OUT/Gen.Task.lean
elixir elixir/to_lean.exs elixir/src/watchdog.ex Leanactors.Gen.Watchdog --pid Watchdog=watchdog > $OUT/Gen.Watchdog.lean
elixir elixir/to_lean.exs elixir/src/ttl.ex Leanactors.Gen.Ttl > $OUT/Gen.Ttl.lean
elixir elixir/to_lean.exs elixir/src/registry.ex Leanactors.Gen.Registry > $OUT/Gen.Registry.lean
elixir elixir/to_lean.exs elixir/src/feed.ex Leanactors.Gen.Feed > $OUT/Gen.Feed.lean
elixir elixir/to_lean.exs elixir/src/ringlog.ex Leanactors.Gen.Ringlog > $OUT/Gen.Ringlog.lean
# untyped mode: no @type anywhere, no --pid flag (the name is derived from
# `GenServer.start_link(__MODULE__, opts, name: __MODULE__)`, so the Lean
# constant is `table_registry`)
elixir elixir/to_lean.exs elixir/real/table_registry.ex Leanactors.Gen.TableRegistry > $OUT/Gen.TableRegistry.lean
# untyped mode again: a ring buffer whose reply is a list (the reply type is
# probed from the clause bodies, not declared) and the LiveView that shows
# what it broadcasts (a socket modelled as the record of its assigns)
elixir elixir/to_lean.exs elixir/real/log_store.ex Leanactors.Gen.LogStore > $OUT/Gen.LogStore.lean
elixir elixir/to_lean.exs elixir/real/logs_live.ex Leanactors.Gen.LogsLive > $OUT/Gen.LogsLive.lean
# untyped mode, a LiveView again: a chain of assigns folded into one record
# update, and a payload inferred `term() | nil` from the `!= nil` the body
# writes about it
elixir elixir/to_lean.exs elixir/real/radio_live.ex Leanactors.Gen.RadioLive > $OUT/Gen.RadioLive.lean
diff -q $OUT/Gen.Lock.lean Leanactors/Gen/Lock.lean
diff -q $OUT/Gen.Bank.lean Leanactors/Gen/Bank.lean
diff -q $OUT/Gen.Supervisor.lean Leanactors/Gen/Supervisor.lean
diff -q $OUT/Gen.Task.lean Leanactors/Gen/Task.lean
diff -q $OUT/Gen.Watchdog.lean Leanactors/Gen/Watchdog.lean
diff -q $OUT/Gen.Ttl.lean Leanactors/Gen/Ttl.lean
diff -q $OUT/Gen.Registry.lean Leanactors/Gen/Registry.lean
diff -q $OUT/Gen.Feed.lean Leanactors/Gen/Feed.lean
diff -q $OUT/Gen.Ringlog.lean Leanactors/Gen/Ringlog.lean
diff -q $OUT/Gen.TableRegistry.lean Leanactors/Gen/TableRegistry.lean
diff -q $OUT/Gen.LogStore.lean Leanactors/Gen/LogStore.lean
diff -q $OUT/Gen.LogsLive.lean Leanactors/Gen/LogsLive.lean
diff -q $OUT/Gen.RadioLive.lean Leanactors/Gen/RadioLive.lean
echo "   generated files are up to date"

echo "== translator fixtures"
# `cmd | grep -v` would hide a failure: the pipeline reports grep's status, and
# grep succeeds precisely when there are FAIL lines to print. So the output is
# captured, a non-zero exit is fatal, and only then are the PASS lines dropped.
elixir elixir/test/run_fixtures.exs > $OUT/fixtures.txt || { grep -v "^PASS " $OUT/fixtures.txt; exit 1; }
grep -v "^PASS " $OUT/fixtures.txt
# and the self-test of the landing tooling: it runs elixir/land_real.exs and
# elixir/real_provenance.exs against a scratch repository under $TMPDIR and
# removes it again, touching nothing here.
elixir elixir/test/land_real_test.exs > $OUT/land_real.txt || { grep -v "^PASS " $OUT/land_real.txt; exit 1; }
grep -v "^PASS " $OUT/land_real.txt

echo "== readiness self-check"
# every module of elixir/src must still report as translatable (the same
# allowlist walk elixir/readiness.exs runs over real projects for docs/readiness.md);
# --strict exits 1 if any candidate module is not translatable.
# (pubsub.ex is the local Phoenix.PubSub twin the drivers send through, not
# a module the model translates: PubSub is an effect of Sys, not an actor.)
elixir elixir/readiness.exs --strict --exclude elixir/src/pubsub.ex elixir/src > $OUT/readiness.src.txt
grep "candidate modules" $OUT/readiness.src.txt | sed 's/^/   /'

echo "== readiness regression gate"
# Re-measure the five real projects and compare with docs/readiness-baseline.json:
# fails if any project translates fewer modules than the baseline records or
# carries more blockers, and names every module whose verdict changed. The
# paths are in the baseline, so there is no copy of the project list here; if
# they are not on this machine the step says so and passes (they are not part
# of the repository). ~15s.
#
# A round that lands translator features is expected to BEAT the baseline:
# refresh it then, together with docs/readiness.md --
#   elixir elixir/readiness.exs --json --update-baseline docs/readiness-baseline.json PATHS...
#   elixir elixir/readiness.exs --markdown PATHS... > docs/readiness.md
elixir elixir/readiness.exs --check-baseline docs/readiness-baseline.json

echo "== prove"
lake build 2>&1 | grep -E "^(error|warning)" && exit 1 || true
grep -rl sorry Leanactors && { echo "sorry found"; exit 1; } || true
echo "   all proofs check, no sorry, no warnings"

echo "== run on BEAM"
elixir elixir/bank.exs | tail -1
elixir elixir/lock.exs 10 5000 | tail -1
elixir elixir/supervisor.exs | tail -1
elixir elixir/task.exs | tail -1
elixir elixir/watchdog.exs | tail -1
elixir elixir/ttl.exs | tail -1
elixir elixir/registry.exs | tail -1
elixir elixir/feed.exs | tail -1
elixir elixir/ringlog.exs | tail -1
elixir elixir/table_registry.exs | tail -1

echo "== differential fuzz (Lean replay vs BEAM)"
# lake build above also built .lake/build/bin/replay (a default target).
# 200 seeded scripts cycling bank, ttl, lock; exits 1 on the first mismatch.
elixir elixir/fuzz.exs --seed 1 --runs 200
