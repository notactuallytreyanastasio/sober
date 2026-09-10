#!/bin/sh
# Full chain: regenerate Lean from Elixir, check nothing drifted, prove, run.
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

echo "== translate"
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > /tmp/Gen.Lock.lean
elixir elixir/to_lean.exs elixir/src/bank.ex Leanactors.Gen.Bank --pid Bank=bank > /tmp/Gen.Bank.lean
elixir elixir/to_lean.exs elixir/src/supervisor.ex Leanactors.Gen.Supervisor --pid Sup=sup > /tmp/Gen.Supervisor.lean
elixir elixir/to_lean.exs elixir/src/task.ex Leanactors.Gen.Task --pid Caller=caller > /tmp/Gen.Task.lean
elixir elixir/to_lean.exs elixir/src/watchdog.ex Leanactors.Gen.Watchdog --pid Watchdog=watchdog > /tmp/Gen.Watchdog.lean
elixir elixir/to_lean.exs elixir/src/ttl.ex Leanactors.Gen.Ttl > /tmp/Gen.Ttl.lean
diff -q /tmp/Gen.Lock.lean Leanactors/Gen/Lock.lean
diff -q /tmp/Gen.Bank.lean Leanactors/Gen/Bank.lean
diff -q /tmp/Gen.Supervisor.lean Leanactors/Gen/Supervisor.lean
diff -q /tmp/Gen.Task.lean Leanactors/Gen/Task.lean
diff -q /tmp/Gen.Watchdog.lean Leanactors/Gen/Watchdog.lean
diff -q /tmp/Gen.Ttl.lean Leanactors/Gen/Ttl.lean
echo "   generated files are up to date"

echo "== translator fixtures"
elixir elixir/test/run_fixtures.exs | grep -v "^PASS "

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

echo "== differential fuzz (Lean replay vs BEAM)"
# lake build above also built .lake/build/bin/replay (a default target).
# 200 seeded scripts, half bank, half ttl; exits 1 on the first mismatch.
elixir elixir/fuzz.exs --seed 1 --runs 200
