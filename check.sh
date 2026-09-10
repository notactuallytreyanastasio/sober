#!/bin/sh
# Full chain: regenerate Lean from Elixir, check nothing drifted, prove, run.
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

echo "== translate"
elixir elixir/to_lean.exs elixir/src/lock.ex Leanactors.Gen.Lock --pid Lock=server > /tmp/Gen.Lock.lean
elixir elixir/to_lean.exs elixir/src/bank.ex Leanactors.Gen.Bank > /tmp/Gen.Bank.lean
diff -q /tmp/Gen.Lock.lean Leanactors/Gen/Lock.lean
diff -q /tmp/Gen.Bank.lean Leanactors/Gen/Bank.lean
echo "   generated files are up to date"

echo "== prove"
lake build 2>&1 | grep -E "^(error|warning)" && exit 1 || true
grep -rl sorry Leanactors && { echo "sorry found"; exit 1; } || true
echo "   all proofs check, no sorry, no warnings"

echo "== run on BEAM"
elixir elixir/bank.exs | tail -1
elixir elixir/lock.exs 10 5000 | tail -1
