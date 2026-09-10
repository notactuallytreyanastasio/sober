#!/bin/sh
# Regenerate every fixture's expected Lean from the current translator.
# Run after an intentional change to elixir/to_lean.exs, then review
# `git diff elixir/test/expected` before committing. Fixtures marked
# `# lean: check` are also compiled, so the library must be built (lake build).
set -e
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
exec elixir elixir/test/run_fixtures.exs --regen "$@"
