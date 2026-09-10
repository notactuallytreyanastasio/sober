# expect: ok
# lean: check
# Clauses that split an enum state field (:idle / :busy) or a list field
# ([] / [_ | t]) are exhaustive to Lean, and the translator's usefulness
# check over the rendered patterns sees it too: no crash clause for :go or
# :pop, and no global catch-all, since Lean would reject either as a
# redundant alternative.
defmodule Machine do
  use GenServer

  @type phase :: :idle | :busy
  @type msg :: :go | :pop | {:push, non_neg_integer()}
  @type state :: {phase(), [non_neg_integer()]}

  def init(s), do: {:ok, s}

  def handle_cast(:go, {:idle, q}), do: {:noreply, {:busy, q}}
  def handle_cast(:go, {:busy, q}), do: {:noreply, {:idle, q}}
  def handle_cast(:pop, {ph, []}), do: {:noreply, {ph, []}}
  def handle_cast(:pop, {ph, [_ | t]}), do: {:noreply, {ph, t}}
  def handle_cast({:push, n}, {ph, q}), do: {:noreply, {ph, q ++ [n]}}
end
