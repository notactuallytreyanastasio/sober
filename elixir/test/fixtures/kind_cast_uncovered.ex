# expect: ok
# lean: check
# A tag declared under @type cast is a cast tag even when no callback
# mentions it: :bump has no clause anywhere, so it gets a crash clause
# (FunctionClauseError on the BEAM). Compare crash_uncovered.ex, where the
# kind is inferred from a handle_cast clause that partially covers the tag.
# The @type msg tag :tick is classified by its handle_info clause as before.
defmodule Counter do
  use GenServer

  @type msg :: :tick
  @type cast :: :bump | {:set, non_neg_integer()}
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast({:set, v}, _), do: {:noreply, v}

  def handle_info(:tick, n), do: {:noreply, n + 1}
end
