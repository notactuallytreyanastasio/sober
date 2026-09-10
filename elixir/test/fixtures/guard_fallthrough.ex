# expect: ok
# lean: check
# A guarded cast whose guard can fail falls through to the next clause of
# the same callback whose patterns are at least as general; that clause's
# body is inlined as the `else` branch with its variables aliased.
defmodule Acct do
  use GenServer

  @type msg :: {:withdraw, non_neg_integer()} | :reset
  @type state :: integer()

  def init(b), do: {:ok, b}

  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}
  def handle_cast({:withdraw, _}, b), do: {:noreply, b}
  def handle_cast(:reset, _), do: {:noreply, 0}
end
