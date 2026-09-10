# expect: ok
# lean: check
# Effects mode: a guarded cast with no clause to fall through to crashes
# with FunctionClauseError when the guard fails.
defmodule Vault do
  use GenServer

  @type msg :: {:withdraw, non_neg_integer()} | :quit
  @type state :: non_neg_integer()

  def init(b), do: {:ok, b}

  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}

  def handle_info(:quit, b), do: {:stop, :normal, b}
end
