# expect: error message tag :bogus not in @type msg
# A clause for a tag missing from @type msg is rejected.
defmodule Strict do
  use GenServer

  @type msg :: :ping
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:ping, n), do: {:noreply, n + 1}
  def handle_info(:bogus, n), do: {:noreply, n}
end
