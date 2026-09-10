# expect: error declared under both @type cast and @type info
# A tag may be declared under only one of msg, cast, info and call.
defmodule Dual do
  use GenServer

  @type cast :: :ping
  @type info :: :ping
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:ping, n), do: {:noreply, n + 1}
end
