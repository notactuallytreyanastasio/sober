# translate: --pid Sink=sink
# expect: ok
# lean: check
# send/2 and GenServer.cast/2 to a registered name go to the constant pid
# given by --pid; the list state uses ++ and [].
defmodule Source do
  use GenServer

  @type msg :: :emit
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:emit, n) do
    send(Sink, {:item, n})
    GenServer.cast(Sink, :flush)
    {:noreply, n + 1}
  end
end

defmodule Sink do
  use GenServer

  @type msg :: {:item, non_neg_integer()} | :flush
  @type state :: [non_neg_integer()]

  def init(s), do: {:ok, s}

  def handle_info({:item, x}, xs), do: {:noreply, xs ++ [x]}
  def handle_cast(:flush, _), do: {:noreply, []}
end
