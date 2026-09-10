# expect: error no --pid mapping for Sink
# A send to a registered name needs a --pid mapping.
defmodule Source do
  use GenServer

  @type msg :: :emit
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:emit, n) do
    send(Sink, :flush)
    {:noreply, n + 1}
  end
end

defmodule Sink do
  use GenServer

  @type msg :: :flush
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:flush, _), do: {:noreply, 0}
end
