# expect: error Sink.forward/2: send(:sink, {:note, k}) is not a binding
# A helper a callback calls must be a pure expression: it has no effects of
# its own, so a `send` inside one is an error naming the helper -- once,
# rather than once per call site.
defmodule Sink do
  use GenServer

  @type msg :: {:log, non_neg_integer()} | {:note, non_neg_integer()}
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  defp forward(n, k) do
    send(:sink, {:note, k})
    n + k
  end

  def handle_cast({:log, k}, n), do: {:noreply, forward(n, k)}
end
