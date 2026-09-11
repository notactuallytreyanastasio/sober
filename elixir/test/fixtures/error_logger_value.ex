# expect: error has no value in the model
# A `:noop` row is a statement that disappears; it is not an expression, so
# binding its result is an error rather than a silent `:ok`.
defmodule Bound do
  use GenServer

  @type msg :: :go
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:go, n) do
    x = Logger.info("hi")
    {:noreply, n + x}
  end
end
