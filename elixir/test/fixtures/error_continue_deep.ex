# expect: error deeper than 3
# A handle_continue body that continues into itself never reaches a tail
# the model can render; the inliner gives up at depth 3.
defmodule Spinner do
  use GenServer

  @type msg :: :go
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:go, n), do: {:noreply, n, {:continue, :spin}}

  def handle_continue(:spin, n), do: {:noreply, n + 1, {:continue, :spin}}
end
