# expect: error must be a string literal or a module attribute bound to one
# A PubSub topic that is neither a string literal nor a string attribute.
defmodule Hub do
  use GenServer

  @type msg :: {:publish, non_neg_integer()}
  @type state :: non_neg_integer()

  def init(s), do: {:ok, s}

  def handle_info({:publish, k}, n) do
    Phoenix.PubSub.broadcast(MyApp.PubSub, k, {:publish, k})
    {:noreply, n + k}
  end
end
