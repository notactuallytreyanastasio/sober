# expect: ok
# lean: check
# warn: no module in this file spawns
# A module whose init/1 subscribes but that nothing in the file spawns: a
# subscribe has no spawn site to hang on (the effect names the subscriber's
# pid, and a root actor's pid is chosen by whoever places it), so the model
# shows no subscription and the translator warns. The hand-written example
# that places this actor must add the `subscribe` to its initial effects.
defmodule Ticker do
  use GenServer

  @topic "ticks"

  @type msg :: {:tick, non_neg_integer()} | :stop
  @type state :: non_neg_integer()

  def init(n) do
    PubSub.subscribe(PubSub, @topic)
    {:ok, n}
  end

  def handle_info({:tick, k}, n), do: {:noreply, n + k}

  def handle_info(:stop, n) do
    PubSub.unsubscribe(PubSub, @topic)
    {:noreply, n}
  end
end
