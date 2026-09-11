# expect: ok
# lean: check
# Phoenix.PubSub as effects: subscribe in init/1 (emitted at the spawn site
# for the child), subscribe/unsubscribe in a handler (`:ok = ` form too),
# broadcast and broadcast! with a message expression, a topic as a string
# literal and as a module attribute, a second PubSub module named with
# --pubsub, and Phoenix.PubSub recognised without any flag.
# translate: --pubsub My.Bus
defmodule Hub do
  use GenServer

  @topic "news"

  @type msg :: :open | {:publish, non_neg_integer()} | :quiet
  @type state :: {pid() | nil, non_neg_integer()}

  def init(s), do: {:ok, s}

  def handle_info(:open, {nil, n}) do
    {:ok, r} = GenServer.start_link(Reader, 0)
    {:noreply, {r, n}}
  end

  def handle_info({:publish, k}, {r, n}) do
    Phoenix.PubSub.broadcast(MyApp.PubSub, @topic, {:item, k})
    Phoenix.PubSub.broadcast!(MyApp.PubSub, "alerts", :alert)
    {:noreply, {r, n + k}}
  end

  def handle_info(:quiet, s) do
    :ok = My.Bus.unsubscribe(My.Bus, "alerts")
    {:noreply, s}
  end

  def handle_info(_, s), do: {:noreply, s}
end

defmodule Reader do
  use GenServer

  @type msg :: {:item, non_neg_integer()} | :alert | :more
  @type state :: non_neg_integer()

  def init(n) do
    Phoenix.PubSub.subscribe(MyApp.PubSub, "news")
    :ok = My.Bus.subscribe(My.Bus, "alerts")
    {:ok, n}
  end

  def handle_info({:item, k}, n), do: {:noreply, n + k}

  def handle_info(:alert, n) do
    Phoenix.PubSub.unsubscribe(MyApp.PubSub, "alerts")
    {:noreply, n}
  end

  def handle_info(:more, n) do
    Phoenix.PubSub.subscribe(MyApp.PubSub, "news")
    {:noreply, n}
  end
end
