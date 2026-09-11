# A feed over PubSub: a publisher broadcasts {:post, n} on "feed" at every
# :tick, two subscribers subscribe in init/1 and count the posts they
# receive; a subscriber told to :leave unsubscribes. Executed by ../feed.exs
# on the local PubSub twin (src/pubsub.ex), translated by ../to_lean.exs.
#
# Translator conventions for PubSub (see the header of ../to_lean.exs):
#   PubSub.subscribe(PubSub, @topic) in init/1  -> `.subscribe fresh "feed"` at the
#                                                  spawn site, after the spawn
#   PubSub.unsubscribe(PubSub, @topic)          -> `.unsubscribe me "feed"`
#   PubSub.broadcast(PubSub, @topic, m)         -> `.broadcast "feed" m`
#   @topic "feed"                               -> the string literal

defmodule Publisher do
  use GenServer

  @topic "feed"

  @type msg :: :start | :tick
  # posts published so far
  @type state :: non_neg_integer()

  def start_link, do: GenServer.start_link(__MODULE__, 0, name: __MODULE__)

  @impl true
  def init(n), do: {:ok, n}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:start, n) do
    {:ok, _a} = GenServer.start_link(Subscriber, 0)
    {:ok, _b} = GenServer.start_link(Subscriber, 0)
    {:noreply, n}
  end

  def handle_info(:tick, n) do
    PubSub.broadcast(PubSub, @topic, {:post, n + 1})
    {:noreply, n + 1}
  end
end

defmodule Subscriber do
  use GenServer

  @topic "feed"

  @type msg :: {:post, non_neg_integer()} | :leave
  # posts seen, still subscribed
  @type state :: {non_neg_integer(), boolean()}

  @impl true
  def init(seen) do
    PubSub.subscribe(PubSub, @topic)
    {:ok, {seen, true}}
  end

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info({:post, _n}, {seen, on}), do: {:noreply, {seen + 1, on}}

  def handle_info(:leave, {seen, true}) do
    PubSub.unsubscribe(PubSub, @topic)
    {:noreply, {seen, false}}
  end

  def handle_info(:leave, s), do: {:noreply, s}
end
