# A local stand-in for Phoenix.PubSub with the same function shapes
# (subscribe/2, unsubscribe/2, broadcast/3), so the drivers run without the
# phoenix_pubsub dependency. One GenServer keeps [{topic, pid}] oldest first;
# a broadcast sends the message to every subscriber of the topic in that
# order, exactly as `Effect.broadcast` does in Leanactors/Sys.lean, and a
# subscriber that dies is dropped (its DOWN), as `Sys.terminate` does.
# The translator (../to_lean.exs) treats this module as PubSub by name.
# Not translated: it is the transport, not a modelled actor.
defmodule PubSub do
  use GenServer

  def start_link(opts \\ []),
    do: GenServer.start_link(__MODULE__, :ok, name: Keyword.get(opts, :name, __MODULE__))

  def subscribe(server, topic), do: GenServer.call(server, {:subscribe, self(), topic})
  def unsubscribe(server, topic), do: GenServer.call(server, {:unsubscribe, self(), topic})
  def broadcast(server, topic, msg), do: GenServer.call(server, {:broadcast, topic, msg})
  def broadcast!(server, topic, msg), do: broadcast(server, topic, msg)
  def subscribers(server, topic), do: GenServer.call(server, {:subscribers, topic})

  @impl true
  def init(:ok), do: {:ok, []}

  @impl true
  def handle_call({:subscribe, pid, topic}, _from, subs) do
    Process.monitor(pid)
    {:reply, :ok, subs ++ [{topic, pid}]}
  end

  def handle_call({:unsubscribe, pid, topic}, _from, subs),
    do: {:reply, :ok, Enum.reject(subs, &(&1 == {topic, pid}))}

  def handle_call({:broadcast, topic, msg}, _from, subs) do
    for {^topic, pid} <- subs, do: send(pid, msg)
    {:reply, :ok, subs}
  end

  def handle_call({:subscribers, topic}, _from, subs),
    do: {:reply, for({^topic, pid} <- subs, do: pid), subs}

  @impl true
  def handle_info({:DOWN, _ref, :process, pid, _reason}, subs),
    do: {:noreply, Enum.reject(subs, fn {_, p} -> p == pid end)}
end
