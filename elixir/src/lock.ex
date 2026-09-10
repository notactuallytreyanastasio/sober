# The lock protocol as ordinary Elixir. This file is BOTH executed on the
# BEAM (by ../lock.exs) AND translated to Lean (by ../to_lean.exs).
#
# Clients acquire with a *blocking* GenServer.call. The server replies
# immediately when the lock is free, otherwise it queues the caller and
# replies later with GenServer.reply/2 when the lock is released. The
# translator turns the blocking call into an await state on the client.

defmodule Lock do
  use GenServer

  @type msg :: {:release, pid()}
  @type call :: :acquire
  @type reply :: :ok
  # holder and queue entries are callers (GenServer.from(), modelled as pids)
  @type state :: {GenServer.from() | nil, [GenServer.from()]}

  def start_link, do: GenServer.start_link(__MODULE__, {nil, []}, name: __MODULE__)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_call(call(), GenServer.from(), state()) :: {:reply, reply(), state()} | {:noreply, state()}
  def handle_call(:acquire, from, {nil, q}), do: {:reply, :ok, {from, q}}
  def handle_call(:acquire, from, {h, q}), do: {:noreply, {h, q ++ [from]}}

  @impl true
  @spec handle_cast(msg(), state()) :: {:noreply, state()}
  def handle_cast({:release, p}, {{p, _}, []}), do: {:noreply, {nil, []}}

  def handle_cast({:release, p}, {{p, _}, [n | rest]}) do
    GenServer.reply(n, :ok)
    {:noreply, {n, rest}}
  end

  def handle_cast({:release, _}, s), do: {:noreply, s}
end

defmodule Client do
  use GenServer

  @type phase :: :idle | :holding
  @type msg :: :tick
  @type state :: phase()

  def start_link, do: GenServer.start_link(__MODULE__, :idle)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:tick, :idle) do
    :ok = GenServer.call(Lock, :acquire, :infinity)
    {:noreply, :holding}
  end

  def handle_info(:tick, :holding) do
    GenServer.cast(Lock, {:release, self()})
    {:noreply, :idle}
  end
end
