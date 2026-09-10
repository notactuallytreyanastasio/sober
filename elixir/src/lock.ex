# The lock protocol as ordinary Elixir. This file is BOTH executed on the
# BEAM (by ../lock.exs) AND translated to Lean (by ../to_lean.exs).
#
# The translator reads the @type declarations to build the Lean inductives.
# `pid() | nil` becomes `Option Pid`, `[pid()]` becomes `List Pid`, and a
# union of atoms becomes an enum.

defmodule Lock do
  use GenServer

  @type msg :: {:acquire, pid()} | {:release, pid()}
  @type state :: {pid() | nil, [pid()]}

  def start_link, do: GenServer.start_link(__MODULE__, {nil, []}, name: __MODULE__)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_cast(msg(), state()) :: {:noreply, state()}
  def handle_cast({:acquire, p}, {nil, q}) do
    send(p, :grant)
    {:noreply, {p, q}}
  end

  def handle_cast({:acquire, p}, {h, q}), do: {:noreply, {h, q ++ [p]}}

  def handle_cast({:release, p}, {p, []}), do: {:noreply, {nil, []}}

  def handle_cast({:release, p}, {p, [n | rest]}) do
    send(n, :grant)
    {:noreply, {n, rest}}
  end

  def handle_cast({:release, _}, s), do: {:noreply, s}
end

defmodule Client do
  use GenServer

  @type phase :: :idle | :waiting | :holding
  @type msg :: :tick | :grant
  @type state :: phase()

  def start_link, do: GenServer.start_link(__MODULE__, :idle)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:tick, :idle) do
    GenServer.cast(Lock, {:acquire, self()})
    {:noreply, :waiting}
  end

  def handle_info(:grant, :waiting), do: {:noreply, :holding}

  def handle_info(:tick, :holding) do
    GenServer.cast(Lock, {:release, self()})
    {:noreply, :idle}
  end

  def handle_info(_, s), do: {:noreply, s}
end
