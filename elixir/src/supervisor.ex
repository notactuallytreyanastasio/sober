# A one-for-one supervisor with a single permanent worker, as ordinary
# Elixir. Executed by ../supervisor.exs, translated by ../to_lean.exs.
#
# Translator conventions for process effects:
#   Process.flag(:trap_exit, true) in init      -> this module traps exits
#   {:ok, pid} = GenServer.start_link(Mod, arg) -> spawnLink with Mod's state = arg
#                                                  (Mod.init must be the identity)
#   {:EXIT, pid(), term()} in @type msg         -> the EXIT message, reason as Reason
#   {:stop, reason, state} / exit(reason)       -> exit effect; :normal or error

defmodule Sup do
  use GenServer

  @type msg :: :start | {:EXIT, pid(), term()}
  @type state :: {pid() | nil, non_neg_integer()}

  def start_link, do: GenServer.start_link(__MODULE__, {nil, 0}, name: __MODULE__)

  @impl true
  def init(s) do
    Process.flag(:trap_exit, true)
    {:ok, s}
  end

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:start, {nil, k}) do
    {:ok, pid} = GenServer.start_link(Worker, 0)
    {:noreply, {pid, k}}
  end

  def handle_info({:EXIT, c, _}, {c, k}) do
    {:ok, pid} = GenServer.start_link(Worker, 0)
    {:noreply, {pid, k + 1}}
  end

  def handle_info(_, s), do: {:noreply, s}
end

defmodule Worker do
  use GenServer

  @type msg :: :job | :crash | :stop
  @type state :: non_neg_integer()

  @impl true
  def init(n), do: {:ok, n}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()} | {:stop, term(), state()}
  def handle_info(:job, n), do: {:noreply, n + 1}
  def handle_info(:crash, n), do: {:stop, :boom, n}
  def handle_info(:stop, n), do: {:stop, :normal, n}
end
