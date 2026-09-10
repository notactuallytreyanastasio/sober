# A one-for-one supervisor with a single permanent worker, as ordinary
# Elixir. Executed by ../supervisor.exs, translated by ../to_lean.exs.
#
# Translator conventions for process effects:
#   Process.flag(:trap_exit, true) in init      -> this module traps exits
#   pid = spawn_link(Mod, :run, [arg])          -> spawnLink with Mod's state = arg
#                                                  (Mod.run is Mod's receive loop)
#   {:EXIT, pid(), term()} in @type msg         -> the EXIT message, reason as Reason
#   {:stop, reason, state} / exit(reason)       -> exit effect; :normal or error
#
# A raw process (no GenServer) is one function whose body is a receive:
#   def run(n) do receive do ... end end        -> each clause is a handle_info
#                                                  clause with `n` as the state
#   pat -> run(e)                               -> next state e
#   pat -> exit(r)                              -> exit effect, state unchanged
#   pat -> :ok  (any other value)               -> the loop returns: exit :normal
#   no catch-all clause                         -> other messages are deferred
#                                                  (re-enqueued to self)

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
    pid = spawn_link(Worker, :run, [0])
    {:noreply, {pid, k}}
  end

  def handle_info({:EXIT, c, _}, {c, k}) do
    pid = spawn_link(Worker, :run, [0])
    {:noreply, {pid, k + 1}}
  end

  def handle_info(_, s), do: {:noreply, s}
end

defmodule Worker do
  @type msg :: :job | :crash | :stop
  @type state :: non_neg_integer()

  @spec run(state()) :: :ok
  def run(n) do
    receive do
      :job -> run(n + 1)
      :crash -> exit(:boom)
      :stop -> :ok
    end
  end
end
