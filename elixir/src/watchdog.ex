# A watchdog: pings a linked worker, expects :pong before a GenServer
# timeout, kills and restarts the worker otherwise. Executed by
# ../watchdog.exs, translated by ../to_lean.exs.
#
# Translator conventions for time, remote exits and unhandled messages:
#   {:noreply, state, t}          -> the actor arms a self-timer for :timeout
#                                    (untimed: it may fire even after a message)
#   Process.send_after(p, m, t)   -> a timer for m at p
#   Process.exit(p, reason)       -> an exit signal to p
#   a cast (or call) with no matching handle_cast/handle_call clause
#                                 -> the process exits with reason error
#                                    (FunctionClauseError on the BEAM; links
#                                    and monitors are notified); an unmatched
#                                    handle_info message is ignored

defmodule Watchdog do
  use GenServer

  @type msg :: :start | :pong | :timeout | {:EXIT, pid(), term()}
  # worker, expecting a pong
  @type state :: {pid() | nil, boolean()}

  def start_link, do: GenServer.start_link(__MODULE__, {nil, false}, name: __MODULE__)

  @impl true
  def init(s) do
    Process.flag(:trap_exit, true)
    {:ok, s}
  end

  @impl true
  @spec handle_cast(msg(), state()) :: {:noreply, state(), timeout()}
  def handle_cast(:pong, {w, true}) do
    send(w, :ping)
    {:noreply, {w, true}, 100}
  end

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()} | {:noreply, state(), timeout()}
  def handle_info(:start, {nil, _}) do
    {:ok, pid} = GenServer.start_link(Worker, {false, 0})
    send(pid, :ping)
    {:noreply, {pid, true}, 100}
  end

  def handle_info(:timeout, {w, true}) do
    Process.exit(w, :kill)
    {:noreply, {w, false}}
  end

  def handle_info({:EXIT, w, _}, {w, _}) do
    {:ok, pid} = GenServer.start_link(Worker, {false, 0})
    send(pid, :ping)
    {:noreply, {pid, true}, 100}
  end

  def handle_info(_, s), do: {:noreply, s}
end

defmodule Worker do
  use GenServer

  @type msg :: :ping | :hang
  # hung, pings answered
  @type state :: {boolean(), non_neg_integer()}

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:ping, {false, n}) do
    GenServer.cast(Watchdog, :pong)
    {:noreply, {false, n + 1}}
  end

  def handle_info(:hang, {_, n}), do: {:noreply, {true, n}}

  def handle_info(_, s), do: {:noreply, s}
end
