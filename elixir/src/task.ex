# An async task: the caller starts a worker, monitors it, and waits for
# either its reply or its DOWN. Executed by ../task.exs, translated by
# ../to_lean.exs.
#
# Translator conventions for monitors and init:
#   {:ok, pid} = GenServer.start(Mod, arg)      -> spawn (no link) with Mod's
#                                                  state = Mod.init(arg), where
#                                                  init/1 is `{:ok, e}` for a pure
#                                                  expression e of its parameter
#                                                  (here Worker.init(parent) builds
#                                                  {parent, 0} from the bare pid)
#   Process.monitor(pid)                         -> monitor effect
#   {:DOWN, reference(), :process, pid(), term()} in @type msg -> DOWN (Pid) (Reason)

defmodule Caller do
  use GenServer

  @type msg :: :go | {:reply, non_neg_integer()} | {:DOWN, reference(), :process, pid(), term()}
  # pending worker, completed results
  @type state :: {pid() | nil, non_neg_integer()}

  def start_link, do: GenServer.start_link(__MODULE__, {nil, 0}, name: __MODULE__)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:go, {nil, r}) do
    {:ok, pid} = GenServer.start(Worker, self())
    Process.monitor(pid)
    {:noreply, {pid, r}}
  end

  def handle_info({:reply, _}, {_, r}), do: {:noreply, {nil, r + 1}}

  def handle_info({:DOWN, _ref, :process, w, _}, {w, r}), do: {:noreply, {nil, r}}

  def handle_info(_, s), do: {:noreply, s}
end

defmodule Worker do
  use GenServer

  @type msg :: :compute | :crash
  # parent, input
  @type state :: {pid(), non_neg_integer()}

  @impl true
  def init(parent), do: {:ok, {parent, 0}}

  @impl true
  @spec handle_info(msg(), state()) :: {:stop, term(), state()}
  def handle_info(:compute, {parent, n}) do
    send(parent, {:reply, n + 1})
    {:stop, :normal, {parent, n}}
  end

  def handle_info(:crash, s), do: {:stop, :boom, s}
end
