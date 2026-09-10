# expect: ok
# lean: check
# One trapping module declares both {:EXIT, pid(), term()} and
# {:DOWN, reference(), :process, pid(), term()}: both become
# (Pid) (Reason) constructors, `sig` gets exitMsg and downMsg, and two
# spawns in one clause bind `fresh` and `fresh + 1`.
defmodule Nanny do
  use GenServer

  @type msg :: :start | {:EXIT, pid(), term()} | {:DOWN, reference(), :process, pid(), term()}
  @type state :: {pid() | nil, pid() | nil}

  def init(s) do
    Process.flag(:trap_exit, true)
    {:ok, s}
  end

  def handle_info(:start, {nil, nil}) do
    {:ok, a} = GenServer.start_link(Kid, 0)
    {:ok, b} = GenServer.start(Kid, 1)
    Process.monitor(b)
    {:noreply, {a, b}}
  end

  def handle_info({:EXIT, a, _reason}, {a, b}), do: {:noreply, {nil, b}}
  def handle_info({:DOWN, _ref, :process, b, _reason}, {a, b}), do: {:noreply, {a, nil}}
  def handle_info(_, s), do: {:noreply, s}
end

defmodule Kid do
  use GenServer

  @type msg :: :crash | :bye
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:crash, n), do: {:stop, :boom, n}
  def handle_info(:bye, n), do: {:stop, :normal, n}
end
