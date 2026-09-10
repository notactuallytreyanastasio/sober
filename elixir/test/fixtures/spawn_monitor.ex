# expect: ok
# lean: check
# `{pid, _ref} = spawn_monitor(Mod, :run, [a])` is one spawnMonitor effect
# with Mod's state constructor applied to `a`; the DOWN arrives as a message.
defmodule Boss do
  use GenServer

  @type msg :: :hire | {:DOWN, reference(), :process, pid(), term()}
  @type state :: {pid() | nil, non_neg_integer()}

  def init(s), do: {:ok, s}

  def handle_info(:hire, {nil, k}) do
    {pid, _ref} = spawn_monitor(Hand, :run, [0])
    {:noreply, {pid, k}}
  end

  def handle_info({:DOWN, _ref, :process, p, _}, {p, k}), do: {:noreply, {nil, k + 1}}
  def handle_info(_, s), do: {:noreply, s}
end

defmodule Hand do
  @type msg :: :work | :quit
  @type state :: non_neg_integer()

  def run(n) do
    receive do
      :work -> run(n + 1)
      :quit -> :ok
    end
  end
end
