# expect: ok
# lean: check
# Process.exit/2 is an exit signal; :normal stays :normal (ignored by a
# non-trapping target, an EXIT message to a trapping one), :kill is kill
# (untrappable: the target dies whatever it traps and its links see error),
# any other reason is error.
defmodule Killer do
  use GenServer

  @type msg :: {:kill, pid()} | {:halt, pid()}
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info({:kill, p}, n) do
    Process.exit(p, :kill)
    {:noreply, n + 1}
  end

  def handle_info({:halt, p}, n) do
    Process.exit(p, :normal)
    {:noreply, n}
  end
end
