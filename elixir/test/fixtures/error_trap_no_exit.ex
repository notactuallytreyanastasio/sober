# expect: error a trapping module must declare {:EXIT, pid(), term()}
# Trapping exits without declaring the EXIT message is rejected.
defmodule Trapper do
  use GenServer

  @type msg :: :start
  @type state :: non_neg_integer()

  def init(n) do
    Process.flag(:trap_exit, true)
    {:ok, n}
  end

  def handle_info(:start, n), do: {:noreply, n + 1}
end
