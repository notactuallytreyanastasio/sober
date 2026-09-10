# expect: error handled by both handle_cast and handle_info
# One message tag handled by two callback kinds would need two Lean clauses
# for one Msg constructor; the translator rejects it.
defmodule Dual do
  use GenServer

  @type msg :: :ping
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:ping, n), do: {:noreply, n + 1}
  def handle_info(:ping, n), do: {:noreply, n}
end
