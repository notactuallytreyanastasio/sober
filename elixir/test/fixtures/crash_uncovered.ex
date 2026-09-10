# expect: ok
# lean: check
# Effects mode (the {:stop, ...} forces it): the cast :open has no clause
# that is total over the state, so a crash clause is emitted for it after
# the cast clauses and before the info clauses.
defmodule Door do
  use GenServer

  @type msg :: :open | :close | :quit
  @type state :: boolean()

  def init(s), do: {:ok, s}

  def handle_cast(:open, false), do: {:noreply, true}
  def handle_cast(:close, _), do: {:noreply, false}

  def handle_info(:quit, s), do: {:stop, :normal, s}
end
