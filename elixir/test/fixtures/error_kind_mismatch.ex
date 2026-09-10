# expect: error declared under @type info but handled by handle_cast
# A handle_cast clause for a tag declared under @type info is a kind
# mismatch (on the BEAM it would be a cast that the info-typed message
# never reaches), so the translator rejects it.
defmodule Mixed do
  use GenServer

  @type info :: :tick
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:tick, n), do: {:noreply, n + 1}
end
