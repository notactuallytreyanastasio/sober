# expect: ok
# lean: check
# A tag declared under @type info with no clause is ignored, as an unmatched
# handle_info message is on the BEAM: :stale gets no crash clause and the
# module keeps the global catch-all. @type msg is omitted here; cast and
# info together declare every tag.
defmodule Ticker do
  use GenServer

  @type cast :: {:set, non_neg_integer()}
  @type info :: :tick | :stale
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast({:set, v}, _), do: {:noreply, v}

  def handle_info(:tick, n), do: {:noreply, n + 1}
end
