# expect: ok
# lean: check
# A module with neither `@type state` nor an init/1: the state shape comes
# from the state patterns of its callbacks (and the keys their bodies update
# or return), which must agree. Cache matches a map, so it becomes a record
# with one field per key; Ping only ever binds the state whole, so it stays
# the opaque `Term`. Every inferred field is a `Term`, as in untyped mode.
defmodule Cache do
  use GenServer

  def start_link(s), do: GenServer.start_link(__MODULE__, s, name: __MODULE__)

  @impl true
  def handle_cast({:put, v}, %{entries: es, last: _l}) do
    {:noreply, %{entries: es, last: v}}
  end

  def handle_cast(:forget, state) do
    {:noreply, %{state | last: state.entries}}
  end

  @impl true
  def handle_call(:swap, _from, %{entries: es, last: l}) do
    {:reply, :ok, %{entries: l, last: es}}
  end
end

defmodule Ping do
  use GenServer

  @impl true
  def handle_info(:ping, s), do: {:noreply, s}
end
