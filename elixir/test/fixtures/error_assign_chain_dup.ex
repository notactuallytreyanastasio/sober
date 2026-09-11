# expect: error does not fit the record state
# The same assign key written twice in one chain. The single record update
# the chain folds into has one slot per key, and dropping the first write
# would drop its sub-expressions with it -- anything unsupported inside them
# would go unreported, and a module would translate that should not. So the
# fold is refused and the call stays what it is: an `assign` the translator
# has no mapping for, reported where the un-rewritten call lands.
defmodule Twice do
  use Phoenix.LiveView

  def handle_info({:bump, n}, socket) do
    {:noreply, socket |> assign(:count, n) |> assign(:count, 0)}
  end
end
