# expect: error unsupported expression assign(socket, key, v)
# A LiveView assign whose key is not a literal atom. `assign(s, :k, v)` is
# rewritten to the field update `%{s | k: v}` because the model's state is a
# record with a fixed set of fields; a computed key would be a map the model
# does not have here, so the call is left alone and reported as the
# unsupported expression it is.
defmodule Dyn do
  use Phoenix.LiveView

  def handle_info({:set, key, v}, socket) do
    {:noreply, assign(socket, key, v)}
  end

  def handle_info(_other, socket), do: {:noreply, socket}
end
