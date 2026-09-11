# expect: ok
# lean: check
# A chain of LiveView assigns, and the one thing an untyped module says
# about a payload.
#
# `socket |> assign(:a, x) |> assign(:b, y)` desugars to
# `assign(assign(socket, :a, x), :b, y)`, whose socket argument is no longer
# a variable. The model's record update needs one at its head -- a record
# state has no whole value to nest one update inside another on -- so the
# chain is folded into the single `%{socket | a: x, b: y}`. That is exactly
# what the chain means: the intermediate socket is anonymous, so a value in
# it can only name the original `socket`, and Elixir's own record update
# reads every field off that same original.
#
# `track` is compared with nil. The model has nil only at an Option type, so
# the payload is inferred `term() | nil` (`Option Term`) rather than the
# opaque `term()` a payload gets by default -- a nil comparison is written
# only about a value that may be absent, and this is the only place an
# untyped module says so. `track != nil` is then a Bool, which is where the
# `playing` assign gets its field type.
defmodule Tuner do
  use Phoenix.LiveView

  def handle_info({:now_playing, track}, socket) do
    {:noreply,
     socket
     |> assign(:now_playing, track)
     |> assign(:playing, track != nil)}
  end

  def handle_info({:listeners, n}, socket) do
    {:noreply, socket |> assign(:listeners, n) |> assign(:busy, n)}
  end
end
