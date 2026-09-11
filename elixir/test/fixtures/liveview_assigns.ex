# expect: ok
# lean: check
# A LiveView socket. Phoenix imports `assign/2,3`, which is a functional
# update of the socket's `assigns` map: `assign(s, :k, v)` is rewritten to
# the map update `%{s | k: v}`, `assign(s, k: v, ..)` and `assign(s, %{k:
# v})` to the multi-field one, and `s.assigns.k` to the field read `s.k`.
# The module declares no @type and has no init/1, so its state is the
# record of the assigns its callbacks touch -- `entries`, `count`, `last`
# -- each typed by the shape the bodies write to it: a list append makes
# `entries` a `[term()]`, an integer literal makes `count` an `integer()`,
# and `last`, which is only ever given the message field, stays opaque.
# Assigns no callback reads or writes (`page_title` here) are not in the
# model, the same abstraction a record state makes of any map.
#
# Nothing else about LiveView is modelled. `mount/3` is the lifecycle, so
# the initial state comes from the spawn site as it does for a GenServer
# with no init/1; `handle_event/3` is a browser event rather than a
# message, so it is not a clause of `beh` -- and because that IS a
# transition the real process makes, the generated file says so.
defmodule Board do
  use Phoenix.LiveView

  def mount(_params, _session, socket) do
    {:ok, assign(socket, page_title: "Board", entries: [], count: 0, last: nil)}
  end

  def handle_info({:entry, e}, socket) do
    {:noreply,
     assign(socket,
       entries: socket.assigns.entries ++ [e],
       count: socket.assigns.count + 1,
       last: e
     )}
  end

  def handle_info(:reset, socket) do
    {:noreply, assign(socket, %{entries: [], count: 0})}
  end

  def handle_info(_other, socket), do: {:noreply, socket}

  def handle_event("clear", _params, socket) do
    {:noreply, assign(socket, :entries, [])}
  end
end
