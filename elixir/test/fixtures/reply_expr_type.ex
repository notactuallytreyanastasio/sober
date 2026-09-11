# expect: ok
# lean: check
# Untyped mode, a reply that is not a literal. There is no @type reply and
# no {:reply, r, _} whose r is an atom or a tagged tuple, so there is no
# union to infer -- but the expressions still have a type between them. The
# translator renders the clauses once with the replies left out, collects
# the type each reply expression has in its own clause, and (there being
# exactly one, `List Term`) compiles the file again with it: `Msg.reply`
# carries a `List Term`, not the opaque `Term` a reply used to collapse to.
# Both replies must agree; `:queue.to_list(q)` is the queue itself, and the
# `entries` field is `List Term` because its defstruct default is a queue.
defmodule Ring do
  use GenServer

  defstruct entries: :queue.new(), cap: 3

  def init(cap), do: {:ok, %__MODULE__{cap: cap}}

  def handle_call(:all, _from, state) do
    {:reply, :queue.to_list(state.entries), state}
  end

  def handle_call(:recent, _from, state) do
    {:reply, Enum.take(state.entries, 2), state}
  end

  def handle_cast({:push, x}, state) do
    if length(state.entries) >= state.cap do
      {_, rest} = :queue.out(state.entries)
      {:noreply, %{state | entries: :queue.in(x, rest)}}
    else
      {:noreply, %{state | entries: :queue.in(x, state.entries)}}
    end
  end
end
