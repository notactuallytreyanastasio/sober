# expect: ok
# lean: check
# A record-shaped state. `@type state :: %{k: T, ..}` with atom keys is one
# St constructor with named fields, one per key: `state.done` is the field,
# `%{state | queue: q}` rebuilds the constructor with that field replaced,
# a bare `state` is the whole constructor, and a map pattern `%{running:
# true} = state` binds the named fields to their sub-patterns and the rest
# as the whole variable would (a field the body never reads is `_`). The
# messages are inferred (no @type msg/cast/call), the state and the reply
# are declared: a declaration refines the fields inference would leave
# opaque. `case Map.pop(q, k)` is a match on `AssocList.get? q k` whose
# `{nil, rest}` arm keeps the map and whose `{v, rest}` arm erases the key.
defmodule Jobs do
  use GenServer

  @type state :: %{queue: %{term() => term()}, running: boolean(), done: non_neg_integer()}
  @type reply :: non_neg_integer()

  def init(_opts), do: {:ok, %{queue: %{}, running: false, done: 0}}

  def handle_cast({:push, id, job}, state) do
    {:noreply, %{state | queue: Map.put(state.queue, id, job), running: true}}
  end

  def handle_cast({:pop, id}, state) do
    case Map.pop(state.queue, id) do
      {nil, _rest} -> {:noreply, state}
      {_job, rest} -> {:noreply, %{state | queue: rest, done: state.done + 1}}
    end
  end

  def handle_cast(:halt, %{running: true} = state), do: {:noreply, %{state | running: false}}
  def handle_cast(:halt, state), do: {:noreply, state}

  def handle_call(:size, _from, %{queue: q} = state), do: {:reply, map_size(q), state}
  def handle_call(:done, _from, state), do: {:reply, state.done, state}
end
