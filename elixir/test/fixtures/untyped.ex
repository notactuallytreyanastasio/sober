# expect: ok
# lean: check
# Untyped mode. This module declares no @type at all, so the translator
# infers the declarations from the source: the cast tags from the
# handle_cast patterns, the info tags from handle_info, the call tags from
# handle_call (each with a leading caller), a msg tag for `:ping`, which
# the module sends but no clause handles, and the reply type from the
# {:reply, r, _} expressions -- all literal, so a tagged union `Reply`,
# where `:ok` occurs at arity 0 and `{:ok, l}` at arity 1 and the unary
# constructor is named `ok1`. The state comes from init/1's literal
# `{nil, false}`: `term() | nil` is `Option Term` and `false` is `Bool`.
# Every inferred field is the opaque `Term` of Leanactors/Term.lean.
defmodule Log do
  use GenServer

  def init(_opts), do: {:ok, {nil, false}}

  def handle_cast({:write, line}, {_last, dirty}) do
    send(self(), :flushed)
    send(self(), :ping)
    {:noreply, {line, dirty}}
  end

  def handle_cast(:clear, {_last, _dirty}), do: {:noreply, {nil, false}}

  def handle_info(:flushed, {last, _dirty}), do: {:noreply, {last, true}}

  def handle_call(:head, _from, {last, dirty}) do
    case last do
      nil -> {:reply, :empty, {last, dirty}}
      l -> {:reply, {:ok, l}, {last, dirty}}
    end
  end

  def handle_call({:drop, _n}, _from, {_last, dirty}), do: {:reply, :ok, {nil, dirty}}
end
