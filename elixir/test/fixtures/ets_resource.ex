# expect: ok
# lean: check
# External resources. `:ets.new(..)` on the right of a binding is a fresh
# opaque reference: the state gets a hidden trailing counter `(ets : Nat)`,
# the k-th table a body creates is `Term.mk (ets + k)` and the continuing
# state advances the counter (`:pair` creates two, so it advances by 2).
# `:ets.delete(ref)` as a statement, and the `try .. rescue .. end` around
# one, are dropped: what happens inside ETS is not modelled. The public
# wrappers `open/1`, `close/1` and `open!/1` are not callbacks, so they are
# not translated (the `raise` in `open!/1` is not a callback body either);
# the generated file names them in a comment.
defmodule Tables do
  use GenServer

  def start_link(opts), do: GenServer.start_link(__MODULE__, opts, name: __MODULE__)

  def open(name), do: GenServer.call(__MODULE__, {:open, name})
  def close(name), do: GenServer.call(__MODULE__, {:close, name})

  def open!(name) do
    case open(name) do
      {:ok, ref} -> ref
      :error -> raise ArgumentError, "no table"
    end
  end

  def init(_opts), do: {:ok, %{refs: %{}}}

  def handle_call({:open, name}, _from, state) do
    ref = :ets.new(:tbl, [:set])
    {:reply, {:ok, ref}, %{state | refs: Map.put(state.refs, name, ref)}}
  end

  def handle_call({:pair, name}, _from, state) do
    left = :ets.new(:tbl, [:set])
    right = :ets.new(:tbl, [:set])
    refs = Map.put(Map.put(state.refs, name, left), name, right)
    {:reply, {:ok, right}, %{state | refs: refs}}
  end

  def handle_call({:close, name}, _from, state) do
    case Map.pop(state.refs, name) do
      {nil, _rest} ->
        {:reply, :error, state}

      {ref, rest} ->
        try do
          :ets.delete(ref)
        rescue
          ArgumentError -> :ok
        end

        {:reply, :ok, %{state | refs: rest}}
    end
  end

  def handle_cast({:drop, name}, state) do
    case Map.pop(state.refs, name) do
      {nil, _rest} -> {:noreply, state}
      {ref, rest} -> :ets.delete(ref); {:noreply, %{state | refs: rest}}
    end
  end
end
