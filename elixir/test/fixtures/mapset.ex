# expect: ok
# lean: check
# A MapSet is a duplicate-free list in insertion order
# (Leanactors/SetList.lean): `MapSet.t(T)` is `List T`, `MapSet.new()` is
# `[]`, and put/delete/member?/size/to_list are the SetList functions.
# `to_list` is the identity on that list, so it is in insertion order and
# not the BEAM's term order: a property may count and test membership, but
# must not depend on the order.
defmodule Seen do
  use GenServer

  @type item :: :a | :b | :c
  @type msg :: {:see, item()} | {:forget, item()} | {:merge, MapSet.t(item())} | :clear
  @type call :: {:seen?, item()} | :count | :list
  @type reply :: {:yes, boolean()} | {:n, non_neg_integer()} | {:items, [item()]}
  @type state :: MapSet.t(item())

  def init(s), do: {:ok, s}

  def handle_cast({:see, i}, s), do: {:noreply, MapSet.put(s, i)}
  def handle_cast({:forget, i}, s), do: {:noreply, MapSet.delete(s, i)}
  def handle_cast({:merge, o}, s), do: {:noreply, MapSet.union(s, o)}
  def handle_cast(:clear, _), do: {:noreply, MapSet.new()}

  def handle_call({:seen?, i}, _from, s), do: {:reply, {:yes, MapSet.member?(s, i)}, s}
  def handle_call(:count, _from, s), do: {:reply, {:n, MapSet.size(s)}, s}
  def handle_call(:list, _from, s), do: {:reply, {:items, MapSet.to_list(s)}, s}
end
