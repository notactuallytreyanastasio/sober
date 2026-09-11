# expect: ok
# lean: check
# Maps. A `%{K => V}` type is an association list `List (K × V)`
# (Leanactors/AssocList.lean): `%{}` is `[]`, a literal `%{k => v, ..}` a
# list of pairs; Map.get/2 and Map.fetch/2 are `get?` (an Option: match
# with `nil`/variable arms or `{:ok, v}`/`:error` arms), Map.get/3 is
# `(get? m k).getD d`, Map.put `insert`, Map.delete `erase`, Map.has_key?
# and is_map_key `hasKey`, map_size `size`, Map.reject/filter with a
# literal `fn {k, v} -> e end` are `reject`/`filter`. A map pattern with
# literal keys, `%{k => p, ..} = m`, is the variable `m` plus guards: `_`
# is `hasKey m k`, a literal or a bound variable is `get? m k = some lit`,
# and a fresh variable p is bound by `match get? m k with | some p => ..`
# around the body (a failing guard falls through to the next clause).
defmodule Counts do
  use GenServer

  @type key :: :x | :y
  @type msg :: {:incr, key()} | {:drop, key()} | {:copy_x, key()} | :zero | :reset | :prune
  @type call :: {:count, key()} | :size
  @type reply :: non_neg_integer()
  @type state :: %{key() => non_neg_integer()}

  def init(m), do: {:ok, m}

  def handle_cast({:incr, k}, m) do
    if Map.has_key?(m, k) do
      {:noreply, Map.put(m, k, Map.get(m, k, 0) + 1)}
    else
      {:noreply, Map.put(m, k, 1)}
    end
  end

  def handle_cast({:drop, k}, m) do
    case Map.fetch(m, k) do
      {:ok, 1} -> {:noreply, Map.delete(m, k)}
      {:ok, n} -> {:noreply, Map.put(m, k, n - 1)}
      :error -> {:noreply, m}
    end
  end

  # a map pattern binding a fresh variable, with the whole map aliased
  def handle_cast({:copy_x, k}, %{x: v} = m), do: {:noreply, Map.put(m, k, v)}
  def handle_cast({:copy_x, _}, m), do: {:noreply, m}

  def handle_cast(:zero, _), do: {:noreply, %{x: 0, y: 0}}

  # a map pattern with a literal value and a wildcard
  def handle_cast(:reset, %{x: 0, y: _} = m), do: {:noreply, Map.delete(m, :y)}
  def handle_cast(:reset, _), do: {:noreply, %{}}

  def handle_cast(:prune, m) do
    if map_size(m) > 1 do
      {:noreply, Map.reject(m, fn {_k, n} -> n == 0 end)}
    else
      {:noreply, m}
    end
  end

  def handle_call({:count, k}, _from, m) do
    case Map.get(m, k) do
      nil -> {:reply, 0, m}
      n -> {:reply, n, m}
    end
  end

  def handle_call(:size, _from, m), do: {:reply, map_size(m), m}
end
