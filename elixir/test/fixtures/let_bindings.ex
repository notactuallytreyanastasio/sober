# expect: ok
# lean: check
# Bindings. `x = e` is a Lean `let` around the clause result, a binding
# inside a block expression is a nested `let`, and a tuple pattern
# `{a, b} = e` is `let (a, b) := e` -- only a pattern that is total at its
# type may be bound, because a `let` has nothing to fall through to.
# `elem/2` and `tuple_size/1` read the same pair, the one tuple the model
# has as a value (a map entry).
defmodule Entries do
  use GenServer

  @type msg :: :bump | :first | :widen
  @type call :: :size
  @type reply :: non_neg_integer()
  @type state :: %{non_neg_integer() => non_neg_integer()}

  def init(m), do: {:ok, m}

  # a plain binding, and a block expression with a binding of its own
  def handle_cast(:bump, m) do
    d = 2

    {:noreply,
     Map.put(m, 0, (
        base = Map.get(m, 0, 0)
        base + d
      ))}
  end

  # a tuple pattern binding: the arm variable is a map entry
  def handle_cast(:first, m) do
    case Enum.at(m, 0) do
      nil ->
        {:noreply, m}

      e ->
        {k, v} = e
        {:noreply, Map.put(m, k, v + 1)}
    end
  end

  # elem/2 and tuple_size/1 on the same pair
  def handle_cast(:widen, m) do
    case Enum.at(m, 0) do
      nil -> {:noreply, m}
      e -> {:noreply, Map.put(m, elem(e, 0), elem(e, 1) * tuple_size(e))}
    end
  end

  def handle_call(:size, _from, m), do: {:reply, map_size(m), m}
end
