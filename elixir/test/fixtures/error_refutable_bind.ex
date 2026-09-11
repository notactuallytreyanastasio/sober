# expect: error the pattern is not total at Option Nat
# A binding is a Lean `let`, which has nothing to fall through to, so only a
# pattern that is total at its type may be bound. `{:ok, v}` at an Option is
# not: the key may be absent. Match on it instead.
defmodule Fetch do
  use GenServer

  @type msg :: :take
  @type state :: %{non_neg_integer() => non_neg_integer()}

  def init(m), do: {:ok, m}

  def handle_cast(:take, m) do
    {:ok, v} = Map.fetch(m, 0)
    {:noreply, Map.put(m, 1, v)}
  end
end
