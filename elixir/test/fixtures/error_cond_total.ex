# expect: error the last clause of a `cond` must be `true ->`
# A `cond` that falls off the end raises CondClauseError, which an
# expression in the model cannot do, so the last clause must be `true ->`.
defmodule Pick do
  use GenServer

  @type msg :: {:set, integer()}
  @type state :: integer()

  def init(s), do: {:ok, s}

  def handle_cast({:set, v}, n) do
    {:noreply,
     cond do
       v > 0 -> v
       v < 0 -> n
     end}
  end
end
