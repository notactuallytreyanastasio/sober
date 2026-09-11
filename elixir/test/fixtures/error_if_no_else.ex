# expect: error an `if` with no `else` is nil
# An `if` with no `else` is nil, and the model has nil only at an Option
# type: anywhere else the other branch has to be spelled out.
defmodule Half do
  use GenServer

  @type msg :: {:set, non_neg_integer()}
  @type state :: non_neg_integer()

  def init(s), do: {:ok, s}

  def handle_cast({:set, v}, n), do: {:noreply, if(v > n, do: v)}
end
