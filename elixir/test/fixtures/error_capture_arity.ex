# expect: error a capture may only use &1
# A capture is a one-argument predicate over the list's elements, so `&2`
# has nothing to refer to; write `fn x -> .. end` for anything else.
defmodule Shelf do
  use GenServer

  @type call :: :pairs
  @type reply :: [non_neg_integer()]
  @type state :: [non_neg_integer()]

  def handle_call(:pairs, _from, l), do: {:reply, Enum.filter(l, &(&1 > &2)), l}
end
