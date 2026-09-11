# expect: error has no field z
# A struct literal, pattern or update may only name declared fields: the
# defstruct and `@type t` are the oracle, as everywhere else.
defmodule Point do
  @type t :: %__MODULE__{x: non_neg_integer()}
  defstruct x: 0
end

defmodule Board do
  use GenServer

  @type cast :: {:move, Point.t()}
  @type state :: non_neg_integer()

  def handle_cast({:move, %Point{z: z}}, n), do: {:noreply, n + z}
end
