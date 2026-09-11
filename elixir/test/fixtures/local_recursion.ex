# expect: ok
# lean: check
# Recursive local helpers. `total/1` recurses on the tail of its list
# argument, which Lean accepts as structural recursion, so it is emitted as
# an ordinary `def`. `since/1` counts down on a number, which Lean does not
# see as a constructor step, so it takes a `fuel : Nat` parameter, returns
# the default value of its result type when the fuel runs out, and is called
# with the documented constant `localFuel`.
defmodule Tally do
  use GenServer

  @type msg :: {:push, non_neg_integer()}
  @type call :: :total | :steps
  @type reply :: non_neg_integer()
  @type state :: [non_neg_integer()]

  def start_link, do: GenServer.start_link(__MODULE__, [], name: __MODULE__)

  @impl true
  def init(l), do: {:ok, l}

  @spec total([non_neg_integer()]) :: non_neg_integer()
  defp total([]), do: 0
  defp total([h | t]), do: h + total(t)

  @spec since(non_neg_integer()) :: non_neg_integer()
  defp since(0), do: 0
  defp since(n), do: 1 + since(n - 1)

  @impl true
  def handle_cast({:push, k}, l), do: {:noreply, l ++ [k]}

  @impl true
  def handle_call(:total, _from, l), do: {:reply, total(l), l}
  def handle_call(:steps, _from, l), do: {:reply, since(length(l)), l}
end
