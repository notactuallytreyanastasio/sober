# expect: error mutually recursive local helpers
# Two helpers that call each other would need a Lean `mutual` block, which
# the translator does not emit: it is an error naming both.
defmodule Parity do
  use GenServer

  @type msg :: {:set, non_neg_integer()}
  @type call :: :even
  @type reply :: boolean()
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  defp even?(0), do: true
  defp even?(n), do: odd?(n - 1)

  defp odd?(0), do: false
  defp odd?(n), do: even?(n - 1)

  def handle_cast({:set, k}, _n), do: {:noreply, k}
  def handle_call(:even, _from, n), do: {:reply, even?(n), n}
end
