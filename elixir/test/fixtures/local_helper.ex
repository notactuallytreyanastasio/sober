# expect: ok
# lean: check
# A private helper a handler calls. `defp` functions that are not callbacks
# and that a callback reaches become Lean definitions emitted before `beh`,
# named <module>_<function>; their calls render as calls. Argument and result
# types come from a @spec when there is one and otherwise from the types the
# helper is called at (`Term` for what use does not fix). `clamp/1` is typed
# by its @spec, `label/1` by its call sites, and `restock/2` shows a helper
# calling another helper and a body that is an `if` expression.
defmodule Shelf do
  use GenServer

  @type level :: :empty | :low | :full
  @type msg :: {:take, non_neg_integer()} | {:put, non_neg_integer()} | :restock
  @type call :: :level
  @type reply :: level()
  @type state :: non_neg_integer()

  @max 10

  def start_link, do: GenServer.start_link(__MODULE__, 0, name: __MODULE__)

  @impl true
  def init(n), do: {:ok, n}

  @spec clamp(non_neg_integer()) :: non_neg_integer()
  defp clamp(n), do: if(n > @max, do: @max, else: n)

  defp label(n) do
    cond do
      n == 0 -> :empty
      n < 3 -> :low
      true -> :full
    end
  end

  defp restock(n, by) do
    room = @max - n
    clamp(n + min_of(by, room))
  end

  defp min_of(a, b), do: if(a <= b, do: a, else: b)

  @impl true
  def handle_cast({:take, k}, n), do: {:noreply, n - k}
  def handle_cast({:put, k}, n), do: {:noreply, clamp(n + k)}
  def handle_cast(:restock, n), do: {:noreply, restock(n, 4)}

  @impl true
  def handle_call(:level, _from, n), do: {:reply, label(n), n}
end
