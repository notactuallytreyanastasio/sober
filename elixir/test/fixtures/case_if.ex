# expect: ok
# lean: check
# `case` over an enum-typed state variable and `if` around whole bodies;
# a named atom union becomes a Lean enum.
defmodule Light do
  use GenServer

  @type colour :: :red | :amber | :green
  @type msg :: :next | {:force, colour()}
  @type state :: {colour(), non_neg_integer()}

  def init(s), do: {:ok, s}

  def handle_cast(:next, {c, n}) do
    case c do
      :red -> {:noreply, {:green, n + 1}}
      :green -> {:noreply, {:amber, n}}
      :amber -> {:noreply, {:red, n}}
    end
  end

  def handle_cast({:force, c}, {_, n}) do
    if n > 3 do
      {:noreply, {c, 0}}
    else
      {:noreply, {c, n + 1}}
    end
  end
end
