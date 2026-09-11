# expect: ok
# lean: check
# `a |> f(b)` is `f(a, b)`, rewritten over the whole module before anything
# else looks at it, so a pipeline of three stages is nested calls and the
# generated Lean shows no trace of the pipe.
defmodule Pipes do
  use GenServer

  @type msg :: {:add, integer()} | :trim
  @type call :: :top
  @type reply :: [integer()]
  @type state :: [integer()]

  def init(s), do: {:ok, s}

  def handle_cast({:add, n}, l), do: {:noreply, l ++ [n]}

  # three stages
  def handle_cast(:trim, l) do
    {:noreply,
     l
     |> Enum.filter(fn x -> x > 0 end)
     |> Enum.reverse()
     |> Enum.take(3)}
  end

  def handle_call(:top, _from, l) do
    {:reply, l |> Enum.reverse() |> Enum.take(1), l}
  end
end
