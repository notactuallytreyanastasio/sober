# expect: ok
# lean: check
# The receive loop of a raw process may be a `defp`. Private/public is an
# Elixir visibility rule with no counterpart in the model, and the function
# that IS the whole life of a process is usually private, entered from a
# public wrapper (a controller action, a `spawn` target's entry point). The
# wrapper is public API and is not translated; the loop is.
defmodule Counter do
  @type msg :: {:add, non_neg_integer()} | :stop
  @type state :: non_neg_integer()

  def start(n), do: loop(n)

  defp loop(n) do
    receive do
      {:add, k} -> loop(n + k)
      :stop -> exit(:normal)
    end
  end
end
