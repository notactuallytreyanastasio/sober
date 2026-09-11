# expect: error receive loop collect is called outside tail position
# A receive loop models the whole life of a process: its tail says what the
# process does next, and a body that falls out of the loop exits it. That
# reading is only faithful when every call to the loop is in tail position.
# `total = collect(0)` is a blocking receive whose value the caller goes on
# to use -- the model's only blocking form is `GenServer.call`, which splits
# the clause into an await state, and there is nothing here to split.
defmodule Collector do
  @type msg :: {:item, non_neg_integer()} | :done
  @type state :: non_neg_integer()

  def run(_n) do
    total = collect(0)
    send(self(), {:item, total})
    exit(:normal)
  end

  defp collect(n) do
    receive do
      {:item, k} -> collect(n + k)
      :done -> n
    end
  end
end
