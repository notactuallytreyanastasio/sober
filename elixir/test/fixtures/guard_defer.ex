# expect: ok
# lean: check
# A receive loop with no catch-all: a guard that fails with no clause to
# fall through to must not consume the message, so it is re-enqueued to
# self (the same defer clause that handles unmatched tags).
defmodule Pool do
  @type msg :: {:take, non_neg_integer()} | {:put, non_neg_integer()}
  @type state :: non_neg_integer()

  def run(n) do
    receive do
      {:take, k} when k <= n -> run(n - k)
      {:put, k} -> run(n + k)
    end
  end
end
