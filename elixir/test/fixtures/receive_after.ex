# expect: ok
# lean: check
# `receive ... after`: the loop's state gets a hidden trailing `gen` field
# and the after message carries a generation. A spawn starts the child at
# generation 0 and arms `after_run 0`; every re-entry (a `run(e)` tail, a
# failed guard, the defer clause, the after body) moves to `gen + 1` and
# arms `after_run (gen + 1)`; `exit` keeps the state, gen included. The
# after body runs only when the carried generation is the current one; a
# stale after message is consumed and ignored, not deferred.
defmodule Ticker do
  @type msg :: {:set, non_neg_integer()} | :stop | :ping
  @type state :: non_neg_integer()

  def run(n) do
    receive do
      {:set, x} when x > n -> run(x)
      :stop -> exit(:normal)
    after
      100 -> run(n + 1)
    end
  end
end

defmodule Boss do
  use GenServer

  @type msg :: :go
  @type state :: pid() | nil

  def handle_cast(:go, _) do
    pid = spawn(Ticker, :run, [0])
    {:noreply, pid}
  end
end
