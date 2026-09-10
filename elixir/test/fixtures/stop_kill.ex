# expect: ok
# lean: check
# Self-exits with :kill: `{:stop, :kill, s}` in a GenServer and `exit(:kill)`
# in a raw receive loop are both `.exit .kill`. The model reports such a
# death to links and monitors as error (the BEAM's :killed), like any
# self-exit; only `Process.exit(p, :kill)` (process_exit.ex) is the
# untrappable `.signal p .kill`. Any other non-:normal reason (:shutdown
# here) is still error.
defmodule Boss do
  use GenServer

  @type msg :: :quit | {:shut, pid()}
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:quit, n), do: {:stop, :kill, n}

  def handle_info({:shut, p}, n) do
    Process.exit(p, :shutdown)
    {:noreply, n}
  end
end

defmodule Grunt do
  @type msg :: :work | :die
  @type state :: non_neg_integer()

  def run(n) do
    receive do
      :work -> run(n + 1)
      :die -> exit(:kill)
    end
  end
end
