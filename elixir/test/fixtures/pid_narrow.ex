# expect: ok
# lean: check
# A variable at an `Option Pid` position that the body sends to is narrowed
# to `some w`; the `none` case is left to later clauses (here the info
# catch-all). Rebuilding the state from the narrowed variable inserts `some`.
defmodule Ref do
  use GenServer

  @type msg :: {:attach, pid()} | :kick | :detach
  @type state :: pid() | nil

  def init(s), do: {:ok, s}

  def handle_info({:attach, p}, _), do: {:noreply, p}

  def handle_info(:kick, w) do
    send(w, :go)
    {:noreply, w}
  end

  def handle_info(:detach, _), do: {:noreply, nil}
  def handle_info(_, s), do: {:noreply, s}
end

defmodule Target do
  use GenServer

  @type msg :: :go
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:go, n), do: {:noreply, n + 1}
end
