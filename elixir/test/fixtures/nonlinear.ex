# expect: ok
# lean: check
# A non-linear pattern (`p` in the message and in the state) becomes a fresh
# name plus an equality guard; through `Option` the state part is `some p'`.
# The failing guard falls through to the catch-all cast clause.
defmodule Owner do
  use GenServer

  @type msg :: {:claim, pid()} | {:drop, pid()}
  @type state :: pid() | nil

  def init(s), do: {:ok, s}

  def handle_cast({:claim, p}, nil), do: {:noreply, p}
  def handle_cast({:drop, p}, p), do: {:noreply, nil}
  def handle_cast(_, s), do: {:noreply, s}
end
