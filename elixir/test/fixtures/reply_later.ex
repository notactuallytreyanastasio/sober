# expect: ok
# warn: not handled in every state
# lean: check
# handle_call stores the caller and answers later with GenServer.reply/2
# from a cast. The cast's state variable is narrowed to `some w` because the
# body replies to it, which leaves the `none` state uncovered: in message
# mode that is a warning, not a crash clause.
defmodule Waiter do
  use GenServer

  @type msg :: :release
  @type call :: :wait
  @type reply :: :go
  @type state :: GenServer.from() | nil

  def init(s), do: {:ok, s}

  def handle_call(:wait, from, nil), do: {:noreply, from}
  def handle_call(:wait, _from, w), do: {:reply, :go, w}

  def handle_cast(:release, w) do
    GenServer.reply(w, :go)
    {:noreply, nil}
  end
end
