# translate: --pid Gate=gate
# expect: ok
# lean: check
# A blocking call whose left-hand side is a pattern, not a variable: the
# resume clause matches `.reply .ok` only; any other reply is deferred.
defmodule Gate do
  use GenServer

  @type msg :: :open
  @type call :: :enter
  @type reply :: :ok | :denied
  @type state :: boolean()

  def init(s), do: {:ok, s}

  def handle_cast(:open, _), do: {:noreply, true}

  def handle_call(:enter, _from, true), do: {:reply, :ok, true}
  def handle_call(:enter, _from, false), do: {:reply, :denied, false}
end

defmodule Visitor do
  use GenServer

  @type msg :: :try
  @type state :: non_neg_integer()

  def init(s), do: {:ok, s}

  def handle_info(:try, n) do
    :ok = GenServer.call(Gate, :enter)
    {:noreply, n + 1}
  end
end
