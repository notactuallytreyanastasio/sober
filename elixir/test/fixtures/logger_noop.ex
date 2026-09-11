# expect: ok
# lean: check
# Logging is not an effect of the actor model: the BEAM's Logger is another
# process this model does not run and a log line cannot change any actor's
# state, so every `Logger.*` row of the @remote table is `:noop` and the
# call is dropped before anything is translated -- arguments included, which
# is why the interpolations below need no support at all. Nothing of this
# module's logging appears in the generated behaviour.
defmodule Chatty do
  use GenServer

  @type msg :: {:add, non_neg_integer()} | :reset
  @type state :: non_neg_integer()

  def init(n) do
    Logger.info("starting at #{n}")
    {:ok, n}
  end

  def handle_cast({:add, k}, n) do
    Logger.debug("adding #{k} to #{n}")
    {:noreply, n + k}
  end

  def handle_cast(:reset, n) do
    Logger.warning("reset from #{n}", count: n, unit: :hits)
    Logger.log(:error, "gone")
    Logger.error(fn -> "lazy" end)
    {:noreply, 0}
  end
end
