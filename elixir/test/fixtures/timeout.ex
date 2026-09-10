# expect: ok
# lean: check
# `{:noreply, state, t}` arms an untimed self-timer for :timeout, which must
# be declared in @type msg. The timeout alone puts the module in effects mode.
defmodule Idle do
  use GenServer

  @type msg :: :poke | :timeout
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_info(:poke, n), do: {:noreply, n, 50}
  def handle_info(:timeout, n), do: {:noreply, n + 1}
end
