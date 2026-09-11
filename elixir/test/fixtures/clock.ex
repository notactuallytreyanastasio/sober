# expect: ok
# lean: check
# The model has no clock. Every read of one -- DateTime.utc_now/0,
# System.monotonic_time/1 -- is the single opaque `Instant.now` of
# Leanactors/Time.lean, which has equality and nothing else: no order, no
# arithmetic. A module may therefore store an instant, pass it on and put it
# in a reply (which is what the real modules that read a clock mostly do),
# and anything that would order or subtract two instants is refused by the
# translator rather than modelled wrongly (see error_clock_order.ex).
defmodule Ticker do
  use GenServer

  @type msg :: :touch | :mono
  @type call :: :last | :hits
  @type reply :: {:at, DateTime.t()} | {:n, non_neg_integer()}
  @type state :: %{last: DateTime.t(), started: DateTime.t(), hits: non_neg_integer()}

  def init(n), do: {:ok, %{last: DateTime.utc_now(), started: DateTime.utc_now(), hits: n}}

  def handle_cast(:touch, s), do: {:noreply, %{s | last: DateTime.utc_now(), hits: s.hits + 1}}
  def handle_cast(:mono, s), do: {:noreply, %{s | last: System.monotonic_time(:millisecond)}}

  def handle_call(:last, _from, s), do: {:reply, {:at, s.last}, s}
  def handle_call(:hits, _from, s), do: {:reply, {:n, s.hits}, s}
end
