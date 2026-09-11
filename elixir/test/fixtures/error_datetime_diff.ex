# expect: error the model has no clock
# DateTime.diff/2 has a row in the @remote table whose action is an error
# with a reason: the arithmetic it asks for does not exist in the model.
defmodule Elapsed do
  use GenServer

  @type msg :: :tick
  @type state :: %{since: DateTime.t(), ms: non_neg_integer()}

  def init(_n), do: {:ok, %{since: DateTime.utc_now(), ms: 0}}

  def handle_cast(:tick, s), do: {:noreply, %{s | ms: DateTime.diff(DateTime.utc_now(), s.since)}}
end
