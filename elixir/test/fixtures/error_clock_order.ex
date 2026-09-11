# expect: error the model has no clock
# Two instants may be compared for equality and nothing else, so `<` on one
# is a translation error and not a Lean error: the model would otherwise
# claim an ordering it does not have.
defmodule Stale do
  use GenServer

  @type msg :: :check
  @type state :: %{seen: DateTime.t(), cut: DateTime.t()}

  def init(_n), do: {:ok, %{seen: DateTime.utc_now(), cut: DateTime.utc_now()}}

  def handle_cast(:check, s) do
    if s.seen < s.cut do
      {:noreply, %{s | seen: DateTime.utc_now()}}
    else
      {:noreply, s}
    end
  end
end
