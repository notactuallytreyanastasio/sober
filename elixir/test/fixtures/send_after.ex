# expect: ok
# lean: check
# Process.send_after/3 to self() and to a pid carried by the message.
defmodule Alarm do
  use GenServer

  @type msg :: :arm | :ring | {:remind, pid()}
  @type state :: boolean()

  def init(s), do: {:ok, s}

  def handle_info(:arm, false) do
    Process.send_after(self(), :ring, 100)
    {:noreply, true}
  end

  def handle_info(:ring, _), do: {:noreply, false}

  def handle_info({:remind, p}, s) do
    Process.send_after(p, :ring, 100)
    {:noreply, s}
  end

  def handle_info(_, s), do: {:noreply, s}
end
