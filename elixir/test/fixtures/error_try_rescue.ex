# expect: error try/rescue is only supported around external resource calls
# A `try .. rescue .. end` is dropped only when its body is nothing but
# external resource calls (`:ets.*`), which the model does not see anyway.
# Around anything else it would have to model a caught exception, which the
# translator does not do: an uncaught raise exits the process, and there is
# no way to resume from one.
defmodule Guarded do
  use GenServer

  def init(_opts), do: {:ok, %{count: 0}}

  def handle_cast(:bump, state) do
    try do
      send(self(), :bumped)
    rescue
      ArgumentError -> :ok
    end

    {:noreply, %{state | count: state.count + 1}}
  end
end
