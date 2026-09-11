# expect: error map pattern keys must be literals
# A map pattern's keys are compared by equality against the association
# list, so only literal keys (atoms, integers) are accepted; a variable key
# would need a value-directed search the translator does not attempt.
defmodule Table do
  use GenServer

  @type key :: :x | :y
  @type msg :: {:lookup, key()}
  @type state :: %{key() => non_neg_integer()}

  def init(m), do: {:ok, m}

  def handle_cast({:lookup, k}, %{k => _} = m), do: {:noreply, m}
  def handle_cast({:lookup, _}, m), do: {:noreply, m}
end
