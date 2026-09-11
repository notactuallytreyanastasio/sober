# expect: ok
# lean: check
# A module name used as a value is a constant of the file's generated
# `Module` inductive: it can be stored in a state, sent in a message and
# compared, which is all the modules this translates ever do with one.
# Nothing can be called on it.
defmodule Router do
  use GenServer

  @type msg :: {:route, module()} | :reset | :deep
  @type call :: :impl
  @type reply :: module()
  @type state :: module()

  def init(m), do: {:ok, m}

  def handle_cast({:route, m}, _), do: {:noreply, m}
  def handle_cast(:reset, _), do: {:noreply, Fallback}
  def handle_cast(:deep, _), do: {:noreply, Loom.MCP.Client}

  def handle_call(:impl, _from, m), do: {:reply, m, m}
end
