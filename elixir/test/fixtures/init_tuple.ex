# expect: ok
# lean: check
# GenServer.start with a tuple argument and an init/1 whose parameter is a
# tuple pattern: the child's initial state is init's expression with the
# parts bound positionally, rendered in the parent's environment (self()
# becomes `me`).
defmodule Parent do
  use GenServer

  @type msg :: :go | {:done, non_neg_integer()}
  @type state :: {pid() | nil, non_neg_integer()}

  def init(s), do: {:ok, s}

  def handle_info(:go, {nil, r}) do
    {:ok, pid} = GenServer.start(Child, {self(), 3})
    {:noreply, {pid, r}}
  end

  def handle_info({:done, v}, {_, r}), do: {:noreply, {nil, r + v}}
  def handle_info(_, s), do: {:noreply, s}
end

defmodule Child do
  use GenServer

  @type msg :: :run
  @type state :: {pid(), non_neg_integer()}

  def init({parent, n}), do: {:ok, {parent, n + 1}}

  def handle_info(:run, {parent, n}) do
    send(parent, {:done, n})
    {:stop, :normal, {parent, n}}
  end
end
