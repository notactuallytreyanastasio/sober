# translate: --pid Counter=counter
# expect: ok
# lean: check
# Two blocking calls in one handler: the first await state captures `acc`,
# the second captures `acc` and the first reply `a`.
defmodule Counter do
  use GenServer

  @type msg :: :bump
  @type call :: :get
  @type reply :: non_neg_integer()
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_cast(:bump, n), do: {:noreply, n + 1}
  def handle_call(:get, _from, n), do: {:reply, n, n}
end

defmodule Prober do
  use GenServer

  @type msg :: :probe
  @type state :: non_neg_integer()

  def init(s), do: {:ok, s}

  def handle_info(:probe, acc) do
    a = GenServer.call(Counter, :get)
    b = GenServer.call(Counter, :get)
    {:noreply, acc + a + b}
  end
end
