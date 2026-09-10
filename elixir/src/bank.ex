# The bank as ordinary Elixir. Executed by ../bank.exs, translated by ../to_lean.exs.
#
# Bank answers `:balance` synchronously via handle_call/3. Client asks with a
# blocking GenServer.call inside handle_info/2. The translator models the
# call as a message carrying the caller pid plus a `reply` message, and
# splits the client clause at the call into an await state.

defmodule Bank do
  use GenServer

  @type msg :: {:deposit, non_neg_integer()} | {:withdraw, non_neg_integer()}
  @type call :: :balance
  @type reply :: integer()
  @type state :: integer()

  def start_link(initial), do: GenServer.start_link(__MODULE__, initial, name: __MODULE__)

  @impl true
  def init(b), do: {:ok, b}

  @impl true
  @spec handle_cast(msg(), state()) :: {:noreply, state()}
  def handle_cast({:deposit, n}, b), do: {:noreply, b + n}
  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}
  def handle_cast({:withdraw, _}, b), do: {:noreply, b}

  @impl true
  @spec handle_call(call(), GenServer.from(), state()) :: {:reply, reply(), state()}
  def handle_call(:balance, _from, b), do: {:reply, b, b}
end

defmodule Client do
  use GenServer

  @type msg :: :tick | :audit
  @type state :: integer() | nil

  def start_link, do: GenServer.start_link(__MODULE__, nil)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:tick, _) do
    v = GenServer.call(Bank, :balance)
    {:noreply, v}
  end

  # Two blocking calls in one handler: the second await state captures `a`.
  def handle_info(:audit, _) do
    a = GenServer.call(Bank, :balance)
    b = GenServer.call(Bank, :balance)
    {:noreply, a + b}
  end
end
