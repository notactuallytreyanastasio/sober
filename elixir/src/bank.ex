# The bank as ordinary Elixir. Executed by ../bank.exs, translated by ../to_lean.exs.

defmodule Bank do
  use GenServer

  @type msg :: {:deposit, non_neg_integer()} | {:withdraw, non_neg_integer()} | {:balance, pid()}
  @type state :: integer()

  def start_link(initial), do: GenServer.start_link(__MODULE__, initial)

  @impl true
  def init(b), do: {:ok, b}

  @impl true
  @spec handle_cast(msg(), state()) :: {:noreply, state()}
  def handle_cast({:deposit, n}, b), do: {:noreply, b + n}
  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}
  def handle_cast({:withdraw, _}, b), do: {:noreply, b}

  def handle_cast({:balance, to}, b) do
    send(to, {:reply, b})
    {:noreply, b}
  end
end

defmodule Client do
  use GenServer

  @type msg :: {:reply, integer()}
  @type state :: integer() | nil

  def start_link, do: GenServer.start_link(__MODULE__, nil)

  @impl true
  def init(s), do: {:ok, s}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info({:reply, v}, _), do: {:noreply, v}
end
