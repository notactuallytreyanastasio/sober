# Elixir twin of Leanactors/Examples/Bank.lean.
# Run: elixir elixir/bank.exs
#
# The @spec below is what Elixir's set-theoretic type checker can see.
# It proves each clause maps a non_neg_integer() state to a
# non_neg_integer() state *if* the guard holds. It cannot prove the
# state stays non-negative across an arbitrary interleaving of casts
# from many clients. Lean's `balance_never_negative` proves that.

defmodule Bank do
  use GenServer

  @type msg ::
          {:deposit, non_neg_integer()}
          | {:withdraw, non_neg_integer()}
          | {:balance, pid()}

  def start_link(initial), do: GenServer.start_link(__MODULE__, initial)

  @impl true
  def init(b), do: {:ok, b}

  @impl true
  @spec handle_cast(msg(), non_neg_integer()) :: {:noreply, non_neg_integer()}
  def handle_cast({:deposit, n}, b), do: {:noreply, b + n}
  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}
  def handle_cast({:withdraw, _}, b), do: {:noreply, b}

  def handle_cast({:balance, to}, b) do
    send(to, {:reply, b})
    {:noreply, b}
  end
end

defmodule Client do
  # Mirrors `St.client (seen : Option Int)`.
  def start, do: spawn(fn -> loop(nil) end)

  defp loop(seen) do
    receive do
      {:reply, v} -> loop(v)
      {:read, from} -> send(from, {:seen, self(), seen}); loop(seen)
    end
  end

  def read(pid) do
    send(pid, {:read, self()})
    receive do
      {:seen, ^pid, v} -> v
    end
  end
end

{:ok, bank} = Bank.start_link(10)
c1 = Client.start()
c2 = Client.start()

# Same stimulus as `Bank.stimulus` in Lean, in the same order.
for m <- [
      {:withdraw, 4},
      {:deposit, 3},
      {:withdraw, 100},
      {:balance, c1},
      {:withdraw, 9},
      {:balance, c2}
    ],
    do: GenServer.cast(bank, m)

# `:sys.get_state` is a synchronous call, so it lands after all the casts.
final_bank = :sys.get_state(bank)
# Give the two client mailboxes a moment; a `read` is a sync round-trip.
seen1 = Client.read(c1)
seen2 = Client.read(c2)

IO.puts("bank    = #{final_bank}")
IO.puts("client1 = #{inspect(seen1)}")
IO.puts("client2 = #{inspect(seen2)}")

expected = {0, 9, 0}
actual = {final_bank, seen1, seen2}

if actual == expected do
  IO.puts("MATCH: Elixir trace agrees with Lean `#eval snapshot final 3`")
else
  IO.puts("MISMATCH: expected #{inspect(expected)}, got #{inspect(actual)}")
  System.halt(1)
end
