# Elixir twin of Leanactors/Examples/Bank.lean.
# Run: elixir elixir/bank.exs
#
# The @spec below is what Elixir's set-theoretic type checker can see.
# It proves each clause maps a non_neg_integer() state to a
# non_neg_integer() state *if* the guard holds. It cannot prove the
# state stays non-negative across an arbitrary interleaving of casts
# from many clients. Lean's `balance_never_negative` proves that.

Code.require_file("src/bank.ex", __DIR__)

{:ok, bank} = Bank.start_link(10)
{:ok, c1} = Client.start_link()
{:ok, c2} = Client.start_link()

# Same interleaving as `Bank.stim1` / `Bank.stim2` in Lean.
for m <- [{:withdraw, 4}, {:deposit, 3}, {:withdraw, 100}], do: GenServer.cast(bank, m)
send(c1, :tick)
# get_state queues behind :tick, whose handler blocks on GenServer.call(Bank, :balance)
seen1 = :sys.get_state(c1)
GenServer.cast(bank, {:withdraw, 9})
send(c2, :tick)
seen2 = :sys.get_state(c2)
final_bank = :sys.get_state(bank)

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
