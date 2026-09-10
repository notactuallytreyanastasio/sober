# Elixir twin of Leanactors/Examples/Ttl.lean.
# Run: elixir elixir/ttl.exs
#
# Lean checks that the cache never holds 0 (a `put 0` raises instead) under
# every interleaving of puts, gets and timer firings. Here: put, get, let
# the 200ms TTL expire, get again, a Reader process asks, then put 0 and
# watch the cache die with an ArgumentError.

Code.require_file("src/ttl.ex", __DIR__)

cache = Cache.start()
^cache = Process.whereis(Cache)

get = fn ->
  send(Cache, {:get, self()})
  receive do
    {:value, v} -> v
  after
    1000 -> raise "no reply from the cache"
  end
end

send(Cache, {:put, 5})
5 = get.()
Process.sleep(400)                     # past the 200ms TTL
nil = get.()                           # expired
send(Cache, {:put, 7})
7 = get.()
7 = get.()                             # a get resets the TTL, like any message

reader = spawn(Reader, :run, [0])
send(reader, :ask)
Process.sleep(50)
{:messages, []} = Process.info(reader, :messages)   # the reply was consumed
true = Process.alive?(reader)

ref = Process.monitor(cache)
send(Cache, {:put, 0})
reason =
  receive do
    {:DOWN, ^ref, :process, ^cache, r} -> r
  after
    1000 -> raise "the cache did not die on put 0"
  end

{%ArgumentError{}, _stack} = reason
nil = Process.whereis(Cache)

IO.puts("cache alive   = #{Process.alive?(cache)}")
IO.puts("exit reason   = #{inspect(elem(reason, 0).__struct__)}")
IO.puts("TTL OK: put/get/expire agree with the model and put 0 kills the cache")
