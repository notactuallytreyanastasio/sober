# Elixir twin of Leanactors/Examples/Registry.lean.
# Run: elixir elixir/registry.exs
#
# Lean checks that a registered name always maps to a live pid or has its
# DOWN in flight. Here the same modules run on the BEAM: client 1 claims
# `a`, client 2 is told `a` is taken and claims `b`, client 1 crashes and
# `a` is freed by the DOWN, `b` is unregistered by hand and claimed again.
# Matches `Registry.taken` (1 holds a, 2 has 0 successes) and
# `Registry.freed` (a is gone) in Lean.

Code.require_file("src/registry.ex", __DIR__)

{:ok, reg} = Reg.start_link()
{:ok, c1} = GenServer.start(Client, 0)
{:ok, c2} = GenServer.start(Client, 0)

wait = fn wait, n, pred ->
  cond do
    pred.() -> :ok
    n > 0 -> Process.sleep(10); wait.(wait, n - 1, pred)
    true -> raise "timeout"
  end
end

# client 1 registers a
send(c1, {:claim, :a})
1 = :sys.get_state(c1)
{:found, ^c1} = GenServer.call(Reg, {:lookup, :a})

# client 2 is refused a, then registers b
send(c2, {:claim, :a})
0 = :sys.get_state(c2)
{:found, ^c1} = GenServer.call(Reg, {:lookup, :a})
send(c2, {:claim, :b})
1 = :sys.get_state(c2)
{:found, ^c2} = GenServer.call(Reg, {:lookup, :b})
%{a: ^c1, b: ^c2} = :sys.get_state(reg)

# client 1 crashes: its DOWN frees a
send(c1, :crash)
wait.(wait, 100, fn -> GenServer.call(Reg, {:lookup, :a}) == :not_found end)
false = Process.alive?(c1)
%{b: ^c2} = :sys.get_state(reg)

# b is unregistered by hand and claimed again
GenServer.cast(Reg, {:unregister, :b})
:not_found = GenServer.call(Reg, {:lookup, :b})
send(c2, {:claim, :b})
2 = :sys.get_state(c2)
{:found, ^c2} = GenServer.call(Reg, {:lookup, :b})
:not_found = GenServer.call(Reg, {:lookup, :c})

IO.puts("registry alive = #{Process.alive?(reg)}, final map = #{inspect(:sys.get_state(reg))}")
IO.puts("REGISTRY OK: taken refused, crash freed the name by DOWN, unregister and re-claim work")
