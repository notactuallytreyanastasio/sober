# Elixir twin of Leanactors/Examples/Lock.lean.
# Run: elixir elixir/lock.exs [clients] [ticks]
#
# Lean proves `mutex_forever`: under every interleaving, no two clients are
# `:holding` at once. Here we run the same protocol on the BEAM with random
# tick timing and check the property on an event log. A property test cannot
# replace the proof, but disagreement would mean the model is wrong.

Code.require_file("src/lock.ex", __DIR__)

# Observation shim: the shared Client module is pure protocol. To log
# critical-section entry and exit we wrap its callbacks in a subclass-like
# module that forwards to Client.handle_info/2 and reports phase changes.
defmodule ObservedClient do
  use GenServer
  def start_link(log), do: GenServer.start_link(__MODULE__, {:idle, log})
  @impl true
  def init(s), do: {:ok, s}
  @impl true
  def handle_info(msg, {phase, log}) do
    {:noreply, phase2} = Client.handle_info(msg, phase)
    case {phase, phase2} do
      {:waiting, :holding} -> send(log, {:enter, self(), System.monotonic_time()})
      {:holding, :idle} -> send(log, {:leave, self(), System.monotonic_time()})
      _ -> :ok
    end
    {:noreply, {phase2, log}}
  end
end

defmodule Log do
  def start, do: spawn(fn -> loop([]) end)
  defp loop(acc) do
    receive do
      {:dump, from} -> send(from, {:events, Enum.reverse(acc)}); loop(acc)
      ev -> loop([ev | acc])
    end
  end
  def dump(pid) do
    send(pid, {:dump, self()})
    receive do {:events, evs} -> evs end
  end
end

[n, ticks] =
  case System.argv() do
    [a, b] -> [String.to_integer(a), String.to_integer(b)]
    _ -> [5, 2000]
  end

{:ok, _} = Lock.start_link()
log = Log.start()
clients = for _ <- 1..n, do: (fn -> {:ok, c} = ObservedClient.start_link(log); c end).()

# Chaos driver: ticks to random clients at random times, like Lean's EnvStep.
for _ <- 1..ticks do
  send(Enum.random(clients), :tick)
  if :rand.uniform(4) == 1, do: Process.sleep(0)
end
Process.sleep(200)

events = Log.dump(log) |> Enum.sort_by(fn {_, _, t} -> t end)

{max_inside, violations} =
  Enum.reduce(events, {0, 0, MapSet.new()}, fn
    {:enter, p, _}, {mx, v, inside} ->
      inside = MapSet.put(inside, p)
      sz = MapSet.size(inside)
      {max(mx, sz), (if sz > 1, do: v + 1, else: v), inside}
    {:leave, p, _}, {mx, v, inside} ->
      {mx, v, MapSet.delete(inside, p)}
  end)
  |> then(fn {mx, v, _} -> {mx, v} end)

IO.puts("clients=#{n} ticks=#{ticks} enters=#{Enum.count(events, &match?({:enter, _, _}, &1))} max_inside=#{max_inside}")

if violations == 0 do
  IO.puts("MUTEX OK: never more than one client holding")
else
  IO.puts("MUTEX VIOLATED #{violations} times")
  System.halt(1)
end
