# Elixir twin of Leanactors/Examples/Lock.lean.
# Run: elixir elixir/lock.exs [clients] [ticks]
#
# Lean proves `mutex_forever`: under every interleaving, no two clients are
# `:holding` at once. Here we run the same protocol on the BEAM with random
# tick timing and check the property on an event log. A property test cannot
# replace the proof, but disagreement would mean the model is wrong.

defmodule Lock do
  use GenServer
  # state: {holder :: pid() | nil, queue :: [pid()]}
  def start_link, do: GenServer.start_link(__MODULE__, {nil, []}, name: __MODULE__)
  @impl true
  def init(s), do: {:ok, s}

  @impl true
  def handle_cast({:acquire, p}, {nil, q}) do
    send(p, :grant)
    {:noreply, {p, q}}
  end
  def handle_cast({:acquire, p}, {h, q}), do: {:noreply, {h, q ++ [p]}}
  def handle_cast({:release, p}, {p, []}), do: {:noreply, {nil, []}}
  def handle_cast({:release, p}, {p, [n | rest]}) do
    send(n, :grant)
    {:noreply, {n, rest}}
  end
  def handle_cast({:release, _}, s), do: {:noreply, s}
end

defmodule Client do
  # phase :: :idle | :waiting | :holding, driven by :tick (env) and :grant (Lock)
  def start(log), do: spawn_link(fn -> loop(:idle, log) end)

  defp loop(:idle, log) do
    receive do
      :tick -> GenServer.cast(Lock, {:acquire, self()}); loop(:waiting, log)
      _ -> loop(:idle, log)
    end
  end
  defp loop(:waiting, log) do
    receive do
      :grant ->
        send(log, {:enter, self(), System.monotonic_time()})
        loop(:holding, log)
      _ -> loop(:waiting, log)
    end
  end
  defp loop(:holding, log) do
    receive do
      :tick ->
        send(log, {:leave, self(), System.monotonic_time()})
        GenServer.cast(Lock, {:release, self()})
        loop(:idle, log)
      _ -> loop(:holding, log)
    end
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
clients = for _ <- 1..n, do: Client.start(log)

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
