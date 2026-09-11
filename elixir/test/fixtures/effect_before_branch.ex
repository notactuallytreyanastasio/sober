# translate: --pid Sink=sink
# expect: ok
# lean: check
# A statement with an effect before an `if`/`case` body. The bindings wrap
# the whole branch as `let`s, so the condition sees them; the effect is
# pushed into every branch -- prepended to the effects of whichever leaf
# runs, which is once per leaf in the text and exactly once in any run. The
# spawn counter advances before the branch, so a leaf that spawns itself
# continues the numbering.
defmodule Router do
  use GenServer

  @type msg :: {:route, non_neg_integer()} | {:grow, non_neg_integer()} | :ping
  @type state :: {pid() | nil, non_neg_integer()}

  def init(s), do: {:ok, s}

  # a send before an `if`: it happens in both branches
  def handle_cast({:route, k}, {peer, n}) do
    send(Sink, :ping)

    if k > n do
      {:noreply, {peer, k}}
    else
      {:noreply, {peer, n}}
    end
  end

  # a binding and a spawn before a `case`: `total` is a `let` around the
  # whole branch, the spawn is prepended to each leaf, and the leaf that
  # spawns again gets `fresh + 1`
  def handle_cast({:grow, k}, {peer, n}) do
    total = n + k
    w = spawn(Worker, :loop, [total])

    case peer do
      nil ->
        w2 = spawn(Worker, :loop, [total])
        send(w2, :ping)
        {:noreply, {w2, total}}

      p ->
        send(p, :ping)
        {:noreply, {w, total}}
    end
  end

  def handle_cast(:ping, s), do: {:noreply, s}
end

defmodule Sink do
  use GenServer

  @type msg :: :ping
  @type state :: non_neg_integer()

  def init(s), do: {:ok, s}

  def handle_info(:ping, n), do: {:noreply, n + 1}
end

defmodule Worker do
  @type msg :: :ping
  @type state :: non_neg_integer()

  def loop(n) do
    receive do
      :ping -> loop(n + 1)
    end
  end
end
