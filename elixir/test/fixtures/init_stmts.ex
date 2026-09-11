# expect: ok
# lean: check
# warn: the option list is modelled as empty
# An init/1 with statements before its `{:ok, state}`: a Logger call
# (dropped), `Process.flag(:trap_exit, true)`, bindings of pure expressions
# (substituted into the state expression, since init/1 has no Lean binder of
# its own -- the state is built at the spawn site), a call to a local helper,
# and `Keyword.get(opts, :k, d)`, which takes its default because the option
# list a real init/1 is handed is not modelled.
defmodule Pool do
  use GenServer
  require Logger

  @type msg :: {:EXIT, pid(), term()} | :drain
  @type state :: {non_neg_integer(), non_neg_integer()}

  def start_link(opts), do: GenServer.start_link(__MODULE__, opts)

  @impl true
  def init(opts) do
    Logger.info("pool starting")
    Process.flag(:trap_exit, true)
    size = Keyword.get(opts, :size, 4)
    slack = Keyword.get(opts, :slack, 1)
    {:ok, {headroom(size, slack), 0}}
  end

  defp headroom(size, slack), do: size + slack

  @impl true
  def handle_info(:drain, {cap, _used}), do: {:noreply, {cap, 0}}
  def handle_info({:EXIT, _p, _r}, {cap, used}), do: {:noreply, {cap, used - 1}}
end

defmodule Boot do
  use GenServer

  @type msg :: :go
  @type state :: pid() | nil

  def init(s), do: {:ok, s}

  @impl true
  def handle_info(:go, _s) do
    {:ok, p} = GenServer.start_link(Pool, [])
    {:noreply, p}
  end
end
