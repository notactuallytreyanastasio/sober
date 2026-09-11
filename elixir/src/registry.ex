# A name registry: names from a small enum map to the pid that registered
# them. A registering process is monitored and its names are dropped when
# its DOWN arrives. Executed by ../registry.exs, translated by ../to_lean.exs.
#
# Translator conventions for maps (see Leanactors/AssocList.lean):
#   @type state :: %{name() => pid()}       -> List (Name × Pid), an association list
#   %{}                                     -> []
#   Map.has_key?(m, n)                      -> AssocList.hasKey m n
#   Map.put(m, n, p) / Map.delete(m, n)     -> AssocList.insert m n p / AssocList.erase m n
#   case Map.fetch(m, n) do {:ok, p} .. :error .. end -> match AssocList.get? m n with some p .. none ..
#   Map.reject(m, fn {_n, q} -> q == p end) -> AssocList.reject m (fun (_n, q) => q = p)
# The reply is one type per file, so `{:lookup, n}` answers `{:found, pid}`
# or `:not_found` (a tagged union becomes an inductive `Reply`).

defmodule Reg do
  use GenServer

  @type name :: :a | :b | :c
  @type err :: :taken
  @type call :: {:register, name()} | {:lookup, name()}
  @type cast :: {:unregister, name()}
  @type info :: {:DOWN, reference(), :process, pid(), term()}
  @type reply :: :ok | {:error, err()} | {:found, pid()} | :not_found
  @type state :: %{name() => pid()}

  def start_link, do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  @impl true
  def init(m), do: {:ok, m}

  @impl true
  @spec handle_call(call(), GenServer.from(), state()) :: {:reply, reply(), state()}
  def handle_call({:register, n}, {pid, _ref}, m) do
    if Map.has_key?(m, n) do
      {:reply, {:error, :taken}, m}
    else
      Process.monitor(pid)
      {:reply, :ok, Map.put(m, n, pid)}
    end
  end

  def handle_call({:lookup, n}, _from, m) do
    case Map.fetch(m, n) do
      {:ok, p} -> {:reply, {:found, p}, m}
      :error -> {:reply, :not_found, m}
    end
  end

  @impl true
  @spec handle_cast(cast(), state()) :: {:noreply, state()}
  def handle_cast({:unregister, n}, m), do: {:noreply, Map.delete(m, n)}

  @impl true
  @spec handle_info(info(), state()) :: {:noreply, state()}
  def handle_info({:DOWN, _ref, :process, p, _}, m), do: {:noreply, Map.reject(m, fn {_n, q} -> q == p end)}
end

defmodule Client do
  use GenServer

  @type name :: :a | :b | :c
  @type msg :: {:claim, name()} | :crash
  # successful registrations
  @type state :: non_neg_integer()

  @impl true
  def init(k), do: {:ok, k}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()} | {:stop, term(), state()}
  def handle_info({:claim, n}, k) do
    r = GenServer.call(Reg, {:register, n})
    if r == :ok, do: {:noreply, k + 1}, else: {:noreply, k}
  end

  def handle_info(:crash, k), do: {:stop, :boom, k}
end
