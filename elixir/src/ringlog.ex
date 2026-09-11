# A ring buffer of log entries, reduced from a real log store (a GenServer
# whose state is its own struct: a queue of entries, a count and a cap).
# Casts push an entry, dropping the oldest when the buffer is full; calls
# return the entries oldest first, or only those of one level. A Reader
# asks through blocking calls and remembers how many entries it saw.
# Executed by ../ringlog.exs, translated by ../to_lean.exs.
#
# Translator conventions for structs, Enum and :queue:
#   defstruct f: d, ..  +  @type t :: %__MODULE__{f: T, ..}
#                                        -> structure Mod where f : T := d ..
#   @type state :: t()  (the module's own struct)
#                                        -> St constructor .mod (f : T) .., one
#                                           field per struct field, in order
#   state.f                              -> the pattern part bound to field f
#   %{state | f: e, ..}                  -> .mod .. with the named parts replaced
#   %__MODULE__{f: e}                    -> .mod with the other fields at their defaults
#   %Entry{level: :warn} / e.level       -> ({ level := .warn } : Entry) / e.level
#   v = e                                -> let v := e; ..
#   :queue.new() / :queue.in(x, q)       -> [] / (q ++ [x])
#   {_, q} = :queue.out(q0)              -> let q := List.tail q0
#   :queue.to_list(q)                    -> q
#   Enum.filter(l, &(&1.f == v))         -> List.filter (fun x1 => (x1.f = v)) l
#   length(l)                            -> List.length l

defmodule Entry do
  @type level :: :debug | :info | :warn | :error
  @type t :: %__MODULE__{level: level(), msg: non_neg_integer()}
  defstruct level: :info, msg: 0
end

defmodule Ringlog do
  use GenServer

  @default_max_entries 3

  @type t :: %__MODULE__{entries: :queue.queue(Entry.t()), count: non_neg_integer(), max_entries: non_neg_integer()}
  defstruct entries: :queue.new(), count: 0, max_entries: @default_max_entries

  @type cast :: {:push, Entry.t()}
  @type call :: :get_entries | {:by_level, Entry.level()}
  @type reply :: [Entry.t()]
  @type state :: t()

  def start_link(max), do: GenServer.start_link(__MODULE__, max, name: __MODULE__)

  @impl true
  def init(max), do: {:ok, %__MODULE__{max_entries: max}}

  @impl true
  @spec handle_call(call(), GenServer.from(), state()) :: {:reply, reply(), state()}
  def handle_call(:get_entries, _from, state) do
    {:reply, :queue.to_list(state.entries), state}
  end

  def handle_call({:by_level, level}, _from, state) do
    entries = :queue.to_list(state.entries)
    {:reply, Enum.filter(entries, &(&1.level == level)), state}
  end

  @impl true
  @spec handle_cast(cast(), state()) :: {:noreply, state()}
  def handle_cast({:push, entry}, state) do
    if state.count >= state.max_entries do
      {_, q} = :queue.out(state.entries)
      {:noreply, %{state | entries: :queue.in(entry, q)}}
    else
      {:noreply, %{state | entries: :queue.in(entry, state.entries), count: state.count + 1}}
    end
  end
end

defmodule Reader do
  use GenServer

  @type msg :: :ask_all | :ask_errors | {:log, Entry.level()}
  # entries received by the last call
  @type state :: non_neg_integer()

  @impl true
  def init(n), do: {:ok, n}

  @impl true
  @spec handle_info(msg(), state()) :: {:noreply, state()}
  def handle_info(:ask_all, _n) do
    r = GenServer.call(Ringlog, :get_entries)
    {:noreply, length(r)}
  end

  def handle_info(:ask_errors, _n) do
    r = GenServer.call(Ringlog, {:by_level, :error})
    {:noreply, length(r)}
  end

  # the message text is the number of entries the last call returned
  def handle_info({:log, level}, n) do
    GenServer.cast(Ringlog, {:push, %Entry{level: level, msg: n}})
    {:noreply, n}
  end
end
