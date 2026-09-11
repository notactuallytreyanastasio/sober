defmodule Ensemble.LogStore do
  @moduledoc """
  In-memory ring buffer for application log entries.

  Acts as a custom Logger handler that captures recent log entries
  and broadcasts them via PubSub for live streaming to the UI.
  """
  use GenServer

  @default_max_entries 1000
  @pubsub_topic "logs"

  defstruct entries: :queue.new(), count: 0, max_entries: @default_max_entries

  # --- Public API ---

  def start_link(opts \\ []) do
    max = Keyword.get(opts, :max_entries, @default_max_entries)
    GenServer.start_link(__MODULE__, max, name: Keyword.get(opts, :name, __MODULE__))
  end

  @doc "Returns all stored log entries in chronological order."
  def get_entries(server \\ __MODULE__) do
    GenServer.call(server, :get_entries)
  end

  @doc "Returns log entries filtered by level."
  def get_entries_by_level(server \\ __MODULE__, level) when is_atom(level) do
    server
    |> get_entries()
    |> Enum.filter(&(&1.level == level))
  end

  @doc "Pushes a new log entry into the buffer. Called by the Logger handler."
  def push_entry(server \\ __MODULE__, entry) do
    GenServer.cast(server, {:push, entry})
  end

  @doc "Returns the PubSub topic for log streaming."
  def topic, do: @pubsub_topic

  # --- Logger handler callbacks ---

  @doc "Logger handler for :logger (Erlang/OTP logger)."
  def log(%{level: level, msg: msg, meta: meta}, _config) do
    message = format_message(msg)
    timestamp = Map.get(meta, :time, :os.system_time(:microsecond))

    entry = %{
      level: level,
      message: message,
      timestamp: timestamp,
      module: Map.get(meta, :mcp_module, Map.get(meta, :module)),
      function: Map.get(meta, :function),
      line: Map.get(meta, :line),
      request_id: Map.get(meta, :request_id)
    }

    push_entry(entry)
  end

  defp format_message({:string, msg}), do: IO.chardata_to_string(msg)
  defp format_message({:report, report}), do: inspect(report)
  defp format_message(msg) when is_binary(msg), do: msg
  defp format_message(msg), do: inspect(msg)

  # --- GenServer callbacks ---

  @impl true
  def init(max_entries) do
    {:ok, %__MODULE__{max_entries: max_entries}}
  end

  @impl true
  def handle_call(:get_entries, _from, state) do
    entries = :queue.to_list(state.entries)
    {:reply, entries, state}
  end

  @impl true
  def handle_cast({:push, entry}, state) do
    Phoenix.PubSub.broadcast(Ensemble.PubSub, @pubsub_topic, {:new_log_entry, entry})

    {entries, count} =
      if state.count >= state.max_entries do
        {_, q} = :queue.out(state.entries)
        {:queue.in(entry, q), state.count}
      else
        {:queue.in(entry, state.entries), state.count + 1}
      end

    {:noreply, %{state | entries: entries, count: count}}
  end
end
