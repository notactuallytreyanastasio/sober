defmodule EnsembleWeb.LogsLive do
  @moduledoc """
  Live view for viewing Ensemble's application logs in real-time.
  """
  use EnsembleWeb, :live_view

  alias Ensemble.LogStore
  alias Ensemble.Settings
  alias EnsembleWeb.Components.Sidebar

  @default_log_limit 1000

  # Stable color palette for request IDs — visually distinct, readable on dark bg
  @request_colors ~w(
    text-cyan-400 text-amber-400 text-emerald-400 text-rose-400
    text-violet-400 text-sky-400 text-orange-400 text-teal-400
    text-pink-400 text-lime-400 text-indigo-400 text-yellow-400
  )

  # Module category colors for the source tag
  @module_categories %{
    "LiveView" => "badge-primary",
    "Web" => "badge-secondary",
    "GenServer" => "badge-accent",
    "App" => "badge-info",
    "Dep" => "badge-ghost opacity-50"
  }

  @impl true
  def mount(_params, _session, socket) do
    if connected?(socket) do
      Phoenix.PubSub.subscribe(Ensemble.PubSub, LogStore.topic())
    end

    entries = LogStore.get_entries()
    limit = Settings.get("log_line_limit", "#{@default_log_limit}") |> parse_limit()

    {:ok,
     socket
     |> assign(:page_title, "Logs")
     |> assign(:active_page, :logs)
     |> assign(:entries, entries)
     |> assign(:level_filter, :all)
     |> assign(:search_query, "")
     |> assign(:log_limit, limit)}
  end

  @impl true
  def handle_info({:new_log_entry, entry}, socket) do
    {:noreply, assign(socket, :entries, socket.assigns.entries ++ [entry])}
  end

  @impl true
  def handle_info(_msg, socket), do: {:noreply, socket}

  @impl true
  def handle_event("filter_level", %{"level" => level}, socket) do
    level_atom = if level == "all", do: :all, else: String.to_existing_atom(level)

    entries =
      if level_atom == :all do
        LogStore.get_entries()
      else
        LogStore.get_entries_by_level(level_atom)
      end

    {:noreply, socket |> assign(:level_filter, level_atom) |> assign(:entries, entries)}
  end

  @impl true
  def handle_event("search_logs", %{"query" => query}, socket) do
    {:noreply, assign(socket, :search_query, query)}
  end

  @impl true
  def handle_event("clear_logs", _params, socket) do
    {:noreply, assign(socket, :entries, [])}
  end

  @impl true
  def render(assigns) do
    ~H"""
    <Layouts.app
      flash={@flash}
      open_projects={assigns[:open_projects] || []}
      all_projects={assigns[:all_projects] || []}
      current_project={assigns[:current_project]}
    >
      <div class="flex h-full">
        <Sidebar.sidebar active_page={:logs} />
        <main class="flex-1 flex flex-col overflow-hidden">
          <div class="flex items-center justify-between p-3 border-b border-base-300 bg-base-200/50">
            <div class="flex items-center gap-2">
              <.icon name="hero-command-line-micro" class="size-4 text-base-content/60" />
              <h2 class="text-sm font-medium text-base-content">Application Logs</h2>
              <span class="text-xs text-base-content/40">({length(@entries)} entries)</span>
            </div>
            <div class="flex items-center gap-2">
              <form phx-change="search_logs" class="relative">
                <.icon
                  name="hero-magnifying-glass-micro"
                  class="size-3.5 absolute left-2 top-1/2 -translate-y-1/2 text-base-content/40"
                />
                <input
                  type="text"
                  name="query"
                  value={@search_query}
                  placeholder="Search logs..."
                  phx-debounce="150"
                  class="input input-xs input-bordered pl-7 w-48 bg-base-100 text-xs"
                />
              </form>
              <div class="join">
                <button
                  :for={level <- [:all, :debug, :info, :warning, :error]}
                  class={[
                    "join-item btn btn-xs",
                    if(@level_filter == level, do: "btn-primary", else: "btn-ghost")
                  ]}
                  phx-click="filter_level"
                  phx-value-level={level}
                >
                  {level |> to_string() |> String.capitalize()}
                </button>
              </div>
              <button class="btn btn-xs btn-ghost" phx-click="clear_logs">
                <.icon name="hero-trash-micro" class="size-3.5" /> Clear
              </button>
            </div>
          </div>

          <div
            id="log-entries"
            phx-hook="AutoScroll"
            class="flex-1 overflow-y-auto p-2 font-mono text-xs bg-base-100"
          >
            <div
              :for={entry <- filtered_entries(@entries, @level_filter, @search_query, @log_limit)}
              class={[
                "flex gap-2 py-0.5 hover:bg-base-300/60 px-2 rounded",
                if(app_module?(entry[:module]), do: "", else: "opacity-40")
              ]}
            >
              <span class="shrink-0 text-base-content/30">{format_timestamp(entry.timestamp)}</span>
              <span class={["shrink-0 w-14 text-right font-semibold", level_color(entry.level)]}>
                [{entry.level |> to_string() |> String.upcase() |> String.pad_leading(5)}]
              </span>
              <span
                :if={entry[:request_id]}
                class={["shrink-0", request_id_color(entry[:request_id])]}
                title={entry[:request_id]}
              >
                {String.slice(entry[:request_id] || "", -6, 6)}
              </span>
              <span
                :if={entry[:module]}
                class={[
                  "shrink-0 badge badge-xs font-normal",
                  module_badge(entry[:module])
                ]}
              >
                {short_module(entry[:module])}
              </span>
              <span class="text-base-content/90 break-all">
                {colorize_message(entry.message, @search_query)}
              </span>
            </div>
            <div
              :if={@entries == []}
              class="flex items-center justify-center h-32 text-base-content/40"
            >
              No log entries yet. Logs will appear here in real-time.
            </div>
          </div>
        </main>
      </div>
    </Layouts.app>
    """
  end

  # --- Filtering ---

  defp filtered_entries(entries, level, search_query, limit) do
    entries
    |> then(fn e -> if level == :all, do: e, else: Enum.filter(e, &(&1.level == level)) end)
    |> then(fn e ->
      if search_query == "" do
        e
      else
        query = String.downcase(search_query)
        Enum.filter(e, &String.contains?(String.downcase(&1.message), query))
      end
    end)
    |> Enum.take(-limit)
  end

  defp parse_limit(val) do
    case Integer.parse(to_string(val)) do
      {n, _} when n > 0 -> n
      _ -> @default_log_limit
    end
  end

  # --- Timestamp ---

  defp format_timestamp(timestamp) when is_integer(timestamp) do
    timestamp
    |> DateTime.from_unix!(:microsecond)
    |> Calendar.strftime("%H:%M:%S.%f")
    |> String.slice(0, 12)
  end

  defp format_timestamp(_), do: "--:--:--"

  # --- Level colors ---

  defp level_color(:debug), do: "text-base-content/50"
  defp level_color(:info), do: "text-info"
  defp level_color(:warning), do: "text-warning"
  defp level_color(:error), do: "text-error"
  defp level_color(_), do: "text-base-content/50"

  # --- #1 & #2: Module categorization and dimming ---

  defp app_module?(nil), do: true
  defp app_module?(mod) when is_atom(mod), do: app_module?(to_string(mod))

  defp app_module?(mod) when is_binary(mod) do
    String.starts_with?(mod, "Elixir.Ensemble") or
      String.starts_with?(mod, "Ensemble")
  end

  defp module_category(nil), do: "App"

  defp module_category(mod) when is_atom(mod), do: module_category(inspect(mod))

  defp module_category(mod) when is_binary(mod) do
    cond do
      String.contains?(mod, "Live") ->
        "LiveView"

      String.contains?(mod, "Web") ->
        "Web"

      not app_module?(mod) ->
        "Dep"

      String.contains?(mod, "Server") or String.contains?(mod, "Store") or
          String.contains?(mod, "Worker") ->
        "GenServer"

      true ->
        "App"
    end
  end

  defp module_badge(mod), do: Map.get(@module_categories, module_category(mod), "badge-ghost")

  defp short_module(nil), do: ""
  defp short_module(mod) when is_atom(mod), do: short_module(inspect(mod))

  defp short_module(mod) when is_binary(mod) do
    mod
    |> String.replace_leading("Elixir.", "")
    |> String.split(".")
    |> List.last("")
  end

  # --- #3: Search highlight ---

  defp colorize_message(message, search_query) do
    message
    |> escape()
    |> colorize_structured_data()
    |> highlight_search_html(search_query)
    |> Phoenix.HTML.raw()
  end

  # Highlight search matches in HTML string, skipping inside tags
  defp highlight_search_html(html, ""), do: html

  defp highlight_search_html(html, query) do
    escaped_query = escape(query)
    lower_query = String.downcase(escaped_query)

    # Split on HTML tags to only highlight in text nodes
    Regex.split(~r/(<[^>]*>)/, html, include_captures: true)
    |> Enum.map_join(fn part ->
      if String.starts_with?(part, "<") do
        part
      else
        highlight_text_node(part, lower_query)
      end
    end)
  end

  defp highlight_text_node(text, query) do
    do_highlight(text, query, "")
  end

  defp do_highlight("", _query, acc), do: acc

  defp do_highlight(rest, query, acc) do
    query_len = byte_size(query)
    lower_rest = String.downcase(rest)

    case :binary.match(lower_rest, query) do
      {pos, _len} ->
        before = binary_part(rest, 0, pos)
        match = binary_part(rest, pos, query_len)
        after_match = binary_part(rest, pos + query_len, byte_size(rest) - pos - query_len)

        new_acc =
          acc <>
            before <>
            ~s(<mark class="bg-yellow-400/25 text-yellow-200 rounded px-0.5">) <>
            match <>
            "</mark>"

        do_highlight(after_match, query, new_acc)

      :nomatch ->
        acc <> rest
    end
  end

  # --- #5: Structured data colorization ---
  # Only colorize tokens that are clearly part of structured Elixir data:
  # - Map/struct openers: %{ %Name{
  # - Closing braces: }
  # - Atoms: :foo
  # - Key-value pairs: key: "val", key: 123 (number/string colored only after a key)
  # - Booleans/nil as values: true, false, nil

  # Patterns matched in order of specificity:
  # 1. File paths with line: lib/foo/bar.ex:60
  # 2. Module.function/arity: Ensemble.Settings.get/2
  # 3. Map/struct openers: %{ %Name{
  # 4. Closing braces: }
  # 5. Key-value pairs: key: "val", key: 123
  # 6. Atoms: :foo
  # 7. Booleans/nil as values
  @structured_re ~r{
    (?:[\w./]+\.ex[s]?:\d+)                                          # file:line
    | (?:[A-Z]\w+(?:\.[A-Z]\w+)+\.\w+/\d+)                          # Module.func/arity
    | (?:[A-Z]\w+(?:\.[A-Z]\w+)+)                                    # Module.Name
    | (?:%\w*\{)                                                      # map/struct opener
    | (?:\})                                                          # closing brace
    | (?::\w+(?=\s*[=&]))                                             # atom before = or &
    | (?::\w+)                                                        # atom
    | (?:\w+:\s+(?:&quot;[^&]*?&quot;|"[^"]*"|\d+\.\d+|\d+|true|false|nil)) # key: value
    | (?:\b(?:true|false|nil)\b(?=[,\s\}]))                           # bare bool/nil
  }x

  defp colorize_structured_data(text) when is_binary(text) do
    Regex.replace(@structured_re, text, &colorize_token/1)
  end

  defp colorize_token(match) do
    cond do
      Regex.match?(~r/\.exs?:\d+$/, match) -> colorize_file_ref(match)
      Regex.match?(~r/^[A-Z]\w+(\.\w+)+\/\d+$/, match) -> colorize_mfa(match)
      Regex.match?(~r/^[A-Z]\w+(\.[A-Z]\w+)+$/, match) -> colorize_span(match, "sky")
      struct_or_brace?(match) -> colorize_span(match, "violet")
      Regex.match?(~r/^\w+:\s+/, match) -> colorize_key_value(match)
      Regex.match?(~r/^:\w+$/, match) -> colorize_span(match, "cyan")
      match in ["true", "false", "nil"] -> colorize_span(match, "amber")
      true -> match
    end
  end

  defp struct_or_brace?(match), do: match == "}" or Regex.match?(~r/^%\w*\{$/, match)

  defp colorize_span(match, color), do: ~s(<span class="text-#{color}-400">#{match}</span>)

  # lib/ensemble/projects.ex:60 → path in underline, line number in amber
  defp colorize_file_ref(match) do
    [path, line] = String.split(match, ":", parts: 2)

    ~s(<span class="text-sky-400 underline decoration-sky-400/30">#{path}</span>) <>
      ~s(:<span class="text-amber-400">#{line}</span>)
  end

  # Ensemble.Settings.get/2 → module in sky, function in teal, arity in amber
  defp colorize_mfa(match) do
    [mod_func, arity] = String.split(match, "/", parts: 2)
    parts = String.split(mod_func, ".")
    {func, mod_parts} = List.pop_at(parts, -1)
    mod = Enum.join(mod_parts, ".")

    ~s(<span class="text-sky-400">#{mod}</span>.) <>
      ~s(<span class="text-teal-400">#{func}</span>) <>
      ~s(/<span class="text-amber-400">#{arity}</span>)
  end

  defp colorize_key_value(match) do
    [key_part, value_part] = String.split(match, ~r/(?<=:\s)/, parts: 2)
    value_part = String.trim(value_part)

    colored_value =
      cond do
        String.starts_with?(value_part, "\"") or String.starts_with?(value_part, "&quot;") ->
          ~s(<span class="text-emerald-400">#{value_part}</span>)

        Regex.match?(~r/^\d/, value_part) ->
          ~s(<span class="text-amber-400">#{value_part}</span>)

        value_part in ["true", "false", "nil"] ->
          ~s(<span class="text-amber-400">#{value_part}</span>)

        true ->
          value_part
      end

    ~s(<span class="text-cyan-400">#{key_part}</span>#{colored_value})
  end

  defp escape(text) do
    text
    |> Phoenix.HTML.html_escape()
    |> Phoenix.HTML.safe_to_string()
  end

  # --- #4: Request ID coloring ---

  defp request_id_color(nil), do: "text-base-content/30"

  defp request_id_color(request_id) do
    index = :erlang.phash2(request_id, length(@request_colors))
    Enum.at(@request_colors, index)
  end
end
