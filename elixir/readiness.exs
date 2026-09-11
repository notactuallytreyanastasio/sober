# Readiness harness: which real-world modules does elixir/to_lean.exs
# translate, and what stops the others?
#
#   elixir elixir/readiness.exs [--markdown | --json] [--strict] [--no-translate]
#                               [--jobs N] [--exclude FILE]... PATH...
#   elixir elixir/readiness.exs --json --update-baseline FILE PATH...
#   elixir elixir/readiness.exs --check-baseline FILE [PATH...]
#
# PATH is a .ex file or a directory (searched recursively for *.ex). For
# every module that `use GenServer` (or defines GenServer callbacks) or
# contains a `receive`, the harness
#
#   1. runs the translator on the module's file (dry: output discarded,
#      stderr captured; a "no registered name for X" error is retried with
#      `--pid X=x`, since that is configuration, not a construct) and records
#      whether the file translated, and
#   2. walks the module's AST itself against @supported, the allowlist of
#      forms the translator accepts (derived from the header of to_lean.exs
#      and the fixture names), reporting EVERY unsupported construct with
#      file:line and a stable kind (`Map.pop/2`, `try/rescue`, `variable
#      binding x = e`, `no @type state (untyped mode not available)`, ...),
#      so the report is complete even though the translator stops at its
#      first error.
#
# Findings have two severities: a blocker makes the translator fail; a note
# is something the translator silently ignores or that only needs a flag
# (`terminate/2`, a send target registered in another file). A module with
# no blockers whose file translated is "translated: yes".
#
# Output: a text report (file:line: kind -- detail) with a summary and the
# blocking constructs by frequency; `--markdown` renders the same as the
# tables of docs/readiness.md, grouped by project (the PATH arguments).
# Exit code 0 once the report is produced; `--strict` exits 1 if any
# candidate module is not translatable (the check.sh self-check over
# elixir/src). `--no-translate` skips step 1 (walker only). `--exclude FILE`
# drops a file from the walk: elixir/src/pubsub.ex is the local transport
# twin of Phoenix.PubSub, a GenServer the model never translates (PubSub is
# an effect of Sys, not an actor). Step 1 runs the translator as a
# subprocess per file, which dominates the runtime, so the files are walked
# in parallel (`--jobs N`, default one per scheduler: the five real projects
# take about 15 seconds instead of 80).
#
# Distance. Each module also gets a *distance*: the number of distinct
# blocker FAMILIES it still hits (`family/1` groups the fine-grained kinds
# into the feature each would need), not the number of blockers. Twelve
# `Logger.info/1` calls in one module are one feature to build; one `Logger`
# call and one `with` are two. `--markdown` reports it per module and adds a
# "Closest to translatable" section -- the ten untranslatable modules that
# are fewest features away -- which is how the next round is planned.
#
# The regression gate. `--json` prints the per-project numbers (files,
# candidate modules, translated, blockers, families, and one line per
# module) as JSON; `--update-baseline FILE` writes them to FILE instead.
# `docs/readiness-baseline.json` is that file, committed, and
# `--check-baseline FILE` re-measures and compares: it exits 1 if any
# project (or the total) translates fewer modules than the baseline records
# or carries more blockers, printing both numbers per project and naming
# every module whose verdict changed. That is a check.sh step. With no PATH
# arguments it measures exactly the paths the baseline was made from (they
# are in the file), and if one of them is not on this machine it says so and
# passes -- the five real projects are not part of the repository.
# A round that lands new translator features is EXPECTED to beat the
# baseline; refresh it then (the gate says so when it is beaten):
#
#   elixir elixir/readiness.exs --json --update-baseline docs/readiness-baseline.json \
#     ~/code/loom/lib ~/code/ensemble/lib ~/code/blinks_backend/lib \
#     ~/code/big_bill/lib ~/code/bobs_broadcast/lib
#   elixir elixir/readiness.exs --markdown <the same paths> > docs/readiness.md
#
# The arguments of an unsupported call are walked too, so one line can carry
# several findings (`Logger.info("x: #{y}")` is a call, a string and an
# interpolation): the counts are of constructs, not of lines to fix.
#
# The walker does not type anything: a construct the translator rejects for
# a type reason only (an atom at a non-enum position, a variable reused at
# another type) is not reported here, and a form reported here may in rare
# cases be accepted (a helper the translator never reaches because it is in
# an ignored def). Kinds are meant to be read by frequency, not as a proof.

defmodule Readiness do
  @root Path.expand("..", __DIR__)
  @translator Path.join(@root, "elixir/to_lean.exs")

  # ---------- the allowlist: what elixir/to_lean.exs accepts ----------
  #
  # One data structure, mirrored on the translator header. Structural forms
  # (patterns, return forms, the receive-loop shape) are matched in code
  # below, but every name the walker consults is here. Extend this when the
  # translator grows.
  @supported %{
    # module shapes: a top-level, single-segment `defmodule` that either
    # `use GenServer` with these callbacks, or is a raw process: exactly one
    # `def loop(state) do receive do .. [after t -> ..] end end`
    callbacks: [handle_cast: 2, handle_info: 2, handle_call: 3, handle_continue: 2, init: 1],
    # callbacks the translator silently ignores (reported as notes)
    ignored_callbacks: [terminate: 2, code_change: 3, format_status: 1, format_status: 2, handle_continue: 1, child_spec: 1],
    # @type declarations the translator reads; any other @type is a local
    # named type (an atom union -> enum, a tagged union -> inductive)
    type_decls: [:msg, :cast, :info, :call, :reply, :state, :continue],
    # type forms: these builtins plus `[T]`, `%{K => V}` (one pair), `T | nil`,
    # a union of atoms, a tagged union `{:tag, T..} | :atom | ..`, a tuple (at
    # state level only) and a local `name()`; EXIT and DOWN alternatives are
    # typed as (Pid, Reason) whatever their declared fields
    builtin_types: [pid: 0, integer: 0, non_neg_integer: 0, boolean: 0, term: 0, any: 0, reference: 0],
    remote_types: [{[:GenServer], :from, 0}],
    # a remote type `Mod.name()` is read when Mod is a module of the same file
    # (a struct `Mod.t()`, an enum `Mod.level()`); a struct type
    # `%__MODULE__{f: T}` / `%Mod{f: T}` is the module's defstruct
    local_remote_types: "Mod.name() for a module of this file",
    # statements before the return form (see `sends` in the translator)
    statements: [
      "send(Name | :name | pid_expr, msg)",
      "GenServer.cast(Name | :name, msg)",
      "GenServer.reply(pid_expr, reply)",
      "Process.send_after(pid_expr, msg, t)",
      "Process.exit(pid_expr, reason)",
      "Process.monitor(pid_expr)  |  _ref = Process.monitor(pid_expr)",
      "{:ok, pid} = GenServer.start_link(Child, arg)  |  GenServer.start(Child, arg)",
      "pid = spawn(Child, :loop, [arg])  |  spawn_link  |  {pid, _ref} = spawn_monitor",
      "v = GenServer.call(Name, msg[, timeout])  (splits the clause; not last; not in a loop with after)",
      "Process.flag(:trap_exit, true)  (init/1 only)"
    ],
    # message payloads and patterns: an atom, a tagged tuple {:tag, ..}, or
    # {:DOWN, ref, :process, pid, reason}; a bare variable pattern is a
    # catch-all; a message *expression* must be an atom or a tagged tuple
    returns: [
      "{:noreply, s}", "{:noreply, s, t | :hibernate | {:continue, x}}",
      "{:reply, r, s}", "{:reply, r, s, t | :hibernate | {:continue, x}}",
      "{:stop, reason, s}", "{:stop, reason, r, s}",
      "exit(reason)", "raise ..", "throw ..",
      "loop(s) | exit(r) | raise | throw | a value   (receive loops)"
    ],
    # expression forms: variables, atoms, integers, booleans, nil, list
    # literals, `[]`, tuples, `self()`, `%{}` and `%{k => v, ..}` literals,
    # these calls and operators, and `if`/`case` at body level only
    map_calls: [get: 2, get: 3, fetch: 2, put: 3, delete: 2, has_key?: 2, keys: 1, values: 1, filter: 2, reject: 2],
    kernel_calls: [self: 0, not: 1, is_map_key: 2, map_size: 1, length: 1, hd: 1, tl: 1],
    operators: [:+, :-, :++, :<=, :>=, :<, :>, :==, :!=, :and, :or],
    # Enum over lists (the List API), with `fn x -> e end` or a capture
    # `&(&1..)` as the predicate
    enum_calls: [filter: 2, reject: 2, map: 2, any?: 2, all?: 2, count: 1, count: 2, member?: 2,
                 reverse: 1, take: 2, drop: 2, at: 2, empty?: 1],
    # an Erlang queue is the list, oldest first
    queue_calls: [new: 0, in: 2, out: 1, to_list: 1, len: 1, is_empty: 1, peek: 1],
    # PubSub effects; which module is PubSub is by name (or --pubsub Mod)
    pubsub_modules: [[:Phoenix, :PubSub], [:PubSub]],
    pubsub_calls: [subscribe: 2, unsubscribe: 2, broadcast: 3, broadcast!: 3],
    # external resources, dropped before translation (not modelled at all)
    resource_forms: [
      "ref = :ets.new(name, opts)   (a fresh opaque Term from a hidden counter)",
      ":ets.f(..) as a statement    (dropped)",
      "try do <only resource calls> rescue .. end  (dropped)"
    ],
    # structs, record-shaped state, untyped mode (see the to_lean.exs header)
    struct_forms: [
      "defstruct f: d, .. with @type t :: %__MODULE__{f: T, ..}",
      "%Mod{f: e} | %{s | f: e} | s.f | %Mod{f: p} pattern",
      "a @type state that is the module's own struct is flattened into the state"
    ],
    record_forms: [
      "@type state :: %{k: T, ..} (atom keys) -> one constructor with named fields",
      "s.f | %{s | f: e} | %{f: p, ..} = s | a literal giving every field"
    ],
    untyped_forms: [
      "no @type msg/cast/info/call -> the unions come from the clause patterns",
      "no @type reply             -> from the literal replies of the file",
      "no @type state             -> from the literal of init/1 (needs an init/1)",
      "term() | any() | reference() -> the opaque Leanactors/Term.lean"
    ],
    # a module attribute bound to a literal is substituted into its later reads
    attr_forms: ["@name literal, read as @name"],
    # `case` scrutinee: a variable, Map.get/2, Map.fetch/2, Map.pop/2, :queue.out/1
    case_scrutinees: ["variable", "Map.get/2", "Map.fetch/2", "Map.pop/2", ":queue.out/1"],
    # patterns (type-directed in the translator; checked by shape here):
    # `_`, variables, nil, [], [h | t], booleans, atoms, integers, {:ok, p}
    # and :error, tuples, {pid, _ref} at a from position, `%{}`, map
    # patterns with literal keys optionally `= m`
    patterns: ["_", "var", "nil", "[]", "[h | t]", "bool", "atom", "integer", "{:ok, p} | :error", "{..}", "%{}", "%{lit => p, ..} [= m]"],
    # exit reasons: :normal, :kill, anything else is error
    reasons: [:normal, :kill, :other]
  }

  @operators @supported.operators
  @kernel_calls @supported.kernel_calls
  @map_calls @supported.map_calls
  @enum_calls @supported.enum_calls
  @queue_calls @supported.queue_calls
  @pubsub_calls @supported.pubsub_calls
  @pubsub_modules @supported.pubsub_modules

  def supported, do: @supported

  # ---------- entry ----------

  @usage """
  usage: elixir elixir/readiness.exs [--markdown | --json] [--strict] [--no-translate]
                                     [--jobs N] [--exclude FILE]... PATH...
         elixir elixir/readiness.exs --json --update-baseline FILE PATH...
         elixir elixir/readiness.exs --check-baseline FILE [PATH...]
  """

  def main(argv) do
    {opts, excluded, paths} = parse_argv(argv, [], [], [])
    md? = flag?(opts, "--markdown")
    json? = flag?(opts, "--json")
    strict? = flag?(opts, "--strict")
    translate? = not flag?(opts, "--no-translate")
    update = opt(opts, "--update-baseline")
    check = opt(opts, "--check-baseline")
    jobs = jobs_opt(opt(opts, "--jobs"))

    # --check-baseline with no PATH argument measures exactly the paths the
    # baseline was made from, so check.sh needs no copy of the project list.
    paths = if paths == [] and check != nil, do: baseline_paths(check), else: paths
    if paths == [], do: die(@usage)

    # A path the baseline names but this machine does not have: the gate is
    # over someone else's checkouts, so say so and pass rather than fail.
    if check != nil and Enum.any?(paths, &(ex_files(&1) == [])) do
      for p <- paths, ex_files(p) == [], do: IO.puts("   readiness gate skipped: no .ex files under #{p}")
      System.halt(0)
    end

    projects =
      for p <- paths do
        files = ex_files(p) -- Enum.flat_map(excluded, &ex_files/1)
        if files == [], do: die("no .ex files under #{p}")
        %{name: project_name(p), root: p, files: files}
      end

    projects = projects |> analyze(translate?, jobs) |> with_verdicts()

    cond do
      check != nil -> System.halt(check_baseline(projects, check))
      update != nil ->
        File.write!(update, json_report(projects, paths))
        IO.puts("wrote #{update} (#{Enum.count(for pr <- projects, f <- pr.files, m <- f.modules, do: m)} candidate modules)")
      json? -> IO.puts(json_report(projects, paths))
      md? -> IO.puts(markdown(projects))
      true -> IO.puts(text(projects))
    end

    mods = for pr <- projects, f <- pr.files, m <- f.modules, do: m
    if strict? and Enum.any?(mods, &(not translatable?(&1))), do: System.halt(1)
  end

  # The files are independent (the translator runs as a subprocess per file),
  # so the walk is one `async_stream` over every file of every project; the
  # results come back in order and are handed back to their projects.
  defp analyze(projects, translate?, jobs) do
    all = for pr <- projects, f <- pr.files, do: f

    results =
      all
      |> Task.async_stream(&analyze_file(&1, translate?), max_concurrency: jobs, timeout: :infinity, ordered: true)
      |> Enum.map(fn {:ok, r} -> r end)

    {out, []} =
      Enum.map_reduce(projects, results, fn pr, rest ->
        {mine, others} = Enum.split(rest, length(pr.files))
        {%{pr | files: mine}, others}
      end)

    out
  end

  defp jobs_opt(nil), do: System.schedulers_online()
  defp jobs_opt(s) do
    case Integer.parse(s) do
      {n, ""} when n > 0 -> n
      _ -> die("--jobs needs a positive integer")
    end
  end

  # --flag, --flag VALUE, --exclude FILE (repeatable), then the paths
  @valued ["--exclude", "--jobs", "--update-baseline", "--check-baseline"]

  defp parse_argv([], opts, excluded, paths), do: {Enum.reverse(opts), Enum.reverse(excluded), Enum.reverse(paths)}
  defp parse_argv(["--exclude", f | rest], opts, excluded, paths), do: parse_argv(rest, opts, [f | excluded], paths)
  defp parse_argv([a], _opts, _excluded, _paths) when a in @valued, do: die("#{a} needs an argument")
  defp parse_argv([a, v | rest], opts, excluded, paths) when a in @valued,
    do: parse_argv(rest, [{a, v} | opts], excluded, paths)
  defp parse_argv([a | rest], opts, excluded, paths) do
    if String.starts_with?(a, "--"),
      do: parse_argv(rest, [a | opts], excluded, paths),
      else: parse_argv(rest, opts, excluded, [a | paths])
  end

  defp flag?(opts, f), do: f in opts
  defp opt(opts, f) do
    Enum.find_value(opts, fn
      {^f, v} -> v
      _ -> nil
    end)
  end

  defp die(msg) do
    IO.puts(:stderr, msg)
    System.halt(2)
  end

  defp ex_files(path) do
    cond do
      File.dir?(path) -> path |> Path.expand() |> Path.join("**/*.ex") |> Path.wildcard() |> Enum.sort()
      File.regular?(path) -> [Path.expand(path)]
      true -> []
    end
  end

  defp project_name(path) do
    p = Path.expand(path)
    if Path.basename(p) in ["lib", "src"], do: Path.basename(Path.dirname(p)), else: Path.basename(p)
  end

  # ---------- per file ----------

  # %{path, modules: [module], skipped: [{name, why}], translator: {:ok | :error | :skipped, text}}
  def analyze_file(path, translate?) do
    src = File.read!(path)

    case Code.string_to_quoted(src, columns: false) do
      {:ok, ast} ->
        mods = modules(ast)
        # registered names anywhere in the file: send/cast/call targets
        registered = for {_, segs, body, _, _} <- mods, n <- registered_in(segs, body), do: n
        # @type reply is one per file: any module's declaration serves a blocking call
        reply? = Enum.any?(mods, fn {_, _, body, _, _} -> Enum.any?(body, &match?({:@, _, [{:type, _, [{:"::", _, [{:reply, _, _}, _]}]}]}, &1)) end)
        # the modules this file declares, by last segment: a struct type or a
        # remote type `Mod.t()` of one of them is read by the translator
        file_mods = for {_, segs, _, _, _} <- mods, do: Atom.to_string(List.last(segs))
        analyzed = for {name, segs, body, nested?, line} <- mods, cand = classify_module(body), cand != nil,
                       do: analyze_module(path, name, segs, body, nested?, cand, registered, reply?, line, file_mods)
        others = for {name, _, body, _, _} <- mods, classify_module(body) == nil, do: {name, behaviour_of(body)}
        translator =
          cond do
            analyzed == [] -> {:skipped, "no candidate module"}
            translate? -> run_translator(path)
            true -> {:skipped, "--no-translate"}
          end
        %{path: path, modules: analyzed, skipped: others, translator: translator}

      {:error, {meta, msg, token}} ->
        line = if is_list(meta), do: Keyword.get(meta, :line, 0), else: meta
        %{path: path, modules: [], skipped: [{Path.basename(path), "parse error at line #{line}: #{inspect(msg)} #{inspect(token)}"}],
          translator: {:skipped, "parse error"}}
    end
  end

  # every defmodule of the file, nested ones included:
  # {dotted name, segments, body statements, nested?}
  defp modules(ast), do: collect_mods(stmts(ast), 0)

  defp collect_mods(nodes, depth) do
    Enum.flat_map(nodes, fn
      {:defmodule, m, [{:__aliases__, _, segs}, [do: body]]} ->
        b = stmts(body)
        [{Enum.map_join(segs, ".", &inspect_seg/1), segs, b, depth > 0, ln(m, 1)} | collect_mods(b, depth + 1)]
      _ -> []
    end)
  end

  defp inspect_seg(s) when is_atom(s), do: Atom.to_string(s)
  defp inspect_seg(s), do: Macro.to_string(s)

  defp stmts({:__block__, _, xs}), do: xs
  defp stmts(x), do: [x]

  # :genserver | :loop | nil
  defp classify_module(body) do
    cond do
      Enum.any?(body, &use_genserver?/1) -> :genserver
      Enum.any?(body, &callback_def?/1) -> :genserver
      has_receive?(body) -> :loop
      true -> nil
    end
  end

  defp use_genserver?({:use, _, [{:__aliases__, _, [:GenServer]} | _]}), do: true
  defp use_genserver?({:@, _, [{:behaviour, _, [{:__aliases__, _, [:GenServer]}]}]}), do: true
  defp use_genserver?(_), do: false

  defp callback_def?({:def, _, [head | _]}) do
    {f, args, _} = head_parts(head)
    {f, length(args || [])} in Keyword.take(@supported.callbacks, [:handle_cast, :handle_info, :handle_call])
  end
  defp callback_def?(_), do: false

  defp has_receive?(body) do
    {_, found} = Macro.prewalk(body, false, fn
      {:receive, _, _} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  defp behaviour_of(body) do
    uses = for {:use, _, [{:__aliases__, _, segs} | _]} <- body, do: Enum.join(segs, ".")
    case uses do
      [] -> "plain module"
      _ -> "use " <> Enum.join(uses, ", ")
    end
  end

  defp head_parts({:when, _, [{f, _, args}, g]}), do: {f, args, g}
  defp head_parts({f, _, args}), do: {f, args, nil}

  # ---------- the translator, wrapped ----------

  @pid_retries 8

  defp run_translator(path, flags \\ [], tries \\ 0) do
    args = [@translator, path, "Readiness.Dry" | flags]
    cmd = Enum.map_join(["elixir" | args], " ", &shell_escape/1) <> " 2>&1 >/dev/null"
    {err, status} = System.cmd("sh", ["-c", cmd])
    first = err |> String.split("\n") |> Enum.find("", &(&1 =~ ~r/^(error:|\*\* \()/)) |> String.trim()
    pid_needed = Regex.run(~r/^error: no registered name for (\S+):/, first)
    # a PubSub under another name is configuration too (`--pubsub My.Bus`)
    bus_needed = Regex.run(~r/unsupported statement (?:[:a-z]+ = )?([A-Z][\w.]*)\.(?:subscribe|unsubscribe|broadcast!?)\(/, first)
    cond do
      status == 0 -> {:ok, "translated" <> if(flags == [], do: "", else: " with " <> Enum.join(flags, " "))}
      pid_needed != nil and tries < @pid_retries ->
        [_, name] = pid_needed
        run_translator(path, flags ++ ["--pid", "#{name}=#{String.downcase(name)}"], tries + 1)
      bus_needed != nil and tries < @pid_retries and "--pubsub" not in flags ->
        [_, m] = bus_needed
        run_translator(path, flags ++ ["--pubsub", m], tries + 1)
      true -> {:error, if(first == "", do: "exit #{status}", else: String.replace_prefix(first, "error: ", ""))}
    end
  end

  defp shell_escape(s), do: "'" <> String.replace(s, "'", "'\\''") <> "'"

  # ---------- per module ----------

  # a finding: %{sev: :blocker | :note, line, kind, detail}
  defp finding(sev, line, kind, detail \\ ""), do: %{sev: sev, line: line, kind: kind, detail: detail}

  defp analyze_module(path, name, segs, body, nested?, kind, registered, reply?, first_line, file_mods) do
    types = for {:@, _, [{:type, _, [{:"::", _, [{tn, _, _}, t]}]}]} <- body, into: %{}, do: {tn, t}
    typeps = for {:@, m, [{tp, _, [{:"::", _, [{tn, _, _}, _]}]}]} <- body, tp in [:typep, :opaque], do: {tn, ln(m, 1)}
    tags = declared_tags(types)
    loop = loop_of(body)
    mod = %{
      name: name, kind: kind, types: types, tags: tags, registered: registered, reply?: reply?,
      loop: loop, after?: loop != nil and elem(loop, 3) != nil,
      defined: defined_funs(body),
      atom_key_map?: atom_key_map?(types),
      file_mods: file_mods,
      # module attributes bound to a literal: substituted into their later reads
      attrs: literal_attrs(body),
      # untyped mode infers the state from init/1, so a module without one
      # and without @type state has nothing to infer from
      init?: Enum.any?(body, fn
        {:def, _, [head | _]} -> match?({:init, [_], _}, head_parts(head))
        _ -> false
      end),
      struct?: Enum.any?(body, &match?({:defstruct, _, _}, &1)),
      continues: for({:def, _, [head | _]} <- body, {f, args, _} = head_parts(head), f == :handle_continue, length(args || []) == 2, do: true) != [],
      trapping?: traps?(body)
    }
    fs =
      [
        if(length(segs) > 1, do: [finding(:note, first_line, "dotted module name (translated under its last segment)", name)], else: []),
        if(nested?, do: [finding(:blocker, first_line, "nested defmodule", name)], else: []),
        for({tn, l} <- typeps, do: finding(:blocker, l, "@typep/@opaque (only @type is read)", "#{tn}")),
        check_types(mod, first_line),
        check_defs(mod, body),
        if(mod.trapping? and not Enum.member?(tags, :EXIT),
          do: [finding(:blocker, first_line, "trap_exit without {:EXIT, pid(), term()} in @type msg/info")], else: [])
      ]
      |> List.flatten()
      |> Enum.sort_by(&{&1.line, &1.kind})

    %{name: name, kind: kind, line: first_line, path: path, findings: fs}
  end

  # {name, arity} of every def/defp of the module, so an unsupported call can
  # say whether it is a helper of this module (inlinable) or something else
  # (a Kernel function, an import, a macro)
  defp defined_funs(body) do
    for {d, _, [head | _]} <- body, d in [:def, :defp], {f, args, _} = head_parts(head), into: MapSet.new() do
      {f, length(args || [])}
    end
  end

  @kernel_funs MapSet.new(Kernel.__info__(:functions) ++ Kernel.__info__(:macros))

  # label for an unsupported zero-module call
  defp call_kind(mod, f, n) do
    cond do
      MapSet.member?(mod.defined, {f, n}) -> "local call #{f}/#{n}"
      MapSet.member?(@kernel_funs, {f, n}) -> "Kernel.#{f}/#{n}"
      true -> "imported/macro call #{f}/#{n}"
    end
  end

  defp ln(meta, default) when is_list(meta), do: Keyword.get(meta, :line, default)
  defp ln(_, default), do: default

  # line of an AST node, or the enclosing one
  defp line_of({_, m, _}, default) when is_list(m), do: ln(m, default)
  defp line_of({a, _}, default), do: line_of(a, default)
  defp line_of([x | _], default), do: line_of(x, default)
  defp line_of(_, default), do: default

  defp traps?(body) do
    {_, found} = Macro.prewalk({:__block__, [], body}, false, fn
      {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  # names registered in a module body: `name: N` of GenServer.start_link/start, Process.register/2
  defp registered_in(segs, body) do
    me = List.last(segs)
    {_, names} = Macro.prewalk({:__block__, [], body}, [], fn
      {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [_, _, opts]} = n, acc when f in [:start_link, :start] and is_list(opts) ->
        case List.keyfind(opts, :name, 0) do
          {:name, x} -> {n, [reg_name(me, x) | acc]}
          nil -> {n, acc}
        end
      {{:., _, [{:__aliases__, _, [:Process]}, :register]}, _, [_, x]} = n, acc -> {n, [reg_name(me, x) | acc]}
      n, acc -> {n, acc}
    end)
    Enum.reject(names, &is_nil/1)
  end

  # `@name literal` is substituted into every later read of @name, so those
  # attributes are values the translator understands
  defp literal_attrs(body) do
    compiler = [:type, :typep, :opaque, :spec, :impl, :doc, :moduledoc, :typedoc, :behaviour,
                :derive, :enforce_keys, :callback, :macrocallback, :optional_callbacks, :dialyzer,
                :external_resource, :on_load, :before_compile, :after_compile, :compile, :deprecated]
    for {:@, _, [{name, _, [v]}]} <- body, is_atom(name), name not in compiler, literal_attr?(v), do: name
  end

  defp literal_attr?(x) when is_atom(x) or is_integer(x) or is_binary(x), do: true
  defp literal_attr?(xs) when is_list(xs), do: Enum.all?(xs, &literal_attr?/1)
  defp literal_attr?({a, b}), do: literal_attr?(a) and literal_attr?(b)
  defp literal_attr?({:{}, _, xs}), do: Enum.all?(xs, &literal_attr?/1)
  defp literal_attr?(_), do: false

  defp reg_name(me, {:__MODULE__, _, _}), do: me
  defp reg_name(_me, {:__aliases__, _, [m]}), do: m
  defp reg_name(_me, a) when is_atom(a) and a not in [nil, true, false], do: a
  defp reg_name(_me, _), do: nil

  # ---------- types ----------

  defp declared_tags(types) do
    for kt <- [:msg, :cast, :info, :call], {:ok, t} <- [Map.fetch(types, kt)], alt <- union(t), tag = tag_of(alt), tag != nil, do: tag
  end

  defp union({:|, _, [a, b]}), do: union(a) ++ union(b)
  defp union(t), do: [t]

  defp tag_of(a) when is_atom(a) and a not in [nil, true, false], do: a
  defp tag_of({a, _}) when is_atom(a) and a not in [nil, true, false], do: a
  defp tag_of({:{}, _, [a | _]}) when is_atom(a) and a not in [nil, true, false], do: a
  defp tag_of(_), do: nil

  # does the module declare a map type `%{K => V}` whose key is an atom, a
  # union of atoms, or a local type that is one? Then an atom-keyed map
  # literal may be an association list rather than a record, which the walker
  # (it types nothing) cannot decide.
  defp atom_key_map?(types), do: Enum.any?(types, fn {_, t} -> map_with_atom_key?(types, t, 0) end)

  defp map_with_atom_key?(_types, _t, d) when d > 6, do: false

  defp map_with_atom_key?(types, t, d) do
    case t do
      {:%{}, _, [{k, v}]} -> atomish_key?(types, k, d + 1) or map_with_atom_key?(types, v, d + 1)
      {:|, _, [a, b]} -> map_with_atom_key?(types, a, d + 1) or map_with_atom_key?(types, b, d + 1)
      [inner] -> map_with_atom_key?(types, inner, d + 1)
      {:{}, _, xs} -> Enum.any?(xs, &map_with_atom_key?(types, &1, d + 1))
      {name, _, args} when is_atom(name) and args in [nil, []] ->
        case Map.fetch(types, name) do
          {:ok, inner} -> map_with_atom_key?(types, inner, d + 1)
          :error -> false
        end
      {a, b} -> map_with_atom_key?(types, a, d + 1) or map_with_atom_key?(types, b, d + 1)
      _ -> false
    end
  end

  defp atomish_key?(_types, _k, d) when d > 6, do: false

  defp atomish_key?(types, k, d) do
    case k do
      a when is_atom(a) and a not in [nil, true, false] -> true
      {:|, _, _} = u -> Enum.all?(union(u), &(is_atom(&1) and &1 not in [nil, true, false]))
      {name, _, args} when is_atom(name) and args in [nil, []] ->
        case Map.fetch(types, name) do
          {:ok, inner} -> atomish_key?(types, inner, d + 1)
          :error -> false
        end
      _ -> false
    end
  end

  defp check_types(mod, first_line) do
    types = mod.types
    msgs = Enum.filter([:msg, :cast, :info, :call], &Map.has_key?(types, &1))
    [
      cond do
        Map.has_key?(types, :state) -> []
        mod.init? -> [finding(:note, first_line, "no @type state (inferred from init/1: untyped mode)")]
        true -> [finding(:blocker, first_line, "no @type state and no init/1 to infer one from")]
      end,
      if(msgs == [], do: [finding(:note, first_line, "no @type msg/cast/info/call (inferred from the clause patterns: untyped mode)")], else: []),
      if(mod.kind == :loop, do: for(kt <- [:cast, :call], Map.has_key?(types, kt), do: finding(:blocker, first_line, "@type #{kt} in a raw process")), else: []),
      for(kt <- msgs, alt <- union(types[kt])) do
        case alt do
          a when is_atom(a) and a not in [nil, true, false] -> []
          _ ->
            case tag_of(alt) do
              nil -> finding(:blocker, first_line, "message alternative is not an atom or tagged tuple", "@type #{kt}: #{str(alt)}")
              tag when tag in [:EXIT, :DOWN] -> []
              _ -> alt |> tuple_args() |> Enum.flat_map(&check_type(mod, &1, first_line, "@type #{kt}"))
            end
        end
      end,
      case Map.fetch(types, :state) do
        # `%{k: T, ..}` with atom keys is a record state: named fields, not a map
        {:ok, {:%{}, _, pairs}} when is_list(pairs) and pairs != [] ->
          if Enum.all?(pairs, fn {k, _} -> is_atom(k) and k not in [nil, true, false] end),
            do: Enum.flat_map(pairs, fn {_, t} -> check_type(mod, t, first_line, "@type state") end),
            else: check_type(mod, {:%{}, [], pairs}, first_line, "@type state")
        {:ok, t} -> t |> state_parts() |> Enum.flat_map(&check_type(mod, &1, first_line, "@type state"))
        :error -> []
      end,
      for({tn, t} <- types, tn not in [:msg, :cast, :info, :call, :state, :continue], do: check_type(mod, t, first_line, "@type #{tn}"))
    ]
  end

  defp tuple_args({_, b}), do: [b]
  defp tuple_args({:{}, _, [_ | rest]}), do: rest

  defp state_parts({:{}, _, ts}), do: ts
  defp state_parts({a, b}), do: [a, b]
  defp state_parts(t), do: [t]

  # a type form -> findings (mirrors lean_type)
  defp check_type(mod, t, line, where) do
    blk = fn kind, detail -> [finding(:blocker, line, kind, "#{where}: #{detail}")] end
    case t do
      {name, _, args} when is_atom(name) and args in [nil, []] ->
        cond do
          {name, 0} in @supported.builtin_types -> []
          Map.has_key?(mod.types, name) -> []
          true -> blk.("unsupported type #{name}()", str(t))
        end
      # `:queue.queue(T)` is `List T`
      {{:., _, [:queue, :queue]}, _, [inner]} -> check_type(mod, inner, line, where)
      {{:., _, [:queue, :queue]}, _, _} -> blk.("queue type without an element type", str(t))
      {{:., _, [{:__aliases__, _, segs}, f]}, _, args} ->
        cond do
          {segs, f, length(args || [])} in @supported.remote_types -> []
          # `Mod.t()` / `Mod.level()`: a type of a module of this file
          Atom.to_string(List.last(segs)) in mod.file_mods and (args || []) == [] -> []
          true -> blk.("unsupported type #{Enum.join(segs, ".")}.#{f}()", str(t))
        end
      a when is_atom(a) and a not in [nil, true, false] -> []
      [inner] -> check_type(mod, inner, line, where)
      [] -> blk.("unsupported type []", str(t))
      {:%{}, _, [{k, v}]} when is_atom(k) and k not in [nil, true, false] ->
        # `%{field: T}` with ONE field is `%{:field => T}`, which the
        # translator accepts as an association list with a one-atom enum key.
        # It is a record in intent, so say so, but it is not a blocker.
        [finding(:note, line, "one-field map type %{field: T} (assoc list with a one-atom key, not a record)", "#{where}: #{str(t)}")] ++
          check_type(mod, v, line, where)
      {:%{}, _, [{k, v}]} -> check_type(mod, k, line, where) ++ check_type(mod, v, line, where)
      {:%{}, _, pairs} when is_list(pairs) ->
        if Enum.all?(pairs, fn {k, _} -> is_atom(k) end) and pairs != [],
          do: blk.("record-shaped map type %{field: T}", str(t)),
          else: blk.("map type with #{length(pairs)} pairs (needs exactly one K => V)", str(t))
      # a struct type `%__MODULE__{f: T, ..}` or `%Mod{..}` of this file
      {:%, _, [m, {:%{}, _, pairs}]} ->
        if struct_module?(mod, m),
          do: Enum.flat_map(pairs, fn {_, ft} -> check_type(mod, ft, line, where) end),
          else: blk.("struct type of a module outside this file", str(t))
      {:%, _, _} -> blk.("struct type", str(t))
      {:|, _, _} = u ->
        alts = union(u)
        cond do
          Enum.all?(alts, &(is_atom(&1) and &1 not in [nil, true, false])) -> []
          tagged_union?(alts) ->
            Enum.flat_map(alts, fn a -> if is_atom(a), do: [], else: a |> tuple_args() |> Enum.flat_map(&check_type(mod, &1, line, where)) end)
          Enum.member?(alts, nil) ->
            case List.delete(alts, nil) do
              [inner] -> check_type(mod, inner, line, where)
              _ -> blk.("unsupported union (only T | nil, atoms, or tagged tuples)", str(t))
            end
          true -> blk.("unsupported union (only T | nil, atoms, or tagged tuples)", str(t))
        end
      {:{}, _, _} -> blk.("tuple type below state level", str(t))
      {_, _} -> blk.("tuple type below state level", str(t))
      other -> blk.("unsupported type", str(other))
    end
  end

  defp tagged_union?(alts) do
    Enum.any?(alts, &tagged_tuple?/1) and
      Enum.all?(alts, fn a -> tagged_tuple?(a) or (is_atom(a) and a not in [nil, true, false]) end)
  end

  # `%__MODULE__{}` or `%Mod{}` where Mod is a module of this file
  defp struct_module?(_mod, {:__MODULE__, _, _}), do: true
  defp struct_module?(mod, {:__aliases__, _, segs}), do: Atom.to_string(List.last(segs)) in mod.file_mods
  defp struct_module?(_mod, _), do: false

  # is this call one of the PubSub effects? {name, args, known module?} or nil.
  # `Phoenix.PubSub` and `PubSub` are PubSub by name; any other module with
  # those function shapes needs `--pubsub Mod`, which is configuration (like
  # --pid), so the walker reports a note rather than a blocker.
  defp pubsub_call({{:., _, [{:__aliases__, _, segs}, f]}, _, args}) when is_list(args) do
    if {f, length(args)} in @pubsub_calls, do: {f, args, segs in @pubsub_modules}, else: nil
  end
  defp pubsub_call({:=, _, [:ok, call]}), do: pubsub_call(call)
  defp pubsub_call(_), do: nil

  # a PubSub topic: a string literal, or a module attribute bound to one
  defp check_topic(mod, t, l) do
    case t do
      s when is_binary(s) -> []
      {:@, _, [{name, _, nil}]} when is_atom(name) ->
        if name in mod.attrs, do: [], else: [finding(:blocker, l, "PubSub topic attribute not bound to a literal", str(t))]
      _ -> [finding(:blocker, l, "PubSub topic is not a string literal or an attribute bound to one", str(t))]
    end
  end

  # the effects of a PubSub call (the server argument is ignored)
  defp check_pubsub(mod, {f, args, known?}, l) do
    flag = if known?, do: [], else: [finding(:note, l, "PubSub module not known by name (needs --pubsub Mod)", pubsub_mod(args))]
    case {f, args} do
      {b, [_server, topic, m]} when b in [:broadcast, :broadcast!] -> [flag, check_topic(mod, topic, l), check_msg_expr(mod, m, l)]
      {_, [_server, topic]} -> [flag, check_topic(mod, topic, l)]
    end
  end

  defp pubsub_mod([{:__aliases__, _, segs} | _]), do: Enum.join(segs, ".")
  defp pubsub_mod(_), do: ""

  # `:ets.f(..)`: dropped before translation (the resource is not modelled)
  defp ets_call?({{:., _, [:ets, _f]}, _, args}) when is_list(args), do: true
  defp ets_call?({:=, _, [_, rhs]}), do: ets_call?(rhs)
  defp ets_call?(_), do: false

  defp tagged_tuple?({a, _}) when is_atom(a) and a not in [nil, true, false], do: true
  defp tagged_tuple?({:{}, _, [a | _]}) when is_atom(a) and a not in [nil, true, false], do: true
  defp tagged_tuple?(_), do: false

  # ---------- defs ----------

  defp check_defs(mod, body) do
    inits = for {:def, m, [head | rest]} <- body, {f, args, _} = head_parts(head), f == :init, length(args || []) == 1, do: {m, head, rest}
    loops = for {:def, m, [head, [do: {:receive, _, _}]]} <- body, do: {m, head}
    handlers = for {:def, _, [head | _]} <- body, {f, args, _} = head_parts(head), {f, length(args || [])} in @supported.callbacks, f != :init, do: f
    mixed = loops != [] and handlers != []
    defs =
      for {d, m, [head | rest]} = node <- body, d in [:def, :defp] do
        {f, args, guard} = head_parts(head)
        arity = length(args || [])
        line = ln(m, 1)
        blocks = case rest do [kw] when is_list(kw) -> kw; _ -> [] end
        extra = Keyword.keys(blocks) -- [:do]
        cond do
          d == :def and {f, arity} in [handle_cast: 2, handle_info: 2, handle_call: 3, handle_continue: 2] ->
            if extra != [],
              do: [finding(:blocker, line, "callback with #{Enum.join(extra, "/")} block", "#{f}/#{arity}")],
              else: check_clause(mod, f, args, guard, blocks[:do], line)
          d == :def and {f, arity} == {:init, 1} -> if length(inits) > 1, do: [finding(:blocker, line, "init/1 with more than one clause")], else: []
          d == :def and {f, arity} in @supported.ignored_callbacks -> [finding(:note, line, "#{f}/#{arity} ignored by the translator")]
          d == :def and match?([do: {:receive, _, _}], blocks) ->
            check_loop_def(mod, f, args, guard, blocks[:do], line, length(loops), mixed)
          {f, arity} in [handle_cast: 2, handle_info: 2, handle_call: 3, handle_continue: 2, init: 1] ->
            [finding(:blocker, line, "callback is defp", "#{f}/#{arity}")]
          has_receive?([node]) ->
            [finding(:blocker, line, "receive not the whole body of a one-argument def", "#{d} #{f}/#{arity}")]
          true -> []
        end
      end
    init_fs = for {m, head, [blocks]} <- Enum.take(inits, 1), is_list(blocks), do: check_init(mod, head, blocks[:do], ln(m, 1))
    [defs, init_fs]
  end

  # init/1: `def init(p), do: {:ok, e}` with optional Process.flag statements
  defp check_init(mod, head, b, line) do
    {:init, [p], _} = head_parts(head)
    param_fs =
      case p do
        {v, _, nil} when is_atom(v) -> []
        {:{}, _, xs} -> if Enum.all?(xs, &match?({v, _, nil} when is_atom(v), &1)), do: [], else: [finding(:blocker, line, "init/1 parameter pattern", str(p))]
        {a, b2} -> if Enum.all?([a, b2], &match?({v, _, nil} when is_atom(v), &1)), do: [], else: [finding(:blocker, line, "init/1 parameter pattern", str(p))]
        _ -> [finding(:blocker, line, "init/1 parameter pattern", str(p))]
      end
    {pre, [last]} = Enum.split(stmts(b), -1)
    pre_fs =
      for s <- pre do
        l = line_of(s, line)
        call = case s do {:=, _, [:ok, c]} -> c; _ -> s end
        case {call, pubsub_call(call)} do
          {{{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]}, _} -> []
          {_, {f, _, _} = pc} when f in [:subscribe, :unsubscribe] -> check_pubsub(mod, pc, l)
          _ -> [finding(:blocker, l, "statement in init/1", str(s))] ++ classify_stmt_kinds(mod, s, l)
        end
      end
    last_fs =
      case last do
        {:ok, e} ->
          selfs = contains?(e, fn {:self, _, []} -> true; _ -> false end)
          if(selfs, do: [finding(:blocker, line_of(e, line), "self() in the initial state")], else: []) ++ check_expr(mod, e, line_of(e, line))
        _ -> [finding(:blocker, line_of(last, line), "init/1 return form (only {:ok, state})", str(last))]
      end
    [param_fs, pre_fs, last_fs]
  end

  # for a rejected init statement, still name what it is (a binding, a call)
  defp classify_stmt_kinds(mod, s, line) do
    case s do
      {:=, _, [_, rhs]} -> check_expr(mod, rhs, line)
      _ -> check_expr(mod, s, line)
    end
  end

  defp contains?(ast, pred) do
    {_, found} = Macro.prewalk(ast, false, fn n, acc -> {n, acc or pred.(n)} end)
    found
  end

  # a GenServer callback clause
  defp check_clause(mod, f, args, guard, body, line) do
    {mpat, from, spat} =
      case {f, args} do
        {:handle_call, [m, fr, s]} -> {m, fr, s}
        {_, [m, s]} -> {m, nil, s}
      end
    ctx = %{mod: mod, kind: f, line: line}
    from_fs =
      case from do
        nil -> []
        {v, _, nil} when is_atom(v) -> []
        {{v, _, nil}, {r, _, nil}} when is_atom(v) and is_atom(r) ->
          if String.starts_with?(Atom.to_string(r), "_"), do: [], else: [finding(:blocker, line, "ref in from-pattern must be a wildcard", str(from))]
        _ -> [finding(:blocker, line, "unsupported from pattern", str(from))]
      end
    guard_fs =
      if f == :handle_continue and guard != nil,
        do: [finding(:blocker, line, "guard on handle_continue")],
        else: check_guard(mod, guard, line)
    mpat_fs = if f == :handle_continue, do: check_pattern(mod, mpat, line), else: check_msg_pattern(mod, mpat, line)
    [mpat_fs, from_fs, check_state_pattern(mod, spat, line), guard_fs, check_body(ctx, body, line)]
  end

  defp check_loop_def(mod, f, args, guard, {:receive, m, [opts]}, line, nloops, mixed) do
    arms = opts[:do] || []
    after_cl = opts[:after]
    shape_fs =
      [
        if(mixed, do: [finding(:blocker, line, "receive loop mixed with GenServer callbacks", "#{f}")], else: []),
        if(nloops > 1, do: [finding(:blocker, line, "more than one receive loop in a module", "#{f}")], else: []),
        if(length(args || []) != 1 or guard != nil, do: [finding(:blocker, line, "receive loop must take one argument and have no guard", "#{f}/#{length(args || [])}")], else: []),
        if(is_list(after_cl) and length(after_cl) > 1, do: [finding(:blocker, ln(m, line), "receive with more than one after clause")], else: [])
      ]
    param = List.first(args || [])
    ctx = %{mod: mod, kind: :loop, loop: f, line: line}
    arm_fs =
      for {:->, am, [lhs, b]} <- arms do
        l = ln(am, line)
        case lhs do
          [{:when, _, [p, g]}] -> [check_msg_pattern(mod, p, l), check_guard(mod, g, l), check_loop_body(ctx, b, l)]
          [p] -> [check_msg_pattern(mod, p, l), check_loop_body(ctx, b, l)]
          _ -> [finding(:blocker, l, "receive arm with several patterns", str(lhs))]
        end
      end
    after_fs =
      case after_cl do
        [{:->, am, [[_t], b]}] -> check_loop_body(ctx, b, ln(am, line))
        _ -> []
      end
    param_fs = if param, do: check_state_pattern(mod, param, line), else: []
    [shape_fs, param_fs, arm_fs, after_fs]
  end

  # ---------- patterns ----------

  defp check_msg_pattern(mod, p, line) do
    case p do
      {v, _, nil} when is_atom(v) -> []
      {:{}, _, [:DOWN, _ref, :process, pid, reason]} -> check_pattern(mod, pid, line) ++ check_pattern(mod, reason, line)
      _ ->
        case tag_of(p) do
          nil -> [finding(:blocker, line, "message pattern is not an atom or tagged tuple", str(p))]
          tag ->
            known = mod.tags == [] or tag in mod.tags
            [
              if(known, do: [], else: [finding(:blocker, line, "message tag not declared in @type msg/cast/info/call", ":#{tag}")]),
              if(is_atom(p), do: [], else: p |> tuple_args() |> Enum.flat_map(&check_pattern(mod, &1, line)))
            ]
        end
    end
  end

  defp check_state_pattern(mod, p, line), do: check_pattern(mod, p, line)

  # a sub-pattern (of a message, a state, a case arm)
  defp check_pattern(mod, p, line) do
    l = line_of(p, line)
    case p do
      {:_, _, nil} -> []
      {:__MODULE__, _, nil} -> [finding(:blocker, l, "__MODULE__ in a pattern")]
      {v, _, nil} when is_atom(v) -> []
      nil -> []
      [] -> []
      b when is_boolean(b) -> []
      a when is_atom(a) -> []
      n when is_integer(n) -> []
      f when is_float(f) -> [finding(:blocker, l, "float literal in a pattern", str(p))]
      s when is_binary(s) -> [finding(:blocker, l, "string pattern", str(p))]
      [{:|, _, [h, t]}] -> check_pattern(mod, h, l) ++ check_pattern(mod, t, l)
      xs when is_list(xs) -> [finding(:blocker, l, "fixed-length list pattern", str(p))]
      {:^, _, _} -> [finding(:blocker, l, "pin ^x in a pattern", str(p))]
      {:<<>>, _, _} -> [finding(:blocker, l, "binary pattern", str(p))]
      # `%Mod{f: p}` is the anonymous constructor, a wildcard for every other field
      {:%, _, [m, {:%{}, _, pairs}]} ->
        if struct_module?(mod, m),
          do: Enum.flat_map(pairs, fn {_, vp} -> check_pattern(mod, vp, l) end),
          else: [finding(:blocker, l, "struct pattern of a module outside this file", str(p))]
      {:%, _, _} -> [finding(:blocker, l, "struct pattern %Mod{}", str(p))]
      {:=, _, [{:%{}, _, _} = mp, {v, _, nil}]} when is_atom(v) -> check_pattern(mod, mp, l)
      {:=, _, [{:%, _, _} = sp, {v, _, nil}]} when is_atom(v) -> check_pattern(mod, sp, l)
      {:=, _, _} -> [finding(:blocker, l, "pattern alias = on a non-map, non-struct", str(p))]
      {:%{}, _, pairs} ->
        for {k, vp} <- pairs do
          kf = if is_atom(k) or is_integer(k), do: [], else: [finding(:blocker, l, "map pattern with a non-literal key", str(k))]
          kf ++ check_pattern(mod, vp, l)
        end
      {:{}, _, xs} -> Enum.flat_map(xs, &check_pattern(mod, &1, l))
      {a, b} -> check_pattern(mod, a, l) ++ check_pattern(mod, b, l)
      other -> [finding(:blocker, l, "unsupported pattern", str(other))]
    end
  end

  # ---------- guards ----------

  defp check_guard(_mod, nil, _line), do: []
  defp check_guard(mod, g, line), do: check_expr(mod, g, line_of(g, line))

  # ---------- bodies ----------

  # a callback body: an if/case over whole bodies, or a block of statements
  # ending in a return form
  defp check_body(ctx, b, line) do
    l = line_of(b, line)
    case b do
      {:if, _, [c, [do: a, else: e]]} -> [check_expr(ctx.mod, c, l), check_body(ctx, a, l), check_body(ctx, e, l)]
      {:if, _, [c, [do: a]]} -> [finding(:blocker, l, "if without else", str(c)), check_expr(ctx.mod, c, l), check_body(ctx, a, l)]
      {:unless, _, [c, blocks]} -> [finding(:blocker, l, "unless", str(c)), check_expr(ctx.mod, c, l), for({_, bb} <- blocks, do: check_body(ctx, bb, l))]
      {:case, _, [scrut, [do: arms]]} ->
        sfs =
          case scrut do
            {v, _, nil} when is_atom(v) -> []
            {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, [_, _]} when f in [:get, :fetch] -> check_expr(ctx.mod, scrut, l)
            # `case Map.pop(m, k)` is a match on `get? m k`, `case :queue.out(q)` on the list
            {{:., _, [{:__aliases__, _, [:Map]}, :pop]}, _, [m, k]} -> check_expr(ctx.mod, m, l) ++ check_expr(ctx.mod, k, l)
            {{:., _, [:queue, :out]}, _, [q]} -> check_expr(ctx.mod, q, l)
            # any other scrutinee is an expression whose type the translator
            # must be able to guess: a type reason, which the walker does not check
            _ -> check_expr(ctx.mod, scrut, l)
          end
        [sfs, for({:->, am, [lhs, ab]} <- arms, do: check_arm(ctx, lhs, ab, ln(am, l)))]
      {:cond, _, [[do: arms]]} ->
        [finding(:blocker, l, "cond"), for({:->, am, [[c], ab]} <- arms, do: [check_expr(ctx.mod, c, ln(am, l)), check_body(ctx, ab, ln(am, l))])]
      {:with, _, args} ->
        {clauses, blocks} = Enum.split_with(args, &(not Keyword.keyword?(&1) or &1 == []))
        [finding(:blocker, l, "with"), for({:<-, _, [p, e]} <- clauses, do: [check_pattern(ctx.mod, p, l), check_expr(ctx.mod, e, l)]),
         for({_, bb} <- List.flatten(blocks), do: check_body(ctx, bb, l))]
      {:try, _, [blocks]} ->
        kinds = Keyword.keys(blocks) -- [:do]
        # `try do <only resource calls> rescue .. end` is dropped before translation
        if resource_try?(b),
          do: [],
          else: [finding(:blocker, l, "try/" <> Enum.join(kinds, "/")), check_body(ctx, blocks[:do], l)]
      {:receive, _, _} when ctx.kind != :loop -> [finding(:blocker, l, "receive inside a callback")]
      _ -> check_stmts(ctx, stmts(b), l)
    end
  end

  defp check_arm(ctx, lhs, body, l) do
    case lhs do
      [{:when, _, [p, g]}] -> [check_pattern(ctx.mod, p, l), check_guard(ctx.mod, g, l), check_body(ctx, body, l)]
      [p] -> [check_pattern(ctx.mod, p, l), check_body(ctx, body, l)]
      _ -> [finding(:blocker, l, "case arm with several patterns", str(lhs))]
    end
  end

  defp check_stmts(ctx, stmts, line) do
    {pre, [last]} = Enum.split(stmts, -1)
    case Enum.split_while(stmts, fn s -> not blocking_call?(s) end) do
      {before, [call | rest]} when rest != [] ->
        [for(s <- before, do: check_stmt(ctx, s, line_of(s, line))), check_blocking(ctx, call, line_of(call, line)),
         check_body(ctx, {:__block__, [], rest}, line_of(rest, line))]
      {_, [call]} ->
        [for(s <- pre, do: check_stmt(ctx, s, line_of(s, line))),
         finding(:blocker, line_of(call, line), "blocking call as the last statement (needs a continuation)", str(call)),
         check_blocking(ctx, call, line_of(call, line))]
      _ ->
        [for(s <- pre, do: check_stmt(ctx, s, line_of(s, line))),
         check_last(ctx, last, line_of(last, line), Enum.any?(pre, &effectful?/1))]
    end
  end

  defp blocking_call?({:=, _, [_lhs, {{:., _, [{:__aliases__, _, [:GenServer]}, :call]}, _, [_, _ | _]}]}), do: true
  defp blocking_call?(_), do: false

  defp check_blocking(ctx, {:=, _, [lhs, {_, _, [target, m | _]}]}, l) do
    [
      if(ctx.kind == :loop and ctx.mod.after?, do: [finding(:blocker, l, "blocking call inside a receive loop with after")], else: []),
      if(ctx.mod.reply?, do: [], else: [finding(:note, l, "no @type reply in the file (inferred from the literal replies: untyped mode)")]),
      check_target(ctx.mod, target, l, "GenServer.call"),
      check_msg_expr(ctx.mod, m, l),
      case lhs do
        {v, _, nil} when is_atom(v) -> []
        p -> check_pattern(ctx.mod, p, l)
      end
    ]
  end

  # a send/cast/call target: a registered alias or atom, or (send only) a pid expression
  defp check_target(mod, target, l, what) do
    case target do
      {:__aliases__, _, [name]} -> registered?(mod, name, l, what)
      {:__aliases__, _, segs} -> [finding(:blocker, l, "dotted module name as a #{what} target", Enum.join(segs, "."))]
      {:__MODULE__, _, _} -> [finding(:blocker, l, "__MODULE__ as a #{what} target")]
      a when is_atom(a) and a not in [nil, true, false] -> registered?(mod, a, l, what)
      _ when what == "send" -> check_expr(mod, target, l)
      _ -> [finding(:blocker, l, "#{what} to a non-constant target", str(target)), check_expr(mod, target, l)]
    end
  end

  defp registered?(mod, name, l, what) do
    if name in mod.registered,
      do: [],
      else: [finding(:note, l, "#{what} target not registered in this file (needs --pid)", "#{name}")]
  end

  # a message expression: an atom or a tagged tuple whose fields are expressions
  defp check_msg_expr(mod, m, l) do
    case m do
      {:{}, _, [:DOWN, _ref, :process, pid, reason]} -> check_expr(mod, pid, l) ++ check_expr(mod, reason, l)
      _ ->
        case tag_of(m) do
          nil -> [finding(:blocker, l, "message expression is not an atom or tagged tuple", str(m)), check_expr(mod, m, l)]
          _ -> if is_atom(m), do: [], else: m |> tuple_args() |> Enum.flat_map(&check_expr(mod, &1, l))
        end
    end
  end

  # a statement before the return form
  defp check_stmt(ctx, s, l) do
    mod = ctx.mod
    case s do
      {:send, _, [target, m]} -> [check_target(mod, target, l, "send"), check_msg_expr(mod, m, l)]
      {{:., _, [{:__aliases__, _, [:Process]}, :send_after]}, _, [to, m, _t]} -> [check_expr(mod, to, l), check_msg_expr(mod, m, l)]
      {{:., _, [{:__aliases__, _, [:Process]}, :exit]}, _, [to, _r]} -> check_expr(mod, to, l)
      {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [target, m]} -> [check_target(mod, target, l, "GenServer.cast"), check_msg_expr(mod, m, l)]
      {{:., _, [{:__aliases__, _, [:GenServer]}, :reply]}, _, [to, r]} ->
        [if(mod.reply?, do: [], else: [finding(:note, l, "no @type reply in the file (inferred from the literal replies: untyped mode)")]), check_expr(mod, to, l), check_expr(mod, r, l)]
      {{:., _, [{:__aliases__, _, [:GenServer]}, :call]}, _, _} ->
        [finding(:blocker, l, "GenServer.call result unused (needs v = GenServer.call(..))", str(s))]
      {:=, _, [{:ok, {v, _, nil}}, {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [child, arg]}]} when is_atom(v) and f in [:start_link, :start] ->
        [check_child(mod, child, l), check_expr(mod, arg, l)]
      {:=, _, [_, {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [_, _, _]}]} when f in [:start_link, :start] ->
        [finding(:blocker, l, "GenServer.#{f} with options in a body", str(s))]
      {:=, _, [lhs, {f, _, [child, _fname, [arg]]}]} when f in [:spawn, :spawn_link, :spawn_monitor] ->
        lhs_ok =
          case {f, lhs} do
            {:spawn_monitor, {{v, _, nil}, {r, _, nil}}} when is_atom(v) and is_atom(r) -> true
            {_, {v, _, nil}} when f != :spawn_monitor and is_atom(v) -> true
            _ -> false
          end
        [if(lhs_ok, do: [], else: [finding(:blocker, l, "unsupported spawn binding", str(lhs))]), check_child(mod, child, l), check_expr(mod, arg, l)]
      {f, _, [{:fn, _, _} | _]} when f in [:spawn, :spawn_link, :spawn_monitor] -> [finding(:blocker, l, "#{f} with an anonymous fn", str(s))]
      {:=, _, [_, {f, _, [{:fn, _, _} | _]}]} when f in [:spawn, :spawn_link, :spawn_monitor] -> [finding(:blocker, l, "#{f} with an anonymous fn", str(s))]
      {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [t]} -> check_expr(mod, t, l)
      {:=, _, [{_, _, nil}, {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [t]}]} -> check_expr(mod, t, l)
      {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} -> [finding(:blocker, l, "Process.flag(:trap_exit) outside init/1")]
      {f, _, args} when f in [:raise, :throw] and is_list(args) -> [finding(:blocker, l, "#{f} not in tail position", str(s))]
      # `:ok = Phoenix.PubSub.subscribe(..)` is the bare call
      {:=, _, [:ok, call]} ->
        cond do
          pubsub_call(call) != nil -> check_pubsub(mod, pubsub_call(call), l)
          ets_call?(call) -> []
          true -> [finding(:blocker, l, "binding a pattern x = e", str(s)), check_expr(mod, call, l)]
        end
      # `ref = :ets.new(..)` is a fresh opaque reference; any other `:ets.f(..)`
      # statement, alone or bound, is dropped before translation
      {:=, _, [{v, _, nil}, {{:., _, [:ets, :new]}, _, args}]} when is_atom(v) and is_list(args) -> []
      # a local binding `v = e` is a `let` around the clause result
      {:=, _, [{v, _, nil}, rhs]} when is_atom(v) -> check_expr(mod, rhs, l)
      # `{_, q} = :queue.out(q0)` drops the oldest element
      {:=, _, [{{:_, _, nil}, {v, _, nil}}, {{:., _, [:queue, :out]}, _, [q]}]} when is_atom(v) -> check_expr(mod, q, l)
      {:=, _, [lhs, rhs]} -> [finding(:blocker, l, "binding a pattern x = e", str(s)), check_pattern(mod, lhs, l), check_expr(mod, rhs, l)]
      {:|>, _, _} -> [finding(:blocker, l, "pipe |>", str(s)), pipe_stages(s) |> Enum.flat_map(&check_expr(mod, &1, l))]
      _ ->
        cond do
          # `Phoenix.PubSub.subscribe/unsubscribe/broadcast`, optionally `:ok = ..`
          pubsub_call(s) != nil -> check_pubsub(mod, pubsub_call(s), l)
          # an external resource call, or a try/rescue around only those:
          # dropped before translation, the resource is not modelled
          ets_call?(s) -> []
          resource_try?(s) -> []
          true ->
            case List.flatten(check_expr(mod, s, l)) do
              [] -> [finding(:blocker, l, "unsupported statement", str(s))]
              fs -> fs
            end
        end
    end
  end

  # a statement with an effect of its own: anything but a pure local binding
  # (a `let`) or a resource call the translator drops
  defp effectful?(s) do
    case s do
      {:=, _, [{v, _, nil}, rhs]} when is_atom(v) -> ets_call?(rhs) == false and spawn_rhs?(rhs)
      {:=, _, [{{:_, _, nil}, {v, _, nil}}, {{:., _, [:queue, :out]}, _, [_]}]} when is_atom(v) -> false
      _ -> not ets_call?(s) and not resource_try?(s)
    end
  end

  # a binding whose right-hand side is itself an effect (a spawn, a call)
  defp spawn_rhs?({f, _, _}) when f in [:spawn, :spawn_link, :spawn_monitor], do: true
  defp spawn_rhs?({{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, _}) when f in [:start, :start_link, :call], do: true
  defp spawn_rhs?({{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, _}), do: true
  defp spawn_rhs?(_), do: false

  # `try do <only resource calls> rescue .. end`, dropped before translation
  defp resource_try?({:try, _, [blocks]}) when is_list(blocks) do
    (Keyword.keys(blocks) -- [:do]) == [:rescue] and Enum.all?(stmts(blocks[:do]), &ets_call?/1)
  end
  defp resource_try?(_), do: false

  defp check_child(mod, child, l) do
    case child do
      {:__aliases__, _, [_name]} -> []
      {:__aliases__, _, segs} -> [finding(:blocker, l, "dotted module name as a child", Enum.join(segs, "."))]
      {:__MODULE__, _, _} -> [finding(:blocker, l, "__MODULE__ as a child")]
      _ -> [finding(:blocker, l, "child module is not an alias", str(child)), check_expr(mod, child, l)]
    end
  end

  defp pipe_stages({:|>, _, [a, b]}), do: pipe_stages(a) ++ [b]
  defp pipe_stages(e), do: [e]

  # the return form of a callback body
  # an if/case/cond/... is only accepted as the whole body, not after statements
  defp check_last(ctx, last, l, effects_before?) do
    control? = match?({f, _, _} when f in [:if, :case, :cond, :with, :try, :unless, :receive], last)
    [
      if(effects_before? and control?,
        do: [finding(:blocker, l, "if/case after a statement with an effect (it would have to be pushed into every branch)", str(last))],
        else: []),
      if(ctx.kind == :loop, do: check_loop_last(ctx, last, l), else: check_callback_last(ctx, last, l))
    ]
  end

  defp check_callback_last(ctx, last, l) do
    mod = ctx.mod
    reply_ok = fn -> if ctx.kind in [:handle_call, :handle_continue], do: [], else: [finding(:blocker, l, "{:reply, ..} outside handle_call")] end
    timeout = fn t ->
      cond do
        t == :hibernate -> []
        match?({:continue, _}, t) -> if mod.continues, do: check_expr(mod, elem(t, 1), l), else: [finding(:blocker, l, "{:continue, x} with no handle_continue clause", str(t))]
        :timeout in mod.tags or mod.tags == [] -> check_expr(mod, t, l)
        true -> [finding(:blocker, l, "GenServer timeout used but :timeout not in @type msg"), check_expr(mod, t, l)]
      end
    end
    case last do
      {:noreply, e} -> check_expr(mod, e, l)
      {:{}, _, [:noreply, e, t]} -> [check_expr(mod, e, l), timeout.(t)]
      {:{}, _, [:reply, r, e]} -> [reply_ok.(), check_expr(mod, r, l), check_expr(mod, e, l)]
      {:{}, _, [:reply, r, e, t]} -> [reply_ok.(), check_expr(mod, r, l), check_expr(mod, e, l), timeout.(t)]
      {:{}, _, [:stop, _r, e]} -> check_expr(mod, e, l)
      {:{}, _, [:stop, _r, r, e]} -> [reply_ok.(), check_expr(mod, r, l), check_expr(mod, e, l)]
      {:exit, _, [_r]} -> []
      {f, _, args} when f in [:raise, :throw] and is_list(args) -> []
      {:if, _, _} -> check_body(ctx, last, l)
      {:case, _, _} -> check_body(ctx, last, l)
      {:cond, _, _} -> check_body(ctx, last, l)
      {:with, _, _} -> check_body(ctx, last, l)
      {:try, _, _} -> check_body(ctx, last, l)
      {:unless, _, _} -> check_body(ctx, last, l)
      {:receive, _, _} -> check_body(ctx, last, l)
      _ -> [finding(:blocker, l, "last statement is not a GenServer return form", str(last)), check_expr(mod, last, l)]
    end
  end

  # the tail of a receive-arm body: loop(e), exit, raise/throw, a value, or
  # a statement (the loop then returns)
  defp check_loop_body(ctx, b, line) do
    l = line_of(b, line)
    case b do
      {:if, _, _} -> check_body(ctx, b, l)
      {:case, _, _} -> check_body(ctx, b, l)
      _ -> check_stmts(ctx, stmts(b), l)
    end
  end

  defp check_loop_last(ctx, last, l) do
    mod = ctx.mod
    case last do
      {f, _, [e]} when f == ctx.loop -> check_expr(mod, e, l)
      {f, _, args} when f == ctx.loop -> [finding(:blocker, l, "loop re-entered with #{length(args || [])} arguments", str(last))]
      {:exit, _, [_r]} -> []
      {f, _, args} when f in [:raise, :throw] and is_list(args) -> []
      {:if, _, _} -> check_body(ctx, last, l)
      {:case, _, _} -> check_body(ctx, last, l)
      {:cond, _, _} -> check_body(ctx, last, l)
      {:with, _, _} -> check_body(ctx, last, l)
      {:try, _, _} -> check_body(ctx, last, l)
      {:receive, _, _} -> [finding(:blocker, l, "nested receive in a receive loop")]
      _ -> if value?(last), do: [], else: check_stmt(ctx, last, l)
    end
  end

  defp value?(x) when is_atom(x) or is_integer(x) or is_list(x), do: true
  defp value?({v, _, nil}) when is_atom(v), do: true
  defp value?({:{}, _, _}), do: true
  defp value?({_, _}), do: true
  defp value?(_), do: false

  # ---------- expressions ----------

  defp check_expr(mod, e, line) do
    l = line_of(e, line)
    blk = fn kind -> [finding(:blocker, l, kind, str(e))] end
    case e do
      nil -> []
      b when is_boolean(b) -> []
      a when is_atom(a) -> []
      n when is_integer(n) -> []
      f when is_float(f) -> blk.("float literal")
      s when is_binary(s) -> blk.("string literal")
      [] -> []
      xs when is_list(xs) ->
        if Keyword.keyword?(xs) and xs != [], do: blk.("keyword list literal"), else: Enum.flat_map(xs, &check_expr(mod, &1, l))
      {:__MODULE__, _, nil} -> blk.("__MODULE__ as a value")
      {:__aliases__, _, _} -> blk.("module alias as a value")
      # `@name` where the module binds it to a literal is substituted
      {:@, _, [{name, _, _}]} ->
        if name in mod.attrs,
          do: [],
          else: [finding(:blocker, l, "module attribute @#{name} as a value", str(e))]
      {:^, _, _} -> blk.("pin ^x")
      # a capture is the argument of an Enum predicate and may only use &1
      {:&, _, [b]} ->
        if capture_arity(b) > 1,
          do: [finding(:blocker, l, "capture with more than one argument (&1 only)", str(e))],
          else: check_expr(mod, capture_body(b), l)
      {:&, _, _} -> blk.("capture & (not &(..))")
      # `fn x -> e end` is an Enum predicate: exactly one clause, one variable
      {:fn, _, [{:->, _, [[{v, _, nil}], b]}]} when is_atom(v) -> check_expr(mod, b, l)
      {:fn, _, clauses} -> [blk.("anonymous fn (only `fn x -> e end`)"), for({:->, _, [_ps, b]} <- clauses, do: check_expr(mod, b, l))]
      {:<<>>, _, _} -> blk.("string interpolation / binary")
      {:sigil_s, _, _} -> blk.("string literal")
      {v, _, nil} when is_atom(v) -> []
      {:self, _, []} -> []
      # `%{s | f: e}` rebuilds a record state or a struct value
      {:%{}, _, [{:|, _, [m, updates]}]} -> [check_expr(mod, m, l), for({_, v} <- updates, do: check_expr(mod, v, l))]
      {:%{}, _, pairs} ->
        cond do
          pairs == [] -> []
          Enum.all?(pairs, fn {k, _} -> is_atom(k) and k not in [nil, true, false] end) ->
            # `%{x: 0, y: 0}` and a record literal have the same AST. When the
            # module declares a map type with an atom-ish key the literal may
            # well be an association list, and the walker does not type, so it
            # is only a note there; with no such type it is a record.
            # a record state literal, an inferred record state, or (when the
            # module declares a map type with an atom-ish key) an assoc list
            [finding(:note, l, "atom-keyed map literal %{field: ..} (a record state, or an assoc list)", str(e)),
             for({_, v} <- pairs, do: check_expr(mod, v, l))]
          true -> for {k, v} <- pairs, do: [check_expr(mod, k, l), check_expr(mod, v, l)]
        end
      {:%, _, [_, {:%{}, _, [{:|, _, _}]}]} -> blk.("struct update %Mod{s | ..} (use %{s | f: e})")
      # `%Mod{f: e}` of a module of this file, other fields at their defaults
      {:%, _, [m, {:%{}, _, pairs}]} ->
        if struct_module?(mod, m),
          do: Enum.flat_map(pairs, fn {_, v} -> check_expr(mod, v, l) end),
          else: [finding(:blocker, l, "struct literal of a module outside this file", str(e))]
      {:%, _, _} -> blk.("struct literal %Mod{}")
      {{:., _, [{:__aliases__, _, [:Access]}, :get]}, _, [m, k]} -> [blk.("access m[k]"), check_expr(mod, m, l), check_expr(mod, k, l)]
      {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, args} ->
        n = length(args)
        cond do
          {f, n} not in @map_calls -> blk.("Map.#{f}/#{n}")
          f in [:filter, :reject] ->
            case args do
              [m, {:fn, _, [{:->, _, [[{{k, _, nil}, {v, _, nil}}], b]}]}] when is_atom(k) and is_atom(v) -> [check_expr(mod, m, l), check_expr(mod, b, l)]
              [m, _] -> [finding(:blocker, l, "Map.#{f} with a non-literal fn {k, v} -> e end", str(e)), check_expr(mod, m, l)]
            end
          true -> Enum.flat_map(args, &check_expr(mod, &1, l))
        end
      # Enum over lists: the List API
      {{:., _, [{:__aliases__, _, [:Enum]}, f]}, _, args} when is_list(args) ->
        if {f, length(args)} in @enum_calls,
          do: Enum.flat_map(args, &check_expr(mod, &1, l)),
          else: [finding(:blocker, l, "Enum.#{f}/#{length(args)}", str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
      # PubSub effects (the server argument is ignored)
      {{:., _, [{:__aliases__, _, segs}, f]}, _, args} when is_list(args) ->
        cond do
          pubsub_call(e) != nil -> check_pubsub(mod, pubsub_call(e), l)
          segs in @pubsub_modules ->
            [finding(:blocker, l, "#{Enum.join(segs, ".")}.#{f}/#{length(args)} (subscribe/2, unsubscribe/2, broadcast/3)", str(e))]
          true -> [finding(:blocker, l, "#{Enum.join(segs, ".")}.#{f}/#{length(args)}", str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
        end
      # `:queue` is the list, oldest first
      {{:., _, [:queue, f]}, _, args} when is_list(args) ->
        if {f, length(args)} in @queue_calls,
          do: Enum.flat_map(args, &check_expr(mod, &1, l)),
          else: [finding(:blocker, l, ":queue.#{f}/#{length(args)}", str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
      {{:., _, [m, f]}, _, args} when is_atom(m) and is_list(args) ->
        [finding(:blocker, l, "#{inspect(m)}.#{f}/#{length(args)}", str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
      {{:., _, [{:__MODULE__, _, _}, f]}, _, args} when is_list(args) ->
        [finding(:blocker, l, "__MODULE__.#{f}/#{length(args)}", str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
      # `s.f`: a field of a record state, a flattened struct state, or a struct
      {{:., _, [m, f]}, meta, []} when is_atom(f) ->
        if Keyword.get(meta, :no_parens, false) or match?({_, _, nil}, m),
          do: [],
          else: [finding(:blocker, l, "call on an expression", str(e))]
      {{:., _, _}, _, _} -> blk.("call on an expression")
      {op, _, [a, b]} when op in @operators -> check_expr(mod, a, l) ++ check_expr(mod, b, l)
      {:|>, _, _} -> [blk.("pipe |>"), pipe_stages(e) |> Enum.flat_map(&check_expr(mod, &1, l))]
      # `[h | t]` as an expression: the list branch above hands us the cons
      {:|, _, [h, t]} -> [blk.("list cons [h | t] in an expression"), check_expr(mod, h, l), check_expr(mod, t, l)]
      {op, _, [a, b]} when op in [:*, :/, :<>, :&&, :||, :in, :"..", :===, :!==, :=~, :"//", :"<-", :"::"] ->
        [blk.("operator #{op}"), check_expr(mod, a, l), check_expr(mod, b, l)]
      {op, _, [a]} when op in [:!, :-, :+] -> [blk.("operator #{op}"), check_expr(mod, a, l)]
      {:not, _, [a]} -> check_expr(mod, a, l)
      {:is_map_key, _, [m, k]} -> check_expr(mod, m, l) ++ check_expr(mod, k, l)
      {:map_size, _, [m]} -> check_expr(mod, m, l)
      {:__block__, _, xs} -> [blk.("block as a sub-expression"), Enum.flat_map(xs, &check_expr(mod, &1, l))]
      {:=, _, [_, rhs]} -> [blk.("variable binding x = e"), check_expr(mod, rhs, l)]
      {:if, _, [c, blocks]} -> [blk.("if/case not at body level"), check_expr(mod, c, l), for({_, b} <- blocks, do: check_expr(mod, b, l))]
      {:unless, _, [c, blocks]} -> [blk.("unless"), check_expr(mod, c, l), for({_, b} <- blocks, do: check_expr(mod, b, l))]
      {:case, _, [s, [do: arms]]} -> [blk.("if/case not at body level"), check_expr(mod, s, l), for({:->, _, [_, b]} <- arms, do: check_expr(mod, b, l))]
      {:cond, _, [[do: arms]]} -> [blk.("cond"), for({:->, _, [[c], b]} <- arms, do: [check_expr(mod, c, l), check_expr(mod, b, l)])]
      {:with, _, _} -> blk.("with")
      # `for x <- l, c, .., do: e` is List.map over the filtered list
      {:for, _, args} when is_list(args) and args != [] ->
        {clauses, blocks} = Enum.split_with(args, &(not Keyword.keyword?(&1)))
        gens = for {:<-, _, [p, src]} <- clauses, do: {p, src}
        filters = clauses -- (for {:<-, _, _} = g <- clauses, do: g)
        body = blocks |> List.flatten() |> Keyword.get(:do)
        extra = (blocks |> List.flatten() |> Keyword.keys()) -- [:do]
        cond do
          length(gens) != 1 or extra != [] ->
            [finding(:blocker, l, "for comprehension (only one generator and a do body)", str(e))]
          true ->
            [{pat, src}] = gens
            [check_pattern(mod, pat, l), check_expr(mod, src, l),
             Enum.flat_map(filters, &check_expr(mod, &1, l)), check_expr(mod, body, l)]
        end
      {:for, _, _} -> blk.("for comprehension")
      {:try, _, [blocks]} -> blk.("try/" <> Enum.join(Keyword.keys(blocks) -- [:do], "/"))
      {:receive, _, _} -> blk.("receive inside a callback")
      {:raise, _, _} -> blk.("raise not in tail position")
      {:throw, _, _} -> blk.("throw not in tail position")
      {:exit, _, _} -> blk.("exit not in tail position")
      {:send, _, [_, _]} -> blk.("send as a sub-expression")
      {:{}, _, xs} -> Enum.flat_map(xs, &check_expr(mod, &1, l))
      {a, b} -> check_expr(mod, a, l) ++ check_expr(mod, b, l)
      {f, _, args} when is_atom(f) and is_list(args) ->
        n = length(args)
        cond do
          {f, n} in @kernel_calls -> Enum.flat_map(args, &check_expr(mod, &1, l))
          String.starts_with?(Atom.to_string(f), "sigil_") -> blk.("sigil")
          true -> [finding(:blocker, l, call_kind(mod, f, n), str(e)) | Enum.flat_map(args, &check_expr(mod, &1, l))]
        end
      other -> [finding(:blocker, l, "unsupported expression", str(other))]
    end
  end

  # the highest `&n` of a capture body, and `&(..)`'s body with `&1` as a variable
  defp capture_arity(b) do
    {_, n} = Macro.prewalk(b, 0, fn
      {:&, _, [i]} = node, acc when is_integer(i) -> {node, max(acc, i)}
      node, acc -> {node, acc}
    end)
    n
  end

  defp capture_body(b) do
    Macro.prewalk(b, fn
      {:&, _, [i]} when is_integer(i) -> {:"x#{i}", [], nil}
      node -> node
    end)
  end

  # ---------- loops ----------

  defp loop_of(body) do
    loops = for {:def, _, [head, [do: {:receive, _, [opts]}]]} <- body, do: {head_parts(head), opts}
    case loops do
      [{{fname, [param], nil}, opts}] -> {fname, param, opts[:do], opts[:after]}
      _ -> nil
    end
  end

  # ---------- distance ----------

  # How far a module is from translatable: the number of distinct blocker
  # *families* it still hits (see `family/1`), not the number of blockers.
  # Twelve `Logger.info/1` calls are one feature to build; one `Logger` call
  # and one `with` are two. Distance 0 means the walker found nothing (the
  # module is translatable, or the translator failed for a reason the walker
  # cannot see); distance 1 means one feature away.
  def distance(m), do: length(families(m))

  def families(m), do: m |> blockers() |> Enum.map(&family(&1.kind)) |> Enum.uniq() |> Enum.sort()

  # The modules with the fewest families first, already-translatable ones
  # dropped: the planning list for the next round. Each keeps its project.
  @closest_n 10

  defp closest(projects, n) do
    for(pr <- projects, f <- pr.files, m <- f.modules, not translatable?(m), do: {pr, m})
    |> Enum.sort_by(fn {pr, m} -> {distance(m), length(blockers(m)), pr.name, m.name} end)
    |> Enum.take(n)
  end

  # ---------- the JSON report and the regression gate ----------

  # The numbers the gate compares, as plain string-keyed data so that the
  # report just written and a baseline read back from disk have the same
  # shape and can be diffed directly.
  defp data(projects, paths) do
    mods = for pr <- projects, f <- pr.files, m <- f.modules, do: m

    %{
      "note" =>
        "Readiness baseline for check.sh. Refresh with: elixir elixir/readiness.exs --json " <>
          "--update-baseline docs/readiness-baseline.json " <> Enum.join(paths, " "),
      "paths" => Enum.map(paths, &Path.expand/1),
      "projects" => Enum.map(projects, &project_data/1),
      "total" => counts(mods, Enum.sum(for pr <- projects, do: length(pr.files)))
    }
  end

  defp project_data(pr) do
    mods = for f <- pr.files, m <- f.modules, do: m

    pr.name
    |> then(&Map.put(counts(mods, length(pr.files)), "name", &1))
    |> Map.put("modules", Enum.sort_by(Enum.map(mods, &module_data(&1, pr)), &{&1["file"], &1["module"]}))
  end

  defp counts(mods, files) do
    %{
      "files" => files,
      "candidates" => length(mods),
      "translated" => Enum.count(mods, &translatable?/1),
      "blockers" => mods |> Enum.flat_map(&blockers/1) |> length(),
      "families" => mods |> Enum.flat_map(&families/1) |> Enum.uniq() |> length()
    }
  end

  defp module_data(m, pr) do
    %{
      "module" => m.name,
      "file" => Path.relative_to(m.path, Path.expand(pr.root)),
      "translated" => translatable?(m),
      "blockers" => length(blockers(m)),
      "distance" => distance(m)
    }
  end

  def json_report(projects, paths), do: enc(data(projects, paths), "") <> "\n"

  # A tiny pretty-printer: keys in sorted order (so a refresh diffs cleanly),
  # and a map whose values are all scalars on one line (module entries).
  defp enc(m, ind) when is_map(m) do
    kvs = m |> Map.to_list() |> Enum.sort_by(&elem(&1, 0))

    if Enum.all?(kvs, fn {_, v} -> not (is_map(v) or is_list(v)) end) do
      "{" <> Enum.map_join(kvs, ", ", fn {k, v} -> jstr(k) <> ": " <> enc(v, ind) end) <> "}"
    else
      inner = ind <> "  "
      "{\n" <> Enum.map_join(kvs, ",\n", fn {k, v} -> inner <> jstr(k) <> ": " <> enc(v, inner) end) <> "\n" <> ind <> "}"
    end
  end

  defp enc([], _ind), do: "[]"

  defp enc(l, ind) when is_list(l) do
    inner = ind <> "  "
    "[\n" <> Enum.map_join(l, ",\n", fn v -> inner <> enc(v, inner) end) <> "\n" <> ind <> "]"
  end

  defp enc(true, _ind), do: "true"
  defp enc(false, _ind), do: "false"
  defp enc(nil, _ind), do: "null"
  defp enc(n, _ind) when is_integer(n), do: Integer.to_string(n)
  defp enc(s, _ind) when is_binary(s), do: jstr(s)

  defp jstr(s) do
    body =
      s
      |> to_string()
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")
      |> String.replace("\t", "\\t")

    "\"" <> body <> "\""
  end

  defp read_baseline(path) do
    unless File.exists?(path) do
      die("no baseline at #{path}; write one with: elixir elixir/readiness.exs --json --update-baseline #{path} PATH...")
    end

    unless Code.ensure_loaded?(:json) do
      die("reading a baseline needs OTP 27 or later (the :json module); rewrite it with --update-baseline instead")
    end

    try do
      :json.decode(File.read!(path))
    rescue
      _ -> die("#{path} is not readable JSON; rewrite it with --json --update-baseline #{path} PATH...")
    end
  end

  defp baseline_paths(path) do
    case read_baseline(path) do
      %{"paths" => ps} when is_list(ps) and ps != [] -> ps
      _ -> die("#{path} records no paths; give them on the command line")
    end
  end

  # The gate. Fails when a project (or the total) translates fewer modules
  # than the baseline, or carries more blockers. An improvement is not a
  # failure: it is a reminder to refresh the baseline.
  defp check_baseline(projects, path) do
    base = read_baseline(path)
    now = data(projects, Map.get(base, "paths", []))

    by_name = fn d -> Map.new(d["projects"], &{&1["name"], &1}) end
    old = by_name.(base)
    new = by_name.(now)

    rows =
      for name <- Enum.map(base["projects"], & &1["name"]) ++ [nil] do
        {label, b, n} =
          if name == nil,
            do: {"all", base["total"], now["total"]},
            else: {name, old[name], new[name]}

        {label, b, n}
      end

    IO.puts("   baseline #{path} (#{length(base["projects"])} projects)")
    IO.puts("   #{pad("project", 16)}#{pad("translated", 14)}blockers")


    bad =
      for {label, b, n} <- rows, reduce: [] do
        acc ->
          cond do
            n == nil ->
              IO.puts("   #{pad(label, 16)}NOT MEASURED in this run")
              [label | acc]

            true ->
              t = cmp(b["translated"], n["translated"], :up)
              k = cmp(b["blockers"], n["blockers"], :down)

              mark =
                cond do
                  t.bad and k.bad -> "  <-- REGRESSION (both)"
                  t.bad -> "  <-- REGRESSION (translated)"
                  k.bad -> "  <-- REGRESSION (blockers)"
                  t.better or k.better -> "  (better)"
                  true -> ""
                end

              IO.puts(String.trim_trailing("   #{pad(label, 16)}#{pad(t.text, 14)}#{pad(k.text, 16)}#{mark}"))
              if t.bad or k.bad, do: [label | acc], else: acc
          end
      end

    module_diff(base, now)

    cond do
      bad != [] ->
        IO.puts("   READINESS REGRESSION in #{Enum.join(Enum.reverse(bad), ", ")}.")
        IO.puts("   Fewer modules translate, or more blockers, than #{path} records.")
        1

      improved?(base, now) ->
        IO.puts("   baseline met, and beaten: refresh it with")
        IO.puts("     elixir elixir/readiness.exs --json --update-baseline #{path} " <> Enum.join(Map.get(base, "paths", []), " "))
        0

      true ->
        IO.puts("   baseline met.")
        0
    end
  end

  defp improved?(base, now) do
    base["total"]["translated"] < now["total"]["translated"] or
      base["total"]["blockers"] > now["total"]["blockers"]
  end

  # translated must not go down, blockers must not go up
  defp cmp(b, n, dir) do
    bad = if dir == :up, do: n < b, else: n > b
    %{bad: bad, better: not bad and n != b, text: "#{b} -> #{n}"}
  end

  # which modules changed verdict, so a regression names names
  defp module_diff(base, now) do
    key = fn pr, m -> pr["name"] <> "/" <> m["file"] <> ":" <> m["module"] end
    flat = fn d -> for pr <- d["projects"], m <- pr["modules"], into: %{}, do: {key.(pr, m), m} end
    old = flat.(base)
    new = flat.(now)

    lost = for {k, m} <- old, m["translated"], new[k] == nil or not new[k]["translated"], do: k
    gained = for {k, m} <- new, m["translated"], old[k] == nil or not old[k]["translated"], do: k

    for k <- Enum.sort(lost), do: IO.puts("   no longer translated: #{k}")
    for k <- Enum.sort(gained), do: IO.puts("   newly translated: #{k}")
    :ok
  end

  defp pad(s, n), do: String.pad_trailing(to_string(s), n)

  # ---------- rendering ----------

  defp str(ast) do
    s = ast |> Macro.to_string() |> String.replace(~r/\s+/, " ")
    if String.length(s) > 70, do: String.slice(s, 0, 67) <> "...", else: s
  end

  defp blockers(m), do: Enum.filter(m.findings, &(&1.sev == :blocker))
  defp notes(m), do: Enum.filter(m.findings, &(&1.sev == :note))

  # translatable: no blockers, and (if the translator ran) it succeeded
  defp translatable?(m), do: blockers(m) == [] and m[:translated] != false

  # attach the file verdict to each module
  defp with_verdicts(projects) do
    for pr <- projects do
      files =
        for f <- pr.files do
          t = case f.translator do {:ok, _} -> true; {:error, _} -> false; _ -> nil end
          %{f | modules: Enum.map(f.modules, &Map.put(&1, :translated, t))}
        end
      %{pr | files: files}
    end
  end

  defp verdict(m) do
    cond do
      blockers(m) == [] and m.translated == true -> "yes"
      blockers(m) == [] and m.translated == nil -> "yes (walker only)"
      blockers(m) == [] -> "no (translator failed, walker found nothing: see notes)"
      m.translated == true -> "no (walker found blockers, translator accepted)"
      true -> "no"
    end
  end

  defp freq(mods), do: freq_by(mods, & &1.kind)

  defp freq_by(mods, f) do
    mods
    |> Enum.flat_map(&blockers/1)
    |> Enum.frequencies_by(f)
    |> Enum.sort_by(fn {k, n} -> {-n, k} end)
  end

  # modules in which a kind occurs
  defp spread(mods), do: spread_by(mods, & &1.kind)

  defp spread_by(mods, f) do
    for m <- mods, k <- m |> blockers() |> Enum.map(f) |> Enum.uniq(), reduce: %{} do
      acc -> Map.update(acc, k, 1, &(&1 + 1))
    end
  end

  # Families group the fine-grained kinds for planning: every call into the
  # same module is one family, all module-local helpers are one, and so on.
  # The kind stays the actionable label ("Logger.info/1"); the family says
  # what a translator feature would have to cover ("call to Logger").
  @remote_kind ~r{^(?<mod>[A-Z][A-Za-z0-9_.]*|:[a-z][a-z0-9_]*)\.[a-z_][A-Za-z0-9_?!]*/[0-9]+$}

  def family(kind) do
    cond do
      String.starts_with?(kind, "local call ") -> "call to a helper in the same module"
      String.starts_with?(kind, "imported/macro call ") -> "call to an imported function or macro"
      String.starts_with?(kind, "Kernel.") -> "Kernel function or guard"
      m = Regex.named_captures(@remote_kind, kind) -> "call to " <> m["mod"]
      true -> kind
    end
  end

  defp text(projects) do
    mods = for pr <- projects, f <- pr.files, m <- f.modules, do: m
    body =
      for pr <- projects, f <- pr.files, f.modules != [] do
        head = "== #{f.path}"
        tr = case f.translator do
          {:ok, s} -> "translator: " <> s
          {:error, s} -> "translator: FAILED: " <> s
          {:skipped, s} -> "translator: skipped (#{s})"
        end
        per_mod =
          for m <- f.modules do
            [
              "#{m.name} (#{kind_name(m.kind)}, line #{m.line}): translated #{verdict(m)}",
              for fnd <- m.findings do
                sev = if fnd.sev == :note, do: " [note]", else: ""
                "  #{Path.basename(m.path)}:#{fnd.line}: #{fnd.kind}#{sev}" <> if(fnd.detail == "", do: "", else: " -- " <> fnd.detail)
              end
            ]
          end
        [head, "   " <> tr, per_mod, ""]
      end
    yes = Enum.count(mods, &translatable?/1)
    skipped = for pr <- projects, f <- pr.files, s <- f.skipped, do: s
    summary = [
      "#{length(mods)} candidate modules (GenServer or receive loop) in #{Enum.sum(for pr <- projects, do: length(pr.files))} files: #{yes} translatable, #{length(mods) - yes} not",
      if(skipped == [], do: [], else: "#{length(skipped)} other modules skipped (#{skipped |> Enum.frequencies_by(&elem(&1, 1)) |> Enum.map_join(", ", fn {w, n} -> "#{n} #{w}" end)})"),
      "blocking constructs by family (occurrences / modules):",
      for({k, n} <- freq_by(mods, &family(&1.kind)),
          do: "  #{String.pad_leading("#{n}", 5)}  #{String.pad_leading("#{spread_by(mods, &family(&1.kind))[k]}", 3)}  #{k}"),
      "blocking constructs by frequency (occurrences / modules):",
      for({k, n} <- freq(mods), do: "  #{String.pad_leading("#{n}", 5)}  #{String.pad_leading("#{spread(mods)[k]}", 3)}  #{k}"),
      "closest to translatable (distinct blocker families / blockers):",
      for({pr, m} <- closest(projects, @closest_n),
          do: "  #{String.pad_leading("#{distance(m)}", 5)}  #{String.pad_leading("#{length(blockers(m))}", 3)}  #{pr.name}/#{m.name}: " <> Enum.join(families(m), ", "))
    ]
    [body, summary] |> List.flatten() |> Enum.join("\n")
  end

  defp kind_name(:genserver), do: "GenServer"
  defp kind_name(:loop), do: "receive loop"

  defp markdown(projects) do
    mods = for pr <- projects, f <- pr.files, m <- f.modules, do: m
    yes = Enum.count(mods, &translatable?/1)
    skipped = for pr <- projects, f <- pr.files, s <- f.skipped, do: s
    fr = freq(mods)
    sp = spread(mods)
    fam = freq_by(mods, &family(&1.kind))
    fsp = spread_by(mods, &family(&1.kind))
    total_blockers = Enum.sum(Enum.map(fr, &elem(&1, 1)))
    [
      "# Translator readiness of real projects",
      "",
      "Generated by `elixir elixir/readiness.exs --markdown " <> Enum.map_join(projects, " ", & &1.root) <> "`.",
      "Do not edit by hand; regenerate after a translator change.",
      "",
      "The same numbers are committed as `docs/readiness-baseline.json`, and `check.sh` re-measures them and fails",
      "if a project translates fewer modules than the baseline records or carries more blockers. A round that lands",
      "translator features is expected to *beat* the baseline, so refreshing both files is part of landing one:",
      "",
      "```",
      "elixir elixir/readiness.exs --json --update-baseline docs/readiness-baseline.json \\",
      "  " <> Enum.map_join(projects, " ", & &1.root),
      "elixir elixir/readiness.exs --markdown \\",
      "  " <> Enum.map_join(projects, " ", & &1.root) <> " > docs/readiness.md",
      "```",
      "",
      "For every module that uses `GenServer` or contains a `receive`, the harness runs the translator on the file",
      "(dry, retrying with `--pid` for unregistered names and `--pubsub` for a PubSub under another name) and",
      "walks the module's AST against the allowlist of forms",
      "the translator supports (`@supported` at the top of `elixir/readiness.exs`), reporting every unsupported",
      "construct, not only the first one the translator hits. A module is *translated* when the walker finds no",
      "blocker and the translator accepted the file. Notes (things the translator silently ignores, or that only",
      "need a `--pid` flag) do not count against a module.",
      "",
      "## Summary",
      "",
      "| Project | Files | Candidate modules | Translated | Blockers | Blocker families |",
      "|---|---:|---:|---:|---:|---:|",
      for pr <- projects do
        pm = for f <- pr.files, m <- f.modules, do: m
        "| #{pr.name} | #{length(pr.files)} | #{length(pm)} | #{Enum.count(pm, &translatable?/1)} | #{pm |> Enum.flat_map(&blockers/1) |> length()} | #{pm |> Enum.flat_map(&families/1) |> Enum.uniq() |> length()} |"
      end,
      "| **all** | #{Enum.sum(for pr <- projects, do: length(pr.files))} | #{length(mods)} | #{yes} | #{total_blockers} | #{length(fam)} |",
      "",
      if(skipped == [], do: [], else: [
        "Other modules seen (not GenServers, no `receive`; skipped): " <>
          (skipped |> Enum.frequencies_by(&elem(&1, 1)) |> Enum.sort_by(fn {_, n} -> -n end) |> Enum.map_join(", ", fn {w, n} -> "#{n} #{w}" end)) <> ".",
        ""
      ]),
      "## Blocking constructs by family",
      "",
      "The same blockers grouped into the feature each one would need: every call into one module is one family,",
      "all calls to helpers of the same module are one, and every other kind is its own family. This is the",
      "planning table -- it says what a translator feature would have to cover, largest first.",
      "",
      "| # | Family | Occurrences | Modules |",
      "|---:|---|---:|---:|",
      for({{k, n}, i} <- Enum.with_index(fam, 1), do: "| #{i} | `#{md_cell(k)}` | #{n} | #{fsp[k]} |"),
      "",
      "## Closest to translatable",
      "",
      "*Distance* is the number of distinct blocker families a module still hits, not the number of blockers:",
      "twelve `Logger.info/1` calls in one module are one feature to build, one `Logger` call and one `with` are two.",
      "It is the per-module column of the table above and the planning list here -- the #{@closest_n} untranslatable",
      "modules that are fewest features away, nearest first (ties broken by the number of blockers).",
      "",
      "| # | Project | Module | Distance | Blockers | Families |",
      "|---:|---|---|---:|---:|---|",
      for {{pr, m}, i} <- Enum.with_index(closest(projects, @closest_n), 1) do
        "| #{i} | #{pr.name} | `#{m.name}` | #{distance(m)} | #{length(blockers(m))} | " <>
          Enum.map_join(families(m), ", ", &"`#{md_cell(&1)}`") <> " |"
      end,
      "",
      "## Blocking constructs by frequency",
      "",
      "Occurrences across all candidate modules, and the number of modules the construct appears in.",
      "A kind is a stable label: `Mod.fun/arity` for a remote call the translator has no mapping for,",
      "`local call f/n` for a helper defined in the module, `Kernel.f/n` for a Kernel function or guard,",
      "`imported/macro call f/n` for anything else with no module prefix, and a named form otherwise.",
      "",
      "| # | Construct | Occurrences | Modules |",
      "|---:|---|---:|---:|",
      for({{k, n}, i} <- Enum.with_index(fr, 1), do: "| #{i} | `#{md_cell(k)}` | #{n} | #{sp[k]} |"),
      "",
      "## Modules",
      "",
      "| Project | Module | File | Kind | Translated | Blockers | Distance | Top constructs |",
      "|---|---|---|---|---|---:|---:|---|",
      for pr <- projects, f <- pr.files, m <- f.modules do
        top =
          m |> blockers() |> Enum.frequencies_by(& &1.kind) |> Enum.sort_by(fn {k, n} -> {-n, k} end) |> Enum.take(4)
          |> Enum.map_join(", ", fn {k, n} -> "`#{md_cell(k)}`" <> if(n > 1, do: " (#{n})", else: "") end)
        rel = Path.relative_to(m.path, Path.expand(pr.root))
        "| #{pr.name} | `#{m.name}` | `#{rel}` | #{kind_name(m.kind)} | #{verdict_short(m)} | #{length(blockers(m))} | #{distance(m)} | #{top} |"
      end,
      "",
      "## Per-module detail",
      "",
      "Every distinct blocking construct per module with its line numbers (notes in italics). The text report",
      "(`elixir elixir/readiness.exs PATH`) lists each occurrence with its source snippet.",
      "",
      for pr <- projects, f <- pr.files, m <- f.modules do
        tr = case f.translator do
          {:ok, s} -> s
          {:error, s} -> "failed: `#{s}`"
          {:skipped, s} -> "skipped (#{s})"
        end
        groups =
          m |> blockers() |> Enum.group_by(& &1.kind) |> Enum.sort_by(fn {k, fs} -> {-length(fs), k} end)
        note_groups = m |> notes() |> Enum.group_by(& &1.kind) |> Enum.sort_by(fn {k, _} -> k end)
        [
          "### #{m.name} (#{pr.name})",
          "",
          "`#{Path.relative_to(m.path, Path.expand(pr.root))}`, #{kind_name(m.kind)}; translator: #{tr}; translated: #{verdict(m)}.",
          "",
          if(groups == [] and note_groups == [], do: ["No findings.", ""], else: []),
          for({k, fs} <- groups, do: "- `#{k}` at " <> lines_str(fs)),
          for({k, fs} <- note_groups, do: "- *#{k}* at " <> lines_str(fs)),
          ""
        ]
      end
    ]
    |> List.flatten()
    |> Enum.join("\n")
  end

  # a `|` inside a markdown table cell splits it, backticks or not
  defp md_cell(s), do: String.replace(s, "|", "\\|")

  defp lines_str(fs) do
    ls = fs |> Enum.map(& &1.line) |> Enum.uniq() |> Enum.sort()
    shown = Enum.take(ls, 12)
    Enum.join(shown, ", ") <> if(length(ls) > 12, do: " (+#{length(ls) - 12} more)", else: "")
  end

  defp verdict_short(m) do
    cond do
      translatable?(m) -> "yes"
      blockers(m) == [] -> "no (translator)"
      true -> "no"
    end
  end
end

Readiness.main(System.argv())
