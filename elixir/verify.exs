#!/usr/bin/env elixir
# A friendly front end for the project's existing verification tools.
#
#   ./verify                       run every stage
#   ./verify translate prove       run only these stages
#   ./verify --no-color            plain text, no ANSI (also respects NO_COLOR)
#
# This does not check anything itself — it shells out to the same tools
# check.sh always used (the translator, diff, lake build, grep,
# elixir/test/run_fixtures.exs, the BEAM drivers) and re-renders whatever
# they printed: a `file:line:col: error: ...` from Lean becomes a source
# frame with a caret and, where the message is one we recognise, a plain
# English note underneath; a `diff -u` becomes a colored hunk. Nothing here
# decides pass/fail on its own — every verdict is still the underlying
# tool's exit code.
#
# Unlike check.sh, a failure does not stop the run: every stage executes
# and the summary at the end lists everything that needs attention, not
# just the first thing that broke.

defmodule V.Ansi do
  def set(on?), do: Process.put(:v_color, on?)
  def on?, do: Process.get(:v_color, false)

  def c(text, codes) do
    if on?() do
      IO.ANSI.format(codes ++ [text, :reset]) |> IO.iodata_to_binary()
    else
      text
    end
  end

  def bold(t), do: c(t, [:bright])
  def dim(t), do: c(t, [:faint])
  def red(t), do: c(t, [:red, :bright])
  def green(t), do: c(t, [:green])
  def yellow(t), do: c(t, [:yellow])
  def cyan(t), do: c(t, [:cyan])
end

defmodule V.Frame do
  alias V.Ansi, as: A

  # Common Lean diagnostic prefixes translated into a plain-English aside.
  # Only messages we're confident about get a note; everything else just
  # shows Lean's own text, unexplained rather than misexplained.
  defp explanations, do: [
    {~r/declaration uses .sorry./,
     "this theorem isn't actually proved — Lean accepted `sorry` as a stand-in. Replace it with a real proof."},
    {~r/unsolved goals/,
     "a tactic block ended before every goal was closed. Whatever case is left wasn't handled — try `sorry` in its place and inspect the goal, or add the missing case explicitly."},
    {~r/type mismatch/,
     "an expression here doesn't have the type Lean expected — check the term right before this point and what it's being used as."},
    {~r/unknown identifier/,
     "Lean doesn't recognize this name — check the spelling, or that it's defined/imported above this point."},
    {~r/unknown constant/,
     "Lean doesn't recognize this name — check the spelling or the relevant `import`."},
    {~r/function expected/,
     "something here is being applied like a function, but Lean doesn't think it is one — check parentheses and argument count."},
    {~r/failed to synthesize/,
     "Lean needed to build an instance (like `Decidable` or `Inhabited`) automatically here and couldn't."},
    {~r/ambiguous/,
     "more than one declaration matches this name — qualify it, or check what's `open`."},
    {~r/linter\.unusedVariables/,
     "this name is bound but never used — prefix it with `_` if that's intentional."}
  ]


  def diag(file, line, col, kind, msg, detail_lines, root) do
    ln = String.to_integer(line)
    colno = String.to_integer(col)
    src = source_lines(root, file)
    gutter_w = max(String.length(Integer.to_string(ln)), 2)

    label =
      case kind do
        "error" -> A.red("error")
        "warning" -> A.yellow("warning")
        _ -> A.cyan("info")
      end

    loc = A.dim("#{file}:#{line}:#{col}")
    header = "#{label}: #{A.bold(msg)}\n  #{A.dim("-->")} #{loc}"

    frame =
      case Enum.at(src, ln - 1) do
        nil ->
          []

        line_text ->
          caret_color = if kind == "error", do: &A.red/1, else: &A.yellow/1
          gutter(gutter_w, ln, line_text) ++
            [
              blank_gutter(gutter_w) <> A.dim("│ ") <>
                String.duplicate(" ", colno) <> caret_color.("^")
            ]
      end

    detail =
      detail_lines
      |> Enum.map(&String.trim_trailing/1)
      |> trim_blank_edges()
      |> Enum.map(&("  " <> A.dim(&1)))

    note = explain(msg)

    ([header, ""] ++ frame)
    |> then(fn lines -> if detail == [], do: lines, else: lines ++ ["" | detail] end)
    |> then(fn lines -> if note, do: lines ++ ["", "  " <> A.cyan("note") <> ": " <> note], else: lines end)
    |> Enum.join("\n")
  end

  defp gutter(w, n, text), do: [A.dim(String.pad_leading(Integer.to_string(n), w)) <> A.dim(" │ ") <> text]
  defp blank_gutter(w), do: String.duplicate(" ", w + 1)

  defp trim_blank_edges(lines) do
    lines |> Enum.drop_while(&(&1 == "")) |> Enum.reverse() |> Enum.drop_while(&(&1 == "")) |> Enum.reverse()
  end

  defp explain(msg), do: Enum.find_value(explanations(), fn {re, note} -> if Regex.match?(re, msg), do: note end)

  defp source_lines(root, file) do
    path = if Path.type(file) == :absolute, do: file, else: Path.join(root, file)

    case File.read(path) do
      {:ok, content} -> String.split(content, "\n")
      {:error, _} -> []
    end
  end
end

defmodule V.Blob do
  # Lean's own diagnostics (from `lake env lean FILE`, e.g. via the fixture
  # runner's `lean: check`) read `file:line:col: kind: message`. Lake's build
  # log (`lake build`) puts the severity first instead: `kind: file:line:col:
  # message`. Both occur in this project's tooling, so both are recognised.
  defp diag_re_file_first, do: ~r/^([^\s:][^:]*):(\d+):(\d+):\s*(error|warning|info):\s*(.*)$/
  defp diag_re_kind_first, do: ~r/^(error|warning|info):\s*([^\s:][^:]*):(\d+):(\d+):\s*(.*)$/

  # `file, line, col, kind, msg` if `line` opens a Lean diagnostic, else nil.
  def match_diag(line) do
    case Regex.run(diag_re_file_first(), line) do
      [_, f, l, c, k, m] ->
        {f, l, c, k, m}

      nil ->
        case Regex.run(diag_re_kind_first(), line) do
          [_, k, f, l, c, m] -> {f, l, c, k, m}
          nil -> nil
        end
    end
  end

  # Scans arbitrary tool output for diagnostic headers and turns each one
  # into a source frame via V.Frame; everything else passes through dimmed,
  # unchanged — except a few lines of Lake's own boilerplate (the full
  # job-invocation `trace:` command, and its "build failed" trailer, which
  # just restates what our own summary line already says) that add noise
  # without adding information, and would otherwise get absorbed into
  # whichever diagnostic happens to be last.
  def render(text, root) do
    lines =
      text
      |> String.split("\n")
      |> Enum.reject(fn l ->
        String.starts_with?(l, "trace: ") or l in ["error: build failed", "Some required targets logged failures:"]
      end)

    {pre, blocks} = split_blocks(lines)

    pre_r =
      pre
      |> Enum.reject(&(String.trim(&1) == ""))
      |> Enum.map(&V.Ansi.dim/1)

    block_r =
      Enum.map(blocks, fn {f, l, c, k, m, body} -> V.Frame.diag(f, l, c, k, m, body, root) end)

    (pre_r ++ block_r) |> Enum.join("\n\n")
  end

  defp split_blocks(lines) do
    {blocks, cur, pre} =
      Enum.reduce(lines, {[], nil, []}, fn line, {blocks, cur, pre} ->
        case match_diag(line) do
          {f, l, c, k, m} ->
            blocks = if cur, do: [cur | blocks], else: blocks
            {blocks, {f, l, c, k, m, []}, pre}

          nil ->
            case cur do
              nil -> {blocks, cur, [line | pre]}
              {f, l, c, k, m, body} -> {blocks, {f, l, c, k, m, [line | body]}, pre}
            end
        end
      end)

    blocks = if cur, do: [cur | blocks], else: blocks
    blocks = blocks |> Enum.reverse() |> Enum.map(fn {f, l, c, k, m, b} -> {f, l, c, k, m, Enum.reverse(b)} end)
    {Enum.reverse(pre), blocks}
  end
end

defmodule V.Diff do
  alias V.Ansi, as: A

  def render(text) do
    text
    |> String.split("\n")
    |> Enum.map(fn
      "+++" <> _ = l -> A.bold(l)
      "---" <> _ = l -> A.bold(l)
      "@@" <> _ = l -> A.cyan(l)
      "+" <> _ = l -> A.green(l)
      "-" <> _ = l -> A.red(l)
      l -> A.dim(l)
    end)
    |> Enum.join("\n")
  end
end

defmodule V.Run do
  alias V.Ansi, as: A

  @root Path.expand("..", __DIR__)

  @gen [
    {"Lock", "elixir/src/lock.ex", "Leanactors.Gen.Lock", ["--pid", "Lock=server"]},
    {"Bank", "elixir/src/bank.ex", "Leanactors.Gen.Bank", ["--pid", "Bank=bank"]},
    {"Supervisor", "elixir/src/supervisor.ex", "Leanactors.Gen.Supervisor", ["--pid", "Sup=sup"]},
    {"Task", "elixir/src/task.ex", "Leanactors.Gen.Task", ["--pid", "Caller=caller"]},
    {"Watchdog", "elixir/src/watchdog.ex", "Leanactors.Gen.Watchdog", ["--pid", "Watchdog=watchdog"]},
    {"Ttl", "elixir/src/ttl.ex", "Leanactors.Gen.Ttl", []},
    {"Registry", "elixir/src/registry.ex", "Leanactors.Gen.Registry", []},
    {"Feed", "elixir/src/feed.ex", "Leanactors.Gen.Feed", []},
    {"Ringlog", "elixir/src/ringlog.ex", "Leanactors.Gen.Ringlog", []},
    # untyped mode: no @type anywhere, no --pid flag (the registered name
    # comes from `name: __MODULE__` in start_link/3)
    {"TableRegistry", "elixir/real/table_registry.ex", "Leanactors.Gen.TableRegistry", []},
    # untyped mode again: the reply type is probed from the clause bodies (a
    # list), and the LiveView's socket is the record of the assigns it touches
    {"LogStore", "elixir/real/log_store.ex", "Leanactors.Gen.LogStore", []},
    {"LogsLive", "elixir/real/logs_live.ex", "Leanactors.Gen.LogsLive", []},
    # and a third: a chain of assigns folded into one record update, and a
    # payload inferred `term() | nil` from the `!= nil` the body writes
    {"RadioLive", "elixir/real/radio_live.ex", "Leanactors.Gen.RadioLive", []}
  ]

  @drivers [
    {"bank", "elixir/bank.exs", []},
    {"lock", "elixir/lock.exs", ["10", "5000"]},
    {"supervisor", "elixir/supervisor.exs", []},
    {"task", "elixir/task.exs", []},
    {"watchdog", "elixir/watchdog.exs", []},
    {"ttl", "elixir/ttl.exs", []},
    {"registry", "elixir/registry.exs", []},
    {"feed", "elixir/feed.exs", []},
    {"ringlog", "elixir/ringlog.exs", []},
    {"table_registry", "elixir/table_registry.exs", []},
    {"fuzz", "elixir/fuzz.exs", ["--seed", "1", "--runs", "200"]}
  ]

  @stages ["translate", "fixtures", "prove", "run"]

  def main(argv) do
    {opts, wanted, _} = OptionParser.parse(argv, switches: [color: :boolean])

    color? =
      Keyword.get(opts, :color, true) and
        System.get_env("NO_COLOR") in [nil, ""] and
        IO.ANSI.enabled?()

    V.Ansi.set(color?)
    ensure_lake_on_path()

    stages = if wanted == [], do: @stages, else: Enum.filter(@stages, &(&1 in wanted))
    if stages == [], do: die("no such stage among #{Enum.join(@stages, ", ")}")

    t0 = System.monotonic_time(:millisecond)
    results = Enum.map(stages, &run_stage/1)
    elapsed = (System.monotonic_time(:millisecond) - t0) / 1000

    summarize(results, elapsed)
    if Enum.any?(results, &(&1.status == :fail)), do: System.halt(1)
  end

  # ── stages ──────────────────────────────────────────────────────────

  defp run_stage("translate") do
    banner("translate", "Elixir @type declarations → Lean, checked byte-for-byte against Leanactors/Gen/")
    items = Enum.map(@gen, &translate_one/1)
    ok? = Enum.all?(items, &(&1.status == :ok))
    Enum.each(items, &print_item/1)
    %{name: "translate", status: (if ok?, do: :ok, else: :fail)}
  end

  defp run_stage("fixtures") do
    banner("fixtures", "translator regression suite (elixir/test/fixtures)")
    {out, status} = System.cmd("elixir", ["elixir/test/run_fixtures.exs"], cd: @root, stderr_to_stdout: true)
    lines = String.split(out, "\n")
    {passes, _fails} = Enum.split_with(lines, &String.starts_with?(&1, "PASS "))
    summary = Enum.find(lines, &(&1 =~ ~r/^\d+\/\d+ fixtures passed/))

    if status == 0 do
      print_item(%{status: :ok, label: summary || "#{length(passes)} fixtures passed"})
    else
      fail_blocks = extract_fixture_failures(out)
      print_item(%{status: :fail, label: summary || "fixtures failed"})
      Enum.each(fail_blocks, fn {name, why} ->
        IO.puts("")
        IO.puts("  " <> A.bold(A.red("✗ " <> name)))
        IO.puts(indent(V.Blob.render(why, @root), 4))
      end)
    end

    %{name: "fixtures", status: (if status == 0, do: :ok, else: :fail)}
  end

  defp run_stage("prove") do
    banner("prove", "lake build (every proof and #eval'd checker), then a sorry/axiom scan")
    {out, status} = System.cmd("lake", ["build"], cd: @root, stderr_to_stdout: true)

    diagnostics =
      out
      |> String.split("\n")
      |> Enum.filter(fn line ->
        case V.Blob.match_diag(line) do
          {_, _, _, k, _} -> k in ["error", "warning"]
          nil -> false
        end
      end)

    infos = out |> String.split("\n") |> Enum.filter(&(&1 =~ ~r/^info:/)) |> Enum.map(&String.replace_prefix(&1, "info: ", ""))

    build_ok? = status == 0 and diagnostics == []

    if build_ok? do
      print_item(%{status: :ok, label: "lake build — all proofs check, no warnings"})
      if infos != [] do
        IO.puts("")
        IO.puts("  " <> A.dim("checker results (#eval), for reference:"))
        Enum.each(infos, &IO.puts("    " <> compact_info(&1)))
      end
    else
      print_item(%{status: :fail, label: "lake build reported problems"})
      IO.puts("")
      IO.puts(indent(V.Blob.render(out, @root), 4))
    end

    {sorry_out, _} = System.cmd("grep", ["-rn", "-E", "\\bsorry\\b|^\\s*axiom\\b", "Leanactors"], cd: @root, stderr_to_stdout: true)
    hits = sorry_out |> String.split("\n") |> Enum.reject(&(&1 == ""))

    if hits == [] do
      print_item(%{status: :ok, label: "no sorry, no axiom"})
    else
      print_item(%{status: :fail, label: "#{length(hits)} sorry/axiom found"})
      Enum.each(hits, fn hit ->
        [file, line, text] = String.split(hit, ":", parts: 3)
        kind = if text =~ ~r/\bsorry\b/, do: "an incomplete proof (`sorry`)", else: "an unproved `axiom`"
        IO.puts("")
        IO.puts(indent(V.Frame.diag(file, line, "0", "error", "#{kind} here — this isn't actually verified", [], @root), 2))
      end)
    end

    %{name: "prove", status: (if build_ok? and hits == [], do: :ok, else: :fail)}
  end

  defp run_stage("run") do
    banner("run", "each Elixir/BEAM driver, then the seeded Lean-vs-BEAM fuzz")
    results =
      Enum.map(@drivers, fn {name, script, args} ->
        {out, status} = System.cmd("elixir", [script | args], cd: @root, stderr_to_stdout: true)
        last = out |> String.split("\n") |> Enum.reject(&(&1 == "")) |> List.last()
        %{status: (if status == 0, do: :ok, else: :fail), label: pad(name, 16) <> (last || ""), full: out}
      end)

    Enum.each(results, fn r ->
      print_item(r)
      if r.status == :fail do
        IO.puts("")
        IO.puts(indent(A.dim(r.full), 4))
      end
    end)

    %{name: "run", status: (if Enum.all?(results, &(&1.status == :ok)), do: :ok, else: :fail)}
  end

  # ── one Gen/ module ─────────────────────────────────────────────────

  defp translate_one({label, src, ns, flags}) do
    {out, err, status} = translate(src, ns, flags)
    gen_path = "Leanactors/Gen/#{label}.lean"

    cond do
      status != 0 ->
        %{status: :fail, label: label, detail: {:blob, err}}

      not File.exists?(Path.join(@root, gen_path)) ->
        %{status: :fail, label: label, detail: {:text, "#{gen_path} does not exist yet"}}

      File.read!(Path.join(@root, gen_path)) != out ->
        tmp = Path.join(System.tmp_dir!(), "verify-#{label}.lean")
        File.write!(tmp, out)
        {diff, _} = System.cmd("diff", ["-u", gen_path, tmp], cd: @root, stderr_to_stdout: true)
        %{status: :fail, label: label, detail: {:diff, diff}}

      true ->
        %{status: :ok, label: label}
    end
  end

  # System.cmd only captures one stream at a time, and stdout here has to
  # stay pure Lean source (it's diffed byte-for-byte against Gen/), so
  # stderr can't just be merged in. Redirect it to a temp file instead,
  # the same trick elixir/test/run_fixtures.exs uses.
  defp translate(src, ns, flags) do
    errfile = Path.join(System.tmp_dir!(), "verify-translate-stderr-#{:erlang.unique_integer([:positive])}")
    cmd = Enum.map_join(["elixir", "elixir/to_lean.exs", src, ns | flags], " ", &shell_quote/1) <> " 2>" <> shell_quote(errfile)
    {out, status} = System.cmd("sh", ["-c", cmd], cd: @root)
    err = File.read!(errfile)
    File.rm(errfile)
    {out, err, status}
  rescue
    _ -> {"", "", 1}
  end

  defp shell_quote(s), do: "'" <> String.replace(s, "'", "'\\''") <> "'"

  # ── fixture failure extraction (for pretty sub-frames) ──────────────

  defp extract_fixture_failures(out) do
    out
    |> String.split("\n")
    |> Enum.reduce({[], nil}, fn line, {acc, cur} ->
      cond do
        String.starts_with?(line, "FAIL ") ->
          acc = if cur, do: [cur | acc], else: acc
          [name | _] = line |> String.trim_leading("FAIL ") |> String.split(":", parts: 2)
          rest = line |> String.trim_leading("FAIL ") |> String.trim_leading(name) |> String.trim_leading(": ")
          {acc, {name, rest}}

        String.starts_with?(line, "PASS ") ->
          acc = if cur, do: [cur | acc], else: acc
          {acc, nil}

        cur != nil ->
          {name, body} = cur
          {acc, {name, body <> "\n" <> String.trim_leading(line)}}

        true ->
          {acc, cur}
      end
    end)
    |> then(fn {acc, cur} -> if cur, do: [cur | acc], else: acc end)
    |> Enum.reverse()
  end

  # ── presentation ─────────────────────────────────────────────────────

  defp banner(name, subtitle) do
    IO.puts("")
    IO.puts(A.bold(A.cyan("▸ #{name}")) <> "  " <> A.dim(subtitle))
  end

  defp print_item(%{status: :fail, label: label, detail: {:diff, diff}}) do
    IO.puts("  #{A.red("✗")} #{label}  #{A.dim("(Leanactors/Gen/#{label}.lean is out of date)")}")
    IO.puts("")
    IO.puts(indent(V.Diff.render(diff), 4))
    IO.puts("")
    IO.puts("    " <> A.cyan("note") <> ": the committed file no longer matches what the translator produces from " <>
              "elixir/src/#{String.downcase(label)}.ex. If the .ex file changed on purpose, regenerate it (see " <>
              "check.sh); if it didn't, something upstream — the translator or the source — drifted.")
  end

  defp print_item(%{status: :fail, label: label, detail: {:blob, text}}) do
    IO.puts("  #{A.red("✗")} #{label}  #{A.dim("(translator failed)")}")
    IO.puts("")
    IO.puts(indent(V.Blob.render(text, @root), 4))
  end

  defp print_item(%{status: :fail, label: label, detail: {:text, msg}}) do
    IO.puts("  #{A.red("✗")} #{label}  #{A.dim(msg)}")
  end

  defp print_item(%{status: :ok, label: label}), do: IO.puts("  #{A.green("✓")} #{label}")
  defp print_item(%{status: :fail, label: label}), do: IO.puts("  #{A.red("✗")} #{label}")

  defp summarize(results, elapsed) do
    ok = Enum.count(results, &(&1.status == :ok))
    total = length(results)
    failed = Enum.filter(results, &(&1.status == :fail)) |> Enum.map(& &1.name)

    IO.puts("")
    IO.puts(A.dim(String.duplicate("─", 60)))

    if failed == [] do
      IO.puts("  #{A.green("✓")} #{A.bold("#{ok}/#{total} stages ok")}  #{A.dim("(#{fmt(elapsed)})")}")
    else
      IO.puts(
        "  #{A.red("✗")} #{A.bold("#{ok}/#{total} stages ok")} — failed: #{A.red(Enum.join(failed, ", "))}  #{A.dim("(#{fmt(elapsed)})")}"
      )
    end
  end

  defp compact_info(line) do
    case Regex.run(~r/^(\S+:\d+:\d+):\s*(.*)$/, line) do
      [_, loc, val] -> A.dim(loc) <> "  " <> truncate(val, 100)
      _ -> line
    end
  end

  defp truncate(s, n) when byte_size(s) > n, do: binary_part(s, 0, n) <> A.dim(" …")
  defp truncate(s, _n), do: s

  defp fmt(seconds), do: "#{:erlang.float_to_binary(seconds, decimals: 1)}s"
  defp pad(s, n), do: String.pad_trailing(s, n)
  defp indent(text, n) do
    prefix = String.duplicate(" ", n)
    text |> String.split("\n") |> Enum.map(&(prefix <> &1)) |> Enum.join("\n")
  end

  defp ensure_lake_on_path do
    if System.find_executable("lake") == nil do
      elan = Path.join(System.user_home!(), ".elan/bin")
      System.put_env("PATH", elan <> ":" <> System.get_env("PATH", ""))
    end
  end

  defp die(msg) do
    IO.puts(:stderr, "verify: " <> msg)
    System.halt(1)
  end
end

V.Run.main(System.argv())
