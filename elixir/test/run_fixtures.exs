# Translator regression fixtures.
#
#   elixir elixir/test/run_fixtures.exs            # run every fixture, exit 1 on any failure
#   elixir elixir/test/run_fixtures.exs --regen    # rewrite expected/*.lean from the translator
#   elixir elixir/test/run_fixtures.exs NAME ...   # only these fixtures (basenames without .ex)
#
# A fixture is elixir/test/fixtures/NAME.ex. Its leading comment block (the
# `#` lines before the first non-comment line) carries directives:
#
#   # translate: --pid Foo=foo ...   extra translator arguments (default none)
#   # expect: ok                     translation must succeed and match
#                                    elixir/test/expected/NAME.lean byte for byte
#   # expect: error SUBSTRING        translation must fail (non-zero exit) with
#                                    SUBSTRING somewhere on stderr
#   # warn: SUBSTRING                (ok fixtures) stderr must contain SUBSTRING
#   # lean: check                    (ok fixtures) the expected file must also
#                                    compile: it is copied to a scratch dir and
#                                    `lake env lean FILE` is run from the repo
#                                    root with no errors and no warnings
#                                    (the runner builds Leanactors.Sys first)
#
# Each fixture is translated into namespace Leanactors.Fixtures.<CamelName>.
# `--regen` rewrites every ok fixture's expected file from the translator's
# current output (see regen_expected.sh); review the diff before committing.

defmodule Fixtures do
  @root Path.expand("../..", __DIR__)
  @translator Path.join(@root, "elixir/to_lean.exs")
  @fixtures Path.join(__DIR__, "fixtures")
  @expected Path.join(__DIR__, "expected")

  def main(argv) do
    {regen?, names} = {"--regen" in argv, Enum.reject(argv, &(&1 == "--regen"))}
    ensure_lake_on_path()
    scratch = Path.join(System.tmp_dir!(), "leanactors-fixtures")
    File.mkdir_p!(scratch)
    File.mkdir_p!(@expected)

    all = @fixtures |> Path.join("*.ex") |> Path.wildcard() |> Enum.sort()
    picked =
      case names do
        [] -> all
        _ -> Enum.filter(all, &(Path.basename(&1, ".ex") in names))
      end
    if picked == [], do: die("no fixtures found in #{@fixtures}")
    if Enum.any?(picked, &(Map.get(directives(&1), "lean") == "check")), do: build_library()

    results = Enum.map(picked, &run_one(&1, scratch, regen?))
    failed = Enum.count(results, &(&1 == :fail))
    IO.puts("#{length(results) - failed}/#{length(results)} fixtures passed")
    if failed > 0, do: System.halt(1)
  end

  defp run_one(src, scratch, regen?) do
    name = Path.basename(src, ".ex")
    d = directives(src)
    ns = "Leanactors.Fixtures." <> camel(name)
    flags = d |> Map.get("translate", "") |> OptionParser.split()
    {out, err, status} = translate(src, ns, flags)

    verdict =
      case Map.get(d, "expect", "ok") do
        "ok" -> check_ok(name, d, out, err, status, scratch, regen?)
        "error " <> sub -> check_error(sub, err, status)
        other -> {:fail, "bad directive `# expect: #{other}`"}
      end

    case verdict do
      :ok ->
        IO.puts("PASS #{name}")
        :pass
      {:fail, why} ->
        IO.puts("FAIL #{name}: #{why}")
        :fail
    end
  end

  defp check_ok(name, d, out, err, status, scratch, regen?) do
    exp_path = Path.join(@expected, name <> ".lean")
    warn = Map.get(d, "warn")
    cond do
      status != 0 ->
        {:fail, "translator exited #{status}\n#{indent(err)}"}
      regen? ->
        File.write!(exp_path, out)
        IO.puts("     wrote #{Path.relative_to(exp_path, @root)}")
        lean_check(d, name, out, scratch)
      not File.exists?(exp_path) ->
        {:fail, "no expected file #{exp_path} (run with --regen to create it)"}
      File.read!(exp_path) != out ->
        actual = Path.join(scratch, name <> ".actual.lean")
        File.write!(actual, out)
        {diff, _} = System.cmd("diff", ["-u", exp_path, actual], stderr_to_stdout: true)
        {:fail, "output differs from expected\n#{indent(diff)}"}
      warn != nil and not String.contains?(err, warn) ->
        {:fail, "expected a warning containing `#{warn}`, stderr was:\n#{indent(err)}"}
      true ->
        lean_check(d, name, out, scratch)
    end
  end

  defp check_error(sub, err, status) do
    cond do
      status == 0 -> {:fail, "expected a translation error containing `#{sub}` but translation succeeded"}
      not String.contains?(err, sub) -> {:fail, "expected an error containing `#{sub}`, stderr was:\n#{indent(err)}"}
      true -> :ok
    end
  end

  # `# lean: check`: the expected content must compile against the built
  # library, with no errors and no warnings (the same bar as check.sh).
  defp lean_check(d, name, content, scratch) do
    if Map.get(d, "lean") == "check" do
      file = Path.join(scratch, name <> ".lean")
      File.write!(file, content)
      {out, status} = System.cmd("lake", ["env", "lean", file], cd: @root, stderr_to_stdout: true)
      noisy = out |> String.split("\n") |> Enum.filter(&(&1 =~ ~r/(^|:\d+:\d+: )(error|warning)/))
      cond do
        status != 0 -> {:fail, "lean exited #{status}\n#{indent(out)}"}
        noisy != [] -> {:fail, "lean reported\n#{indent(Enum.join(noisy, "\n"))}"}
        true -> :ok
      end
    else
      :ok
    end
  end

  # Run the translator with stdout and stderr captured separately (a port
  # only captures stdout, so stderr goes through a temp file).
  defp translate(src, ns, flags) do
    errfile = Path.join(System.tmp_dir!(), "leanactors-fixture-stderr-#{:erlang.unique_integer([:positive])}")
    cmd = Enum.map_join(["elixir", @translator, src, ns | flags], " ", &shell_quote/1) <> " 2>" <> shell_quote(errfile)
    {out, status} = System.cmd("sh", ["-c", cmd])
    err = File.read!(errfile)
    File.rm(errfile)
    {out, err, status}
  end

  defp shell_quote(s), do: "'" <> String.replace(s, "'", "'\\''") <> "'"

  # the leading comment block as a map of directive -> value
  defp directives(src) do
    src
    |> File.stream!()
    |> Enum.take_while(&String.starts_with?(&1, "#"))
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/^#\s*(translate|expect|warn|lean):\s*(.*?)\s*$/, line) do
        [_, k, v] -> [{k, v}]
        nil -> []
      end
    end)
    |> Map.new()
  end

  defp camel(name), do: name |> String.split("_") |> Enum.map_join(&String.capitalize/1)

  defp indent(s), do: s |> String.trim_trailing() |> String.split("\n") |> Enum.map_join("\n", &("    " <> &1))

  # the modules generated files import must be built before `lake env lean`
  # can check a fixture (a no-op when check.sh or lake build already ran)
  defp build_library do
    {out, status} = System.cmd("lake", ["build", "Leanactors.Sys"], cd: @root, stderr_to_stdout: true)
    if status != 0, do: die("lake build Leanactors.Sys failed\n#{indent(out)}")
  end

  defp ensure_lake_on_path do
    if System.find_executable("lake") == nil do
      elan = Path.join(System.user_home!(), ".elan/bin")
      System.put_env("PATH", elan <> ":" <> System.get_env("PATH", ""))
      System.find_executable("lake") || die("lake not found; install elan or put lake on PATH")
    end
  end

  defp die(msg) do
    IO.puts(:stderr, "run_fixtures: " <> msg)
    System.halt(1)
  end
end

Fixtures.main(System.argv())
