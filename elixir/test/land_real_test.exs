# Self-test for elixir/land_real.exs and elixir/real_provenance.exs.
#
#   elixir elixir/test/land_real_test.exs [-v]
#
# Landing a module writes into six places at once (elixir/real/, Gen/,
# Examples/, check.sh, Leanactors.lean, MANIFEST.json), so the test runs the
# real script against a SCRATCH root under the system temp directory -- a
# skeleton repository with the repo's own check.sh, Leanactors.lean and
# translator copied in, an empty elixir/real/, and a scratch "upstream
# project" to land out of. Nothing in this repository is touched (the last
# case checks that), and the scratch directory is removed at the end.
#
# What it pins:
#
#   * the copy is byte-identical to the origin, and the Lean generated from
#     the copy is the committed Leanactors/Gen/TableRegistry.lean, modulo the
#     namespace (the scratch module is landed under --name DemoRegistry so
#     that every wiring step is a fresh insertion rather than a no-op)
#   * check.sh gains exactly the translate and diff lines, Leanactors.lean
#     exactly the two imports, MANIFEST.json exactly one entry
#   * the skeleton example has a hand `beh`, `beh_eq_gen`, and the TODO
#     markers a human has to answer
#   * a second run changes NOTHING (idempotence), file by file
#   * real_provenance.exs fails on an edited copy and on an unrecorded file,
#     and reports (but does not fail on) an origin that moved on upstream
#   * land_real.exs refuses to overwrite a copy that differs from the origin,
#     printing both md5s, and --update lands it deliberately
defmodule LandRealTest do
  @root Path.expand("../..", __DIR__)

  def main(argv) do
    verbose? = "-v" in argv
    scratch = Path.join(System.tmp_dir!(), "leanactors-land-real-#{:erlang.unique_integer([:positive])}")
    before = repo_snapshot()

    try do
      setup(scratch)
      run_cases(scratch, verbose?)
    after
      File.rm_rf!(scratch)
    end

    check("the repository itself is untouched", repo_snapshot() == before)
    report()
  end

  # --- the scratch repository ---------------------------------------------

  defp setup(scratch) do
    for d <- ["elixir/real", "Leanactors/Gen", "Leanactors/Examples", "loom/lib/loom/teams"],
        do: File.mkdir_p!(Path.join(scratch, d))

    File.cp!(Path.join(@root, "check.sh"), Path.join(scratch, "check.sh"))
    File.cp!(Path.join(@root, "Leanactors.lean"), Path.join(scratch, "Leanactors.lean"))
    File.cp!(Path.join(@root, "elixir/to_lean.exs"), Path.join(scratch, "elixir/to_lean.exs"))
    File.cp!(Path.join(@root, "elixir/real/table_registry.ex"), origin(scratch))
  end

  defp origin(scratch), do: Path.join(scratch, "loom/lib/loom/teams/table_registry.ex")

  defp run_cases(scratch, verbose?) do
    {out, status} = land(scratch, ["--name", "DemoRegistry", "--no-lean"])
    if verbose?, do: IO.puts(out)
    check("land_real exits 0", status == 0, out)

    # 1. the verbatim copy
    copy = Path.join(scratch, "elixir/real/demo_registry.ex")
    check("the copy exists", File.exists?(copy))
    check("the copy is byte-identical to the origin", File.read!(copy) == File.read!(origin(scratch)))

    # 2. the generated Lean is the committed one, namespace aside
    gen = Path.join(scratch, "Leanactors/Gen/DemoRegistry.lean")
    check("the Gen file exists", File.exists?(gen))

    if File.exists?(gen) do
      renamed = String.replace(File.read!(gen), "Leanactors.Gen.DemoRegistry", "Leanactors.Gen.TableRegistry")
      committed = File.read!(Path.join(@root, "Leanactors/Gen/TableRegistry.lean"))
      check("the generated Lean matches the committed Gen/TableRegistry.lean", renamed == committed)
    end

    # 3. check.sh gained exactly the two lines
    added = lines_added(Path.join(@root, "check.sh"), Path.join(scratch, "check.sh"))

    check(
      "check.sh gained the translate and diff lines only",
      added == [
        "elixir elixir/to_lean.exs elixir/real/demo_registry.ex Leanactors.Gen.DemoRegistry > $OUT/Gen.DemoRegistry.lean",
        "diff -q $OUT/Gen.DemoRegistry.lean Leanactors/Gen/DemoRegistry.lean"
      ],
      inspect(added)
    )

    # 4. the example skeleton
    ex = Path.join(scratch, "Leanactors/Examples/DemoRegistry.lean")
    check("the example skeleton exists", File.exists?(ex))

    if File.exists?(ex) do
      src = File.read!(ex)

      for marker <- [
            "def beh : EBehavior St Msg",
            "theorem beh_eq_gen : Gen.DemoRegistry.beh = beh",
            "export Leanactors.Gen.DemoRegistry (",
            "TODO(human)",
            "-- def init : Sys St Msg :=",
            "-- #eval exploreWith beh sig check envMsgs init 8 4"
          ],
          do: check("the skeleton has `#{marker}`", String.contains?(src, marker))

      check(
        "the skeleton restates every generated clause",
        clause_count(File.read!(gen)) == clause_count(src),
        "gen #{clause_count(File.read!(gen))}, example #{clause_count(src)}"
      )
    end

    # 5. Leanactors.lean gained exactly the two imports
    imports = lines_added(Path.join(@root, "Leanactors.lean"), Path.join(scratch, "Leanactors.lean"))

    check(
      "Leanactors.lean gained the two imports only",
      imports == ["import Leanactors.Gen.DemoRegistry", "import Leanactors.Examples.DemoRegistry"],
      inspect(imports)
    )

    # 6. the manifest entry
    entry = manifest_entry(scratch, "DemoRegistry")

    check("MANIFEST.json records the module", entry != nil)

    if entry do
      check("  its origin is the scratch upstream file", entry["origin"] == origin(scratch), entry["origin"])
      check("  its md5 is the file's", entry["md5"] == md5(copy), entry["md5"])
      check("  its project is `loom`", entry["project"] == "loom", entry["project"])
      check("  its origin_rel is the path inside that project",
        entry["origin_rel"] == "lib/loom/teams/table_registry.ex", entry["origin_rel"])
      check("  its Elixir module is the source's", entry["module"] == "Loom.Teams.TableRegistry", entry["module"])
    end

    # 7. provenance passes
    {out, status} = provenance(scratch, [])
    check("real_provenance passes on the fresh landing", status == 0, out)
    check("  and says the copy matches the origin", out =~ "byte-identical to its origin", out)

    # 8. idempotence, file by file
    snapshot = tree(scratch)
    {out2, status2} = land(scratch, ["--name", "DemoRegistry", "--no-lean"])
    check("a second landing exits 0", status2 == 0, out2)
    check("a second landing changes nothing", tree(scratch) == snapshot, diff_of(snapshot, tree(scratch)))
    check("  and says so", out2 =~ "already landed, byte-identical", out2)

    # 9. an edited copy is caught
    File.write!(copy, File.read!(copy) <> "\n# edited\n")
    {out, status} = provenance(scratch, [])
    check("an edited copy fails provenance", status == 1, out)
    check("  and the message says the copy was edited", out =~ "the copy was edited", out)
    File.write!(copy, File.read!(origin(scratch)))

    # 10. an unrecorded file under elixir/real/ is caught
    ghost = Path.join(scratch, "elixir/real/ghost.ex")
    File.write!(ghost, "defmodule Ghost do\nend\n")
    {out, status} = provenance(scratch, [])
    check("an unrecorded file fails provenance", status == 1, out)
    check("  and the message names it", out =~ "no MANIFEST.json entry", out)
    File.rm!(ghost)

    # 11. a changed origin is refused, with both md5s
    was = File.read!(origin(scratch))
    File.write!(origin(scratch), was <> "\n# upstream moved on\n")
    {out, status} = land(scratch, ["--name", "DemoRegistry", "--no-lean"])
    check("landing a changed origin over a copy is refused", status == 1, out)
    check("  and prints both md5s", out =~ md5(copy) and out =~ RealMd5.of_string(was <> "\n# upstream moved on\n"), out)
    check("  and leaves the copy alone", File.read!(copy) == was)

    # 12. --update lands it deliberately
    {out, status} = land(scratch, ["--name", "DemoRegistry", "--no-lean", "--update"])
    check("--update lands the changed origin", status == 0, out)
    check("  and the copy is the new origin", File.read!(copy) == File.read!(origin(scratch)))
    {_, status} = provenance(scratch, [])
    check("  and provenance passes again", status == 0)

    # 13. an origin that moves on after landing is reported, not failed
    File.write!(origin(scratch), was)
    {out, status} = provenance(scratch, [])
    check("an origin that moved on does not fail provenance", status == 0, out)
    check("  but is reported", out =~ "ORIGIN MOVED", out)
    {_, status} = provenance(scratch, ["--strict-origin"])
    check("  and --strict-origin does fail on it", status == 1)
  end

  # --- running the scripts -------------------------------------------------

  defp land(scratch, args) do
    System.cmd("elixir", [Path.join(@root, "elixir/land_real.exs"), origin(scratch), "--root", scratch | args],
      cd: @root,
      stderr_to_stdout: true
    )
  end

  defp provenance(scratch, args) do
    System.cmd("elixir", [Path.join(@root, "elixir/real_provenance.exs"), "--root", scratch | args],
      cd: @root,
      stderr_to_stdout: true
    )
  end

  # --- little helpers ------------------------------------------------------

  defp manifest_entry(scratch, name) do
    path = Path.join(scratch, "elixir/real/MANIFEST.json")

    if File.exists?(path) and Code.ensure_loaded?(:json) do
      case :json.decode(File.read!(path)) do
        %{"modules" => mods} -> Enum.find(mods, &(&1["name"] == name))
        _ -> nil
      end
    end
  end

  defp lines_added(old_path, new_path) do
    old = old_path |> File.read!() |> String.split("\n")
    new = new_path |> File.read!() |> String.split("\n")
    new -- old
  end

  # the clauses of a `def beh`: the `| ..` lines that follow it
  defp clause_count(src) do
    lines = String.split(src, "\n")

    case Enum.find_index(lines, &(&1 == "def beh : EBehavior St Msg")) do
      nil -> -1
      i -> lines |> Enum.drop(i + 1) |> Enum.take_while(&String.starts_with?(&1, "  ")) |> Enum.count(&String.starts_with?(&1, "  |"))
    end
  end

  defp tree(dir) do
    dir
    |> Path.join("**/*")
    |> Path.wildcard()
    |> Enum.reject(&File.dir?/1)
    |> Map.new(&{Path.relative_to(&1, dir), md5(&1)})
  end

  defp diff_of(a, b) do
    keys = (Map.keys(a) ++ Map.keys(b)) |> Enum.uniq() |> Enum.sort()
    keys |> Enum.filter(&(Map.get(a, &1) != Map.get(b, &1))) |> inspect()
  end

  defp repo_snapshot do
    for f <- ["check.sh", "Leanactors.lean", "elixir/real/MANIFEST.json"],
        p = Path.join(@root, f),
        File.exists?(p),
        into: %{},
        do: {f, md5(p)}
  end

  defp md5(path), do: RealMd5.of_string(File.read!(path))

  # --- the tally -----------------------------------------------------------

  defp check(what, ok?, detail \\ nil) do
    if ok? do
      IO.puts("PASS #{what}")
    else
      IO.puts("FAIL #{what}" <> if(detail in [nil, ""], do: "", else: "\n" <> indent(to_string(detail))))
      Process.put(:failed, (Process.get(:failed) || 0) + 1)
    end
  end

  defp indent(s), do: s |> String.trim_trailing() |> String.split("\n") |> Enum.map_join("\n", &("    " <> &1))

  defp report do
    failed = Process.get(:failed) || 0

    if failed == 0 do
      IO.puts("land_real self-test: all checks passed")
    else
      IO.puts("land_real self-test: #{failed} check(s) FAILED")
      System.halt(1)
    end
  end
end

defmodule RealMd5 do
  def of_string(s), do: :crypto.hash(:md5, s) |> Base.encode16(case: :lower)
end

LandRealTest.main(System.argv())
