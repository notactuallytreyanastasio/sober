# Land a real module: copy it in verbatim, translate it, and wire it up.
#
#   elixir elixir/land_real.exs PATH/TO/Module.ex [--pid Mod=const ...]
#                                                 [--pubsub Mod ...]
#                                                 [--name LeanName] [--root DIR]
#                                                 [--update] [--force-example]
#                                                 [--no-lean] [--dry-run]
#
# Given a module from a real project that the translator already accepts, this
# does the six mechanical steps that landing one has always needed, and only
# those -- it writes no property and proves nothing:
#
#   1. translate the file AT ITS ORIGINAL PATH, read-only. A translator error
#      here is the answer: the module is not landable yet, nothing is written.
#   2. copy it to elixir/real/<snake_name>.ex and check the copy is
#      byte-identical to the origin (printing both md5s if it is not). An
#      existing copy that differs is refused, not overwritten: --update lands
#      the current origin on top of it deliberately.
#   3. generate Leanactors/Gen/<Name>.lean from the COPY (what check.sh does).
#   4. append the translate and diff lines to check.sh, in its translate
#      section.
#   5. write a SKELETON Leanactors/Examples/<Name>.lean: the generated `beh`
#      restated as a hand-written one, `beh_eq_gen` proved against it, and
#      commented stubs for the initial system and the bounded checker. An
#      existing example is never overwritten (--force-example does).
#   6. add the `Gen` and `Examples` imports to Leanactors.lean, and record the
#      module in elixir/real/MANIFEST.json (origin path + md5), which
#      elixir/real_provenance.exs then checks on every run of check.sh.
#
# What a human still has to do is printed at the end, and it is the part that
# matters: the skeleton's `beh` is a COPY of the generated clauses, which
# makes `beh_eq_gen` true but says nothing. Rewrite it into the behaviour you
# would have written by hand (`beh_eq_gen` is what keeps that honest), then
# fill in `init` and a bounded check of a property that is actually true of
# the module, and write down in the docstring what the model does not cover.
#
# Every step is idempotent: running it twice changes nothing the second time
# (it prints what was already in place), so it is safe to re-run after the
# translator has changed.
#
# --no-lean skips the `lake env lean` check of the skeleton; without it, a
# skeleton that does not compile is reported and its import is NOT added to
# Leanactors.lean, so the tree still builds.
Code.require_file("real_manifest.exs", __DIR__)

defmodule LandReal do
  @doc false
  def main(argv) do
    {opts, rest} =
      OptionParser.parse!(argv,
        strict: [
          pid: :keep,
          pubsub: :keep,
          name: :string,
          root: :string,
          update: :boolean,
          force_example: :boolean,
          lean: :boolean,
          dry_run: :boolean
        ]
      )

    src =
      case rest do
        [one] -> Path.expand(one)
        _ -> die("usage: elixir elixir/land_real.exs PATH/TO/Module.ex [--pid Mod=const] [--name LeanName]")
      end

    unless File.exists?(src), do: die("no such file: #{src}")

    root = Path.expand(opts[:root] || RealManifest.default_root())
    dry? = opts[:dry_run] || false

    flags =
      Enum.flat_map(opts, fn
        {:pid, v} -> ["--pid", v]
        {:pubsub, v} -> ["--pubsub", v]
        _ -> []
      end)

    {module, name} = module_and_name(src, opts[:name])
    snake = Macro.underscore(name)
    ns = "Leanactors.Gen." <> name
    dest_rel = "elixir/real/#{snake}.ex"
    gen_rel = "Leanactors/Gen/#{name}.lean"
    ex_rel = "Leanactors/Examples/#{name}.lean"

    IO.puts("land_real: #{module}  ->  #{name}")
    IO.puts("  origin    #{src}")
    IO.puts("  copy      #{dest_rel}")
    IO.puts("  namespace #{ns}#{if flags == [], do: "", else: " " <> Enum.join(flags, " ")}")
    if dry?, do: IO.puts("  (--dry-run: nothing will be written)")

    manifest = read_manifest(root)
    check_name_free(manifest, name, module, dest_rel)

    # 1. the origin must translate, as it stands.
    gen = translate!(root, src, ns, flags, "the origin")

    # 2. the verbatim copy.
    copy_verbatim(root, src, dest_rel, opts[:update] || false, dry?)

    # 3. the generated Lean, from the copy (byte-identical input, so this is
    #    the same text -- translating it again is the check that it is).
    gen2 =
      if dry? or not File.exists?(Path.join(root, dest_rel)) do
        gen
      else
        translate!(root, Path.join(root, dest_rel), ns, flags, "the copy")
      end

    if gen2 != gen do
      die("translating the copy gave different Lean than translating the origin -- the copy is not verbatim")
    end

    write_step(root, gen_rel, gen, dry?, "generated")

    # 4. check.sh.
    wire_check_sh(root, dest_rel, ns, flags, name, dry?)

    # 5. the example skeleton.
    {example_written?, example_note} =
      write_example(root, gen, name, ex_rel, opts[:force_example] || false, dry?)

    # a skeleton that does not compile must not be imported, or the tree stops
    # building; say so loudly and leave the file for the human to fix.
    compiles? =
      cond do
        dry? -> :skipped
        opts[:lean] == false -> :skipped
        not File.exists?(Path.join(root, ex_rel)) -> :skipped
        true -> lean_check(root, name, ex_rel)
      end

    # 6. Leanactors.lean and the manifest.
    wire_root_module(root, name, ex_rel, compiles?, dry?)
    record(root, manifest, %{
      "name" => name,
      "module" => module,
      "origin" => src,
      "file" => dest_rel,
      "gen" => gen_rel,
      "example" => ex_rel,
      "namespace" => ns,
      "flags" => flags
    }, dry?)

    todo(name, ex_rel, dest_rel, example_written?, example_note, compiles?)
  end

  # --- 1. translation ------------------------------------------------------

  defp translate!(root, file, ns, flags, what) do
    translator = Path.join(root, "elixir/to_lean.exs")
    unless File.exists?(translator), do: die("no translator at #{translator} (wrong --root?)")
    {out, err, status} = run_translator(translator, file, ns, flags)

    if status != 0 do
      IO.puts(:stderr, "\nland_real: the translator refused #{what}:\n" <> indent(err))

      die(
        "#{Path.relative_to(file, root)} is not landable yet. Fix the translator (soundly) or\n" <>
          "  leave the module blocked and record why -- nothing was written."
      )
    end

    warnings = err |> String.trim_trailing() |> String.split("\n", trim: true)
    for w <- warnings, do: IO.puts("  warning (#{what}): #{w}")
    out
  end

  # stdout and stderr separately: a port captures only stdout, so stderr goes
  # through a temp file (the same trick elixir/test/run_fixtures.exs uses).
  defp run_translator(translator, file, ns, flags) do
    errfile = Path.join(System.tmp_dir!(), "land-real-stderr-#{:erlang.unique_integer([:positive])}")
    cmd = Enum.map_join(["elixir", translator, file, ns | flags], " ", &shell_quote/1) <> " 2>" <> shell_quote(errfile)
    {out, status} = System.cmd("sh", ["-c", cmd])
    err = File.read!(errfile)
    File.rm(errfile)
    {out, err, status}
  end

  defp shell_quote(s), do: "'" <> String.replace(s, "'", "'\\''") <> "'"

  # --- 2. the verbatim copy ------------------------------------------------

  defp copy_verbatim(root, src, dest_rel, update?, dry?) do
    dest = Path.join(root, dest_rel)
    origin_md5 = RealManifest.md5(src)

    cond do
      File.exists?(dest) and RealManifest.md5(dest) == origin_md5 ->
        step(dest_rel, "already landed, byte-identical (md5 #{origin_md5})")

      File.exists?(dest) and not update? ->
        IO.puts(:stderr, "\nland_real: #{dest_rel} already exists and is NOT the origin's bytes.")
        IO.puts(:stderr, "    origin #{src}")
        IO.puts(:stderr, "      md5  #{origin_md5}")
        IO.puts(:stderr, "    copy   #{dest_rel}")
        IO.puts(:stderr, "      md5  #{RealManifest.md5(dest)}")
        IO.puts(:stderr, "  Either the copy was edited (it must not be) or the origin has moved on.")
        die("refusing to overwrite; re-run with --update to land the current origin deliberately")

      dry? ->
        step(dest_rel, "would copy (md5 #{origin_md5})")

      true ->
        File.mkdir_p!(Path.dirname(dest))
        File.cp!(src, dest)
        got = RealManifest.md5(dest)

        if got != origin_md5 do
          File.rm(dest)
          die("the copy is not byte-identical: origin #{origin_md5}, copy #{got}")
        end

        step(dest_rel, (if update?, do: "re-landed", else: "copied") <> " verbatim (md5 #{got})")
    end
  end

  # --- 3/5/6. writing files ------------------------------------------------

  defp write_step(root, rel, content, dry?, what) do
    path = Path.join(root, rel)
    old = if File.exists?(path), do: File.read!(path)

    cond do
      old == content -> step(rel, "#{what}, unchanged")
      dry? and old == nil -> step(rel, "would write (#{what})")
      dry? -> step(rel, "would rewrite (#{what} changed)")
      true ->
        File.mkdir_p!(Path.dirname(path))
        File.write!(path, content)
        step(rel, if(old == nil, do: "written (#{what})", else: "rewritten (#{what} changed)"))
    end
  end

  # --- 4. check.sh ---------------------------------------------------------

  defp wire_check_sh(root, dest_rel, ns, flags, name, dry?) do
    path = Path.join(root, "check.sh")
    unless File.exists?(path), do: die("no check.sh at #{path} (wrong --root?)")
    src = File.read!(path)
    lines = String.split(src, "\n")

    out = "$OUT/Gen.#{name}.lean"
    tr_line =
      Enum.join(["elixir elixir/to_lean.exs", dest_rel, ns] ++ flags, " ") <> " > " <> out

    diff_line = "diff -q #{out} Leanactors/Gen/#{name}.lean"

    has_tr? = Enum.any?(lines, &(String.contains?(&1, "to_lean.exs") and String.contains?(&1, dest_rel)))
    has_diff? = Enum.any?(lines, &(&1 == diff_line))

    cond do
      has_tr? and has_diff? ->
        step("check.sh", "already translates and diffs #{name}")

      dry? ->
        step("check.sh", "would add the translate and diff lines for #{name}")

      true ->
        lines =
          if has_tr?, do: lines, else: insert_after(lines, tr_line, &(String.starts_with?(&1, "elixir elixir/to_lean.exs")))

        lines =
          if has_diff?, do: lines, else: insert_after(lines, diff_line, &String.starts_with?(&1, "diff -q $OUT/Gen."))

        File.write!(path, Enum.join(lines, "\n"))
        step("check.sh", "translate and diff lines added for #{name}")
    end
  end

  # after the LAST line the predicate accepts, so the landed modules stay
  # together at the end of the block they belong to.
  defp insert_after(lines, new, pred) do
    case lines |> Enum.with_index() |> Enum.filter(fn {l, _} -> pred.(l) end) |> List.last() do
      nil -> die("check.sh has no line to anchor `#{new}` to; add it by hand")
      {_, i} -> List.insert_at(lines, i + 1, new)
    end
  end

  # --- 5. the example skeleton --------------------------------------------

  defp write_example(root, gen, name, ex_rel, force?, dry?) do
    path = Path.join(root, ex_rel)
    content = skeleton(gen, name)

    cond do
      File.exists?(path) and not force? ->
        step(ex_rel, "exists, left alone (--force-example overwrites)")
        {false, :kept}

      dry? ->
        step(ex_rel, "would write the skeleton")
        {true, :skeleton}

      true ->
        File.mkdir_p!(Path.dirname(path))
        File.write!(path, content)
        step(ex_rel, if(force?, do: "skeleton written (overwrote)", else: "skeleton written"))
        {true, :skeleton}
    end
  end

  @doc """
  The skeleton example. Its `beh` is the generated one's clauses COPIED, so
  `beh_eq_gen` holds the moment it is written and the human's job is to
  rewrite those clauses into a readable hand model without breaking it. The
  initial system and the bounded checker are commented stubs: what the right
  initial state and the true property are is exactly what a script cannot know.
  """
  def skeleton(gen, name) do
    exports = top_level_names(gen) -- ["beh"]
    ctors = state_constructors(gen)

    ctor_comment =
      case ctors do
        [] -> ["--   (no St constructor found -- read Leanactors/Gen/#{name}.lean)"]
        cs -> for c <- cs, do: "--   " <> c
      end

    """
    import Leanactors.Explore
    import Leanactors.SysProps
    import Leanactors.Gen.#{name}
    /-!
    # Leanactors.Examples.#{name}

    SKELETON, written by `elixir/land_real.exs`. `#{name}` is a real module
    copied verbatim into `elixir/real/` (its origin is recorded in
    `elixir/real/MANIFEST.json` and checked by `elixir/real_provenance.exs`)
    and translated by `elixir/to_lean.exs` with no edits.

    Three things are still TODO and a script cannot do them:

    1. `beh` below is the *generated* behaviour's clauses, copied. Rewrite it
       as the behaviour you would have written by hand -- the names, the
       grouping and the comments a reader needs -- and let `beh_eq_gen` keep
       the rewrite honest.
    2. `init`: the initial system the property is about.
    3. the property itself, as a bounded check (`Leanactors/Explore.lean`),
       plus a mutant the check catches. A property that is *actually true* of
       this module, not one invented to be easy.

    Say here, too, what the model does NOT cover: every real module abstracts
    something away (ETS contents, time, an external service), and a property
    proved about the abstraction is a property of the abstraction.
    -/

    namespace Leanactors.Examples.#{name}

    open Leanactors Config Sys

    export Leanactors.Gen.#{name} (#{Enum.join(exports, " ")})

    /-- TODO(human): the behaviour, hand-written. These clauses are the
    generated ones, copied verbatim by `land_real.exs` -- rewrite them. -/
    def beh : EBehavior St Msg
    #{String.trim_trailing(beh_clauses(gen, name))}

    /-- The translated Elixir is extensionally the same behaviour. -/
    theorem beh_eq_gen : Gen.#{name}.beh = beh := by
      funext me fresh s m
      cases s <;> cases m <;> first | rfl | simp [Gen.#{name}.beh, beh]

    /-! ## TODO(human): the property, as a bounded check

    The state constructor(s) this module has:

    #{Enum.join(ctor_comment, "\n")}

    Uncomment and fill in:

    -- /-- The system the property is about: the server alone at pid 0, with
    -- callers outside it (a reply to a pid that is not an actor is dropped). -/
    -- def init : Sys St Msg :=
    --   { cfg := ⟨fun p => if p = 0 then some ⟨.<ctor> <initial fields>, []⟩ else none⟩
    --     next := 1, links := [], signals := [] }
    --
    -- /-- The property, as a decidable check on a configuration. -/
    -- def check (s : Sys St Msg) : Bool :=
    --   match s.cfg.stateOf 0 with
    --   | some (.<ctor> ..) => <the property>
    --   | _ => false
    --
    -- /-- The messages the environment may send, per pid. -/
    -- def envMsgs : Pid → List Msg
    --   | 0 => [/- the interesting messages -/]
    --   | _ => []
    --
    -- #eval exploreWith beh sig check envMsgs init 8 4
    --
    -- /-- **Mutant**: a one-clause change that breaks the property; the
    -- checker must find a trace. -/
    -- def behMutant : EBehavior St Msg
    --   | me, fresh, s, msg => beh me fresh s msg
    --
    -- #eval exploreWith behMutant sig check envMsgs init 8 4
    -/

    end Leanactors.Examples.#{name}
    """
  end

  # the clause block of the generated `def beh`, verbatim (its lines are the
  # indented ones that follow the header, comments included).
  defp beh_clauses(gen, name) do
    lines = String.split(gen, "\n")

    case Enum.find_index(lines, &(&1 == "def beh : EBehavior St Msg")) do
      nil -> die("Leanactors/Gen/#{name}.lean has no `def beh : EBehavior St Msg` to copy")
      i ->
        lines
        |> Enum.drop(i + 1)
        |> Enum.take_while(&String.starts_with?(&1, "  "))
        |> Enum.join("\n")
    end
  end

  # every top-level declaration of the generated namespace, so the example can
  # `export` them all: the types, the registered-name constants, `sig`, and
  # any module-local helper the clauses call.
  defp top_level_names(gen) do
    gen
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/^(?:def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z0-9_']*)/, line) do
        [_, n] -> [n]
        nil -> []
      end
    end)
    |> Enum.uniq()
  end

  defp state_constructors(gen) do
    lines = String.split(gen, "\n")

    case Enum.find_index(lines, &(&1 == "inductive St")) do
      nil -> []
      i ->
        lines
        |> Enum.drop(i + 1)
        |> Enum.take_while(&String.starts_with?(&1, "  |"))
        |> Enum.map(&String.trim/1)
    end
  end

  # --- the Lean compile check ---------------------------------------------

  defp lean_check(root, name, ex_rel) do
    if ensure_lake_on_path() do
      targets = ["Leanactors.Explore", "Leanactors.SysProps", "Leanactors.Gen." <> name]
      {out, status} = System.cmd("lake", ["build" | targets], cd: root, stderr_to_stdout: true)

      if status != 0 do
        IO.puts("  lake build #{Enum.join(targets, " ")} failed; skipping the skeleton's compile check\n" <> indent(out))
        :skipped
      else
        {out, status} = System.cmd("lake", ["env", "lean", ex_rel], cd: root, stderr_to_stdout: true)

        noisy = out |> String.split("\n") |> Enum.filter(&(&1 =~ ~r/(^|:\d+:\d+: )(error|warning)/))

        cond do
          status == 0 and noisy == [] ->
            step(ex_rel, "compiles (`lake env lean`), no warnings")
            :ok

          true ->
            IO.puts("  the skeleton does NOT compile yet:")
            IO.puts(indent(if(noisy == [], do: out, else: Enum.join(noisy, "\n"))))
            IO.puts("  (usually `beh_eq_gen`: the copied clauses need a different tactic.)")
            :failed
        end
      end
    else
      IO.puts("  lake not found; skipping the skeleton's compile check (--no-lean silences this)")
      :skipped
    end
  end

  defp ensure_lake_on_path do
    if System.find_executable("lake") == nil do
      elan = Path.join(System.user_home!(), ".elan/bin")
      System.put_env("PATH", elan <> ":" <> System.get_env("PATH", ""))
      System.find_executable("lake") != nil
    else
      true
    end
  end

  # --- 6. Leanactors.lean and the manifest --------------------------------

  defp wire_root_module(root, name, ex_rel, compiles?, dry?) do
    path = Path.join(root, "Leanactors.lean")
    unless File.exists?(path), do: die("no Leanactors.lean at #{path} (wrong --root?)")
    src = File.read!(path)
    lines = src |> String.trim_trailing() |> String.split("\n")

    gen_import = "import Leanactors.Gen.#{name}"
    ex_import = "import Leanactors.Examples.#{name}"

    wanted =
      cond do
        compiles? == :failed ->
          IO.puts("  Leanactors.lean: NOT importing #{ex_rel} while it does not compile")
          [gen_import]

        not File.exists?(Path.join(root, ex_rel)) ->
          [gen_import]

        true ->
          [gen_import, ex_import]
      end

    missing = Enum.reject(wanted, &(&1 in lines))

    cond do
      missing == [] ->
        step("Leanactors.lean", "already imports #{name}")

      dry? ->
        step("Leanactors.lean", "would add " <> Enum.join(missing, ", "))

      true ->
        File.write!(path, Enum.join(lines ++ missing, "\n") <> "\n")
        step("Leanactors.lean", "added " <> Enum.join(missing, ", "))
    end
  end

  defp record(root, manifest, base, dry?) do
    src = base["origin"]
    {project, origin_rel} = RealManifest.split_origin(src)
    bytes = File.read!(src)

    entry =
      Map.merge(base, %{
        "project" => project,
        "origin_rel" => origin_rel,
        "md5" => RealManifest.md5_bin(bytes),
        "bytes" => byte_size(bytes),
        "lines" => length(String.split(bytes, "\n")) - 1
      })

    updated = RealManifest.put_entry(manifest, entry)
    rel = "elixir/real/MANIFEST.json"
    content = RealManifest.encode(updated)
    path = RealManifest.manifest_path(root)
    old = if File.exists?(path), do: File.read!(path)

    cond do
      old == content -> step(rel, "unchanged")
      dry? -> step(rel, "would record #{entry["name"]} (origin #{origin_rel}, md5 #{entry["md5"]})")
      true ->
        File.mkdir_p!(Path.dirname(path))
        File.write!(path, content)
        step(rel, "recorded #{entry["name"]} (origin #{project}/#{origin_rel}, md5 #{entry["md5"]})")
    end
  end

  defp read_manifest(root) do
    try do
      RealManifest.read(root)
    rescue
      e -> die(Exception.message(e))
    end
  end

  # two projects can both have a `Client`; the Lean name is the file name, so
  # the collision has to be resolved by hand with --name.
  defp check_name_free(manifest, name, module, dest_rel) do
    case RealManifest.entry_named(manifest, name) do
      nil ->
        :ok

      %{"module" => ^module} ->
        :ok

      other ->
        die(
          "the Lean name #{name} is already taken by #{other["module"]} (#{other["file"]}).\n" <>
            "  Landing #{module} as #{dest_rel} would collide: pick another with --name."
        )
    end
  end

  # --- module name ---------------------------------------------------------

  defp module_and_name(src, override) do
    module =
      case first_defmodule(File.read!(src)) do
        nil -> die("no `defmodule` in #{src}")
        segs -> Enum.join(segs, ".")
      end

    name = override || List.last(String.split(module, "."))
    unless name =~ ~r/^[A-Z][A-Za-z0-9_]*$/, do: die("#{name} is not a usable Lean module name; pass --name")
    {module, name}
  end

  defp first_defmodule(source) do
    case Code.string_to_quoted(source) do
      {:ok, ast} ->
        {_, found} =
          Macro.prewalk(ast, nil, fn
            {:defmodule, _, [{:__aliases__, _, segs} | _]} = node, nil -> {node, segs}
            node, acc -> {node, acc}
          end)

        found

      {:error, {meta, msg, tok}} ->
        die("cannot parse the source (line #{line_of(meta)}): #{inspect(msg)} #{inspect(tok)}")
    end
  end

  defp line_of(meta) when is_list(meta), do: Keyword.get(meta, :line, 0)
  defp line_of({line, _, _}), do: line
  defp line_of(_), do: 0

  # --- output --------------------------------------------------------------

  defp step(what, said), do: IO.puts("  #{pad(what)} #{said}")

  defp pad(s), do: String.pad_trailing(s, 38)

  defp todo(name, ex_rel, dest_rel, example_written?, example_note, compiles?) do
    IO.puts("")
    IO.puts("Landed. What a human still has to do:")

    if example_note == :kept do
      IO.puts("  * #{ex_rel} already existed and was left alone.")
    end

    if example_written? do
      IO.puts("  * #{ex_rel}: `beh` is the generated clauses COPIED. Rewrite it by hand;")
      IO.puts("    `beh_eq_gen` fails if the rewrite changes the behaviour.")
      IO.puts("  * #{ex_rel}: fill in `init` and a bounded check of a property that is")
      IO.puts("    TRUE of #{name}, plus a mutant the check catches, and say in the docstring")
      IO.puts("    what the model does not cover. THIS IS THE PART THAT MATTERS.")
    end

    if compiles? == :failed do
      IO.puts("  * #{ex_rel} does not compile yet, so Leanactors.lean does not import it.")
      IO.puts("    Fix it, then re-run this script to add the import.")
    end

    IO.puts("  * optional: a BEAM driver elixir/#{Path.basename(dest_rel, ".ex")}.exs, if the module")
    IO.puts("    can be run for real; add it to check.sh's `run on BEAM` section.")
    IO.puts("  * refresh the readiness report (its \"Landed\" section is generated):")
    IO.puts("      elixir elixir/readiness.exs --markdown <project lib paths> > docs/readiness.md")
    IO.puts("  * ./check.sh")
  end

  defp indent(s), do: s |> String.trim_trailing() |> String.split("\n") |> Enum.map_join("\n", &("    " <> &1))

  defp die(msg) do
    IO.puts(:stderr, "land_real: " <> msg)
    System.halt(1)
  end
end

LandReal.main(System.argv())
