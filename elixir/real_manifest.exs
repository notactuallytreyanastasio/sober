# The manifest of real, unmodified modules: elixir/real/MANIFEST.json.
#
# This file defines a module and runs nothing. It is loaded with
# `Code.require_file/2` by the three scripts that share it:
#
#   elixir/land_real.exs        writes an entry when a real module is landed
#   elixir/real_provenance.exs  checks every landed file against its entry
#   elixir/readiness.exs        renders the "Landed" section of docs/readiness.md
#
# One entry per file under `elixir/real/`:
#
#   {"name":       "TableRegistry",            the Lean name: Gen/<name>.lean
#    "module":     "Loom.Teams.TableRegistry", the Elixir module
#    "project":    "loom",                     the project it was copied out of
#    "origin":     "/abs/path/.../table_registry.ex",   where it was copied FROM
#    "origin_rel": "lib/loom/teams/table_registry.ex",  the same, inside that project
#    "file":       "elixir/real/table_registry.ex",     the copy in this repo
#    "md5":        "...",   of both, at landing time; they were byte-identical
#    "bytes":      2683, "lines": 92,
#    "namespace":  "Leanactors.Gen.TableRegistry",
#    "flags":      [],      extra translator arguments (--pid, --pubsub)
#    "gen":        "Leanactors/Gen/TableRegistry.lean",
#    "example":    "Leanactors/Examples/TableRegistry.lean"}
#
# The origin path is absolute and therefore machine-specific, exactly like the
# project paths in `docs/readiness-baseline.json`: a checkout without those
# projects can still verify the copies against the recorded md5, and skips the
# comparison against the origin itself.
defmodule RealManifest do
  @doc "The repository root this script lives in (scripts may override it)."
  def default_root, do: Path.expand("..", __DIR__)

  def manifest_path(root), do: Path.join(root, "elixir/real/MANIFEST.json")
  def real_dir(root), do: Path.join(root, "elixir/real")

  @doc "Every `.ex` file under elixir/real/, repo-relative, sorted."
  def real_files(root) do
    root
    |> real_dir()
    |> Path.join("*.ex")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.map(&Path.relative_to(&1, root))
  end

  @doc """
  The manifest as `%{"note" => .., "modules" => [entry]}`. A missing file is
  the empty manifest; an unreadable one raises, because silently landing on
  top of a broken manifest would lose entries.
  """
  def read(root) do
    path = manifest_path(root)

    cond do
      not File.exists?(path) ->
        %{"note" => note(), "modules" => []}

      not Code.ensure_loaded?(:json) ->
        raise "reading #{path} needs OTP 27 or later (the :json module)"

      true ->
        case :json.decode(File.read!(path)) do
          %{"modules" => mods} = m when is_list(mods) -> m
          _ -> raise "#{path} is not a manifest (no \"modules\" list)"
        end
    end
  end

  def entries(manifest), do: Map.get(manifest, "modules", [])

  @doc "The entry for a repo-relative file under elixir/real/, or nil."
  def entry_for_file(manifest, file), do: Enum.find(entries(manifest), &(&1["file"] == file))

  def entry_named(manifest, name), do: Enum.find(entries(manifest), &(&1["name"] == name))

  @doc "Replace (or add) one entry, keeping the list sorted by Lean name."
  def put_entry(manifest, entry) do
    kept = Enum.reject(entries(manifest), &(&1["name"] == entry["name"]))
    Map.merge(manifest, %{"note" => note(), "modules" => Enum.sort_by([entry | kept], & &1["name"])})
  end

  def write!(root, manifest) do
    File.write!(manifest_path(root), encode(manifest))
  end

  def encode(manifest), do: enc(manifest, "") <> "\n"

  def note do
    "Real modules copied verbatim out of other projects. One entry per file under " <>
      "elixir/real/, written by elixir/land_real.exs and checked by elixir/real_provenance.exs " <>
      "(which check.sh runs): the copy must still be byte-identical to the origin it was taken from."
  end

  @doc "Lowercase hex md5 of a file's bytes."
  def md5(path), do: path |> File.read!() |> md5_bin()

  def md5_bin(bytes), do: :crypto.hash(:md5, bytes) |> Base.encode16(case: :lower)

  @doc """
  Split an absolute origin path into `{project, path-inside-the-project}` at
  its last `lib` segment: `/Users/x/code/loom/lib/loom/teams/t.ex` is
  `{"loom", "lib/loom/teams/t.ex"}`. A path with no `lib` segment keeps its
  parent directory's name and its basename.
  """
  def split_origin(origin) do
    segs = origin |> Path.expand() |> Path.split()

    case Enum.find_index(Enum.reverse(segs), &(&1 == "lib")) do
      nil ->
        {Path.basename(Path.dirname(origin)), Path.basename(origin)}

      back ->
        i = length(segs) - 1 - back
        project = if i > 0, do: Enum.at(segs, i - 1), else: ""
        {project, Enum.join(Enum.drop(segs, i), "/")}
    end
  end

  @doc """
  What a landed module has in Lean, read off the files themselves rather than
  recorded: the example, whether it proves `beh_eq_gen`, whether it runs a
  bounded checker (`#eval` of an explorer), and the proof file if there is
  one. This is what the "Landed" section of docs/readiness.md reports, so the
  README's claims about landed modules are generated, not written by hand.
  """
  def status(root, entry) do
    name = entry["name"]
    ex_rel = entry["example"] || "Leanactors/Examples/#{name}.lean"
    ex_path = Path.join(root, ex_rel)
    proof_rel = "Leanactors/Examples/#{name}Proof.lean"
    src = if File.exists?(ex_path), do: File.read!(ex_path), else: ""

    checker? =
      src
      |> String.split("\n")
      |> Enum.any?(&(String.starts_with?(&1, "#eval") and String.contains?(&1, "explore")))

    %{
      example: if(File.exists?(ex_path), do: ex_rel),
      beh_eq_gen: String.contains?(src, "theorem beh_eq_gen"),
      checker: checker?,
      proof: if(File.exists?(Path.join(root, proof_rel)), do: proof_rel),
      gen: entry["gen"] || "Leanactors/Gen/#{name}.lean"
    }
  end

  # --- the same tiny JSON printer elixir/readiness.exs writes its baseline
  # with: keys in sorted order so a refresh diffs cleanly, and a map whose
  # values are all scalars on one line.
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
end
