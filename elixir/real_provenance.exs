# Provenance of the real modules: is everything under elixir/real/ still a
# byte-for-byte copy of the file it was taken from?
#
#   elixir elixir/real_provenance.exs [--root DIR] [--strict-origin] [--quiet]
#
# "We translate real, unmodified code" is the strongest claim this repository
# makes, and it is the easiest one to break by accident: one edit to a file
# under elixir/real/ to get it through the translator and the claim is false
# while every test still passes. This script turns it into a checked claim.
# check.sh runs it before it translates anything.
#
# For every file under elixir/real/ (the manifest is elixir/real/MANIFEST.json,
# written by elixir/land_real.exs):
#
#   * it must have a manifest entry               -- else: an unrecorded copy
#   * its md5 must equal the recorded one         -- else: the copy was edited
#   * check.sh must translate it                  -- else: it is not being checked
#   * its generated Leanactors/Gen/<Name>.lean must exist
#   * if the origin path exists on this machine, the two files must be
#     byte-identical
#
# The origin lives in another project that this repository does not control,
# so an origin that has MOVED ON since landing (the copy is still exactly what
# was landed, but upstream has changed) is reported and does not fail the
# script -- `--strict-origin` makes it fail. An origin that is not on this
# machine at all is reported and skipped, like the readiness gate's project
# paths. An edited *copy* always fails: that one is ours.
Code.require_file("real_manifest.exs", __DIR__)

defmodule RealProvenance do
  def main(argv) do
    {opts, _rest} =
      OptionParser.parse!(argv, strict: [root: :string, strict_origin: :boolean, quiet: :boolean])

    root = Path.expand(opts[:root] || RealManifest.default_root())
    strict_origin? = opts[:strict_origin] || false
    quiet? = opts[:quiet] || false

    manifest =
      try do
        RealManifest.read(root)
      rescue
        e -> die(Exception.message(e))
      end

    files = RealManifest.real_files(root)
    entries = RealManifest.entries(manifest)
    check_sh = read_check_sh(root)

    if files == [] and entries == [] do
      say(quiet?, "   no real modules landed yet (elixir/real/ is empty)")
      System.halt(0)
    end

    unrecorded =
      for f <- files, RealManifest.entry_for_file(manifest, f) == nil, do: {f, "no MANIFEST.json entry"}

    results = Enum.map(entries, &check_entry(&1, root, check_sh))
    failures = unrecorded ++ for({:fail, f, why} <- results, do: {f, why})
    drifted = for {:drift, f, why} <- results, do: {f, why}
    absent = for {:absent, f, _} <- results, do: f
    ok = for {:ok, f, _} <- results, do: f

    for {f, why} <- Enum.sort(failures), do: IO.puts("   FAIL #{f}: #{why}")
    for {f, why} <- Enum.sort(drifted), do: IO.puts("   ORIGIN MOVED #{f}: #{why}")

    unless quiet? do
      for f <- Enum.sort(ok), do: IO.puts("   ok #{f} (byte-identical to its origin)")
      for f <- Enum.sort(absent), do: IO.puts("   ok #{f} (md5 as landed; origin not on this machine)")
    end

    IO.puts(
      "   #{length(entries)} real module(s): #{length(ok)} verified against the origin, " <>
        "#{length(absent)} origin not present, #{length(drifted)} origin moved on, #{length(failures)} failed"
    )

    cond do
      failures != [] ->
        IO.puts(:stderr, "real_provenance: elixir/real/ no longer matches its origins.")
        IO.puts(:stderr, "  A file under elixir/real/ must stay byte-identical to the file it was copied from;")
        IO.puts(:stderr, "  land a changed upstream deliberately with: elixir elixir/land_real.exs <origin> --update")
        System.halt(1)

      drifted != [] and strict_origin? ->
        IO.puts(:stderr, "real_provenance: --strict-origin and an origin has moved on since landing.")
        System.halt(1)

      true ->
        :ok
    end
  end

  defp check_entry(entry, root, check_sh) do
    file = entry["file"]
    path = Path.join(root, file)

    cond do
      not File.exists?(path) ->
        {:fail, file, "listed in MANIFEST.json but not in the tree"}

      (got = RealManifest.md5(path)) != entry["md5"] ->
        {:fail, file, "md5 #{got}, MANIFEST.json records #{entry["md5"]} -- the copy was edited"}

      not translated_by_check_sh?(check_sh, file) ->
        {:fail, file, "check.sh does not translate it (no `elixir/to_lean.exs #{file}` line)"}

      entry["gen"] != nil and not File.exists?(Path.join(root, entry["gen"])) ->
        {:fail, file, "generated #{entry["gen"]} is missing"}

      true ->
        origin = entry["origin"]

        cond do
          origin == nil or not File.exists?(origin) ->
            {:absent, file, origin}

          RealManifest.md5(origin) == entry["md5"] ->
            {:ok, file, origin}

          true ->
            {:drift, file,
             "#{origin} is now md5 #{RealManifest.md5(origin)}; the copy is still the one landed (#{entry["md5"]})"}
        end
    end
  end

  # check.sh is a shell script, not data: the test is deliberately dumb -- a
  # translate line naming this file, which is how every landed module is
  # regenerated and diffed against its committed Gen file.
  defp translated_by_check_sh?(nil, _file), do: true

  defp translated_by_check_sh?(check_sh, file) do
    check_sh
    |> String.split("\n")
    |> Enum.any?(&(String.contains?(&1, "to_lean.exs") and String.contains?(&1, file)))
  end

  defp read_check_sh(root) do
    path = Path.join(root, "check.sh")
    if File.exists?(path), do: File.read!(path)
  end

  defp say(true, _msg), do: :ok
  defp say(false, msg), do: IO.puts(msg)

  defp die(msg) do
    IO.puts(:stderr, "real_provenance: " <> msg)
    System.halt(1)
  end
end

RealProvenance.main(System.argv())
