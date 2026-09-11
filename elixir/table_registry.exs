# Elixir twin of Leanactors/Examples/TableRegistry.lean, running the real
# module `elixir/real/table_registry.ex` (copied verbatim from
# loom/lib/loom/teams/table_registry.ex) on the BEAM, with real ETS tables.
# Run: elixir elixir/table_registry.exs
#
# Lean proves two properties of the registry's *map*: a team maps to at
# most one reference, and distinct teams hold distinct references. ETS
# itself is abstracted away in the model (`:ets.new` is a fresh opaque
# `Term`, `:ets.delete` and its try/rescue are no-ops), so the point of
# this driver is the other direction: the real ETS calls run, and the map
# the real module keeps satisfies what Lean proved.

Code.require_file("real/table_registry.ex", __DIR__)

{:ok, reg} = Loom.Teams.TableRegistry.start_link()

teams = [:t1, :t2, :t3]

# create: every team gets its own table
refs = for t <- teams, do: (fn -> {:ok, r} = Loom.Teams.TableRegistry.create_table(t); r end).()
3 = length(Enum.uniq(refs))
true = Enum.all?(refs, &is_reference/1)

# the map Lean reasons about: one reference per team, all distinct
%{tables: tables} = :sys.get_state(reg)
3 = map_size(tables)
^refs = Enum.map(teams, &Map.fetch!(tables, &1))
3 = length(Enum.uniq(Map.values(tables)))

# the tables are real and independent
for {t, r} <- Enum.zip(teams, refs), do: :ets.insert(r, {:who, t})
for {t, r} <- Enum.zip(teams, refs), do: [{:who, ^t}] = :ets.lookup(r, :who)

# get
{:ok, first} = Loom.Teams.TableRegistry.get_table(:t1)
^first = hd(refs)
:error = Loom.Teams.TableRegistry.get_table(:nope)

# re-creating a team replaces its reference (Map.put), and the new one is
# fresh: this is `create` inserting `Term.mk ets` in Lean
{:ok, again} = Loom.Teams.TableRegistry.create_table(:t1)
true = again != first
%{tables: tables2} = :sys.get_state(reg)
^again = Map.fetch!(tables2, :t1)
3 = length(Enum.uniq(Map.values(tables2)))

# delete: the entry goes, the ETS table is destroyed, and deleting again
# is still :ok (the {nil, _} arm)
:ok = Loom.Teams.TableRegistry.delete_table(:t2)
:error = Loom.Teams.TableRegistry.get_table(:t2)
:ok = Loom.Teams.TableRegistry.delete_table(:t2)
%{tables: tables3} = :sys.get_state(reg)
2 = map_size(tables3)
false = Map.has_key?(tables3, :t2)

# the try/rescue the model drops: deleting a table whose reference is
# already gone raises ArgumentError inside the callback and is rescued, so
# the registry survives
{:ok, doomed} = Loom.Teams.TableRegistry.create_table(:t4)
:ets.delete(doomed)
:ok = Loom.Teams.TableRegistry.delete_table(:t4)
true = Process.alive?(reg)

# get_table! raises for an unknown team (a public wrapper the translator
# ignores; `raise` there is not a callback)
try do
  Loom.Teams.TableRegistry.get_table!(:nope)
  raise "expected ArgumentError"
rescue
  ArgumentError -> :ok
end

%{tables: final} = :sys.get_state(reg)
2 = map_size(final)
2 = length(Enum.uniq(Map.values(final)))

IO.puts("registry alive = #{Process.alive?(reg)}, teams = #{inspect(Map.keys(final))}")
IO.puts("TABLE REGISTRY OK: one table per team, references distinct, delete idempotent, rescue survives")
