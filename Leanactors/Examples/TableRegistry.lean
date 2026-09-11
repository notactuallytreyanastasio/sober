import Leanactors.Explore
import Leanactors.SysProps
import Leanactors.Gen.TableRegistry
/-!
# Leanactors.Examples.TableRegistry

`Loom.Teams.TableRegistry`, copied verbatim into `elixir/real/table_registry.ex`
from a real project and translated by `elixir/to_lean.exs` with no
annotations at all: the module carries no `@type`, so the translator
inferred its messages from the `handle_call` clause patterns
(`{:create, team_id}`, `{:get, team_id}`, `{:delete, team_id}` — three
call tags), its reply type from the `{:reply, r, s}` tuples
(`{:ok, ref} | :error | :ok`, the inductive `Reply`, where `:ok` and
`{:ok, ref}` share a tag and the unary one is named `ok1`) and its state
from `init/1`'s literal `%{tables: %{}}` — a record with one named field
`tables`, an association list of team ids to table references.

Both are `Term`, the opaque type of `Leanactors/Term.lean`: the source
says nothing about what a team id is, and an ETS table reference is not
something the model can look inside. What it can do is count: the state
carries a hidden `ets : Nat`, `:ets.new/2` returns `Term.mk ets` and bumps
it, and `:ets.delete/1` — with the `try ... rescue ArgumentError` around
it — is dropped, because the effect of deleting a table is not visible in
this model. So what is proved below is a property of the registry's *map*,
not of ETS.

**Properties.** This file is the model: the hand-written behaviour, its
equality with the translated one, the bounded check of the property and a
mutant the check catches. The proof that the property holds in *every*
reachable configuration is `Leanactors.Examples.TableRegistryProof`
(`refs_distinct`, `refs_below_counter`), which states the invariant this
file only checks:

* A team id maps to at most one reference.
* Distinct teams hold distinct references: no two teams ever share an ETS
  table.
-/

namespace Leanactors.Examples.TableRegistry

open Leanactors Config Sys

export Leanactors.Gen.TableRegistry (Reply Msg St table_registry sig)

/-- The behaviour, hand-written. `create` always inserts (`Map.put`
replaces an existing entry), `get` answers from the map, `delete` answers
`:ok` either way and drops the entry when there was one. -/
def beh : EBehavior St Msg
  | _, _, .table_registry m n, .create c t =>
      (.table_registry (AssocList.insert m t (Term.mk n)) (n + 1),
       [.send c (.reply (.ok1 (Term.mk n)))])
  | _, _, .table_registry m n, .get c t =>
      (match AssocList.get? m t with
       | some r => (.table_registry m n, [.send c (.reply (.ok1 r))])
       | none => (.table_registry m n, [.send c (.reply .error)]))
  | _, _, .table_registry m n, .delete c t =>
      (match AssocList.get? m t with
       | none => (.table_registry m n, [.send c (.reply .ok)])
       | some _ => (.table_registry (AssocList.erase m t) n, [.send c (.reply .ok)]))
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.TableRegistry.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;> first | rfl | simp [Gen.TableRegistry.beh, beh]

/-- The registry alone, an empty map and a counter at 0. Callers are
outside the system (the replies go to pid 1, which is not an actor), which
is exactly how the real module is used: the caller blocks in
`GenServer.call`. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.table_registry [] 0, []⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## The properties, as a bounded check -/

/-- `Uniq` as a `Bool`, for the explorer. -/
def uniqB : List (Term × Term) → Bool
  | [] => true
  | kv :: rest => rest.all (fun x => x.1 != kv.1 && x.2 != kv.2) && uniqB rest

/-- Every registry in the system has a map with no repeated team and no
repeated reference. -/
def checkUniq (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.table_registry m _) => uniqB m
  | _ => false

/-- Two teams, each created, looked up and deleted. -/
def teamA : Term := Term.mk 7
def teamB : Term := Term.mk 8

def envMsgs : Pid → List Msg
  | 0 => [.create 1 teamA, .create 1 teamB, .get 1 teamA, .delete 1 teamA]
  | _ => []

def explore (b : EBehavior St Msg) (sg : Signals St Msg) (chk : Sys St Msg → Bool)
    (s : Sys St Msg) (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sg chk envMsgs s depth env

#eval explore beh sig checkUniq init 8 4

/-- **Mutant**: `:ets.new` without the counter bump — the same reference
is handed to every team. The checker finds two teams sharing a table. -/
def behSameRef : EBehavior St Msg
  | _, _, .table_registry m n, .create c t =>
      (.table_registry (AssocList.insert m t (Term.mk n)) n,
       [.send c (.reply (.ok1 (Term.mk n)))])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behSameRef sig checkUniq init 8 4

/-! ## Concrete traces -/

/-- Two teams claim a table; the second reference is not the first. -/
def two : Sys St Msg :=
  let s1 := runSys beh sig { init with cfg := init.cfg.deliver 0 (.create 1 teamA) } [.run 0]
  runSys beh sig { s1 with cfg := s1.cfg.deliver 0 (.create 1 teamB) } [.run 0]

/-- Deleting `teamA` drops its entry and leaves the counter alone, so the
next table is still fresh. -/
def dropped : Sys St Msg :=
  let s1 := runSys beh sig { two with cfg := two.cfg.deliver 0 (.delete 1 teamA) } [.run 0]
  runSys beh sig { s1 with cfg := s1.cfg.deliver 0 (.create 1 teamA) } [.run 0]

#eval (two.cfg.stateOf 0, two.cfg.get 1)
#eval dropped.cfg.stateOf 0

end Leanactors.Examples.TableRegistry
