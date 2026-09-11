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

**Properties.**

* A team id maps to at most one reference (`team_has_one_ref`).
* Distinct teams hold distinct references (`refs_unique`): no two teams
  ever share an ETS table.

Both come from one invariant on the registry's map, `AssocList.Uniq`
(no repeated key, no repeated value), kept by `create` because the
reference it inserts is fresh — every reference already in the map has an
id below the counter (`Bounded`) and the new one is the counter. The
counter is what makes this a per-actor invariant: no other actor, no
message and no signal can put a reference into the map.
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

/-! ## The proof

`Bounded m n` says every reference in the map was created before the
counter reached `n`; with `Uniq m` it is inductive. The only step that
can change a registry's state is its own `run`, so `Inv` is stated for
every pid and the other three kinds of step are the `SysProps` case
lemmas. -/

/-- Every reference in the map has an id below the counter. -/
def Bounded (m : List (Term × Term)) (n : Nat) : Prop := ∀ kv ∈ m, kv.2.id < n

theorem Bounded.nil (n : Nat) : Bounded [] n := by
  intro kv hkv; cases hkv

/-- Hence the reference the counter is about to create is in no entry. -/
theorem Bounded.fresh {m : List (Term × Term)} {n : Nat} (h : Bounded m n) :
    ∀ kv ∈ m, kv.2 ≠ Term.mk n :=
  fun kv hkv => Term.ne_of_id_ne (Nat.ne_of_lt (h kv hkv))

theorem Bounded.insert {m : List (Term × Term)} {n : Nat} (h : Bounded m n) (k : Term) :
    Bounded (AssocList.insert m k (Term.mk n)) (n + 1) := by
  intro kv hkv
  obtain ⟨kk, vv⟩ := kv
  rcases AssocList.mem_insert hkv with ⟨_, rfl⟩ | hkv
  · simp
  · have := h _ hkv; omega

theorem Bounded.erase {m : List (Term × Term)} {n : Nat} (h : Bounded m n) (k : Term) :
    Bounded (AssocList.erase m k) n := by
  intro kv hkv
  obtain ⟨kk, vv⟩ := kv
  exact h _ (AssocList.mem_erase hkv).1

/-- Every registry state in the system has a bounded, unique map. -/
def Inv (s : Sys St Msg) : Prop :=
  ∀ p m n, s.cfg.stateOf p = some (.table_registry m n) → Bounded m n ∧ AssocList.Uniq m

theorem Inv.set {a : Sys St Msg} (hi : Inv a) {p : Pid} {st' : St} {rest : List Msg}
    (hst : ∀ m n, st' = .table_registry m n → Bounded m n ∧ AssocList.Uniq m) :
    Inv { a with cfg := a.cfg.set p ⟨st', rest⟩ } := by
  intro q m n h
  simp only [stateOf_set] at h
  split at h
  · exact hst m n (Option.some.inj h)
  · exact hi q m n h

theorem Inv.deliver {a : Sys St Msg} (hi : Inv a) (q : Pid) (msg : Msg) :
    Inv { a with cfg := a.cfg.deliver q msg } := by
  intro p m n h
  simp only [stateOf_deliver] at h
  exact hi p m n h

theorem Inv.terminate {a : Sys St Msg} (hi : Inv a) (p : Pid) (r : Reason) :
    Inv (a.terminate p r) := by
  intro q m n h
  rw [terminate_stateOf] at h
  split at h
  · cases h
  · exact hi q m n h

/-- The registry's own step, clause by clause: `create` inserts the fresh
`Term.mk n` and bumps the counter, `get` changes nothing, `delete`
erases. -/
theorem Inv.run {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a) : Inv b := by
  obtain ⟨st, msg, rest, hget, hs'⟩ := runE_cases h
  obtain ⟨m, n⟩ := st
  obtain ⟨hb, hu⟩ := hi p m n (by simp [stateOf, hget])
  cases msg with
  | create c t =>
    simp only [beh, applyEffects, List.foldl, applyEffect] at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
    · exact (hi.set (by rintro m' n' ⟨rfl, rfl⟩; exact ⟨hb.insert t, hu.insert_fresh hb.fresh⟩)).deliver c _
    · cases hr
  | get c t =>
    -- both arms answer from the map and leave it alone
    simp only [beh] at hs'
    split at hs' <;>
      · simp only [applyEffects, List.foldl, applyEffect] at hs'
        rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
        · exact (hi.set (by rintro m' n' ⟨rfl, rfl⟩; exact ⟨hb, hu⟩)).deliver c _
        · cases hr
  | delete c t =>
    simp only [beh] at hs'
    split at hs'
    · -- no entry: the map is untouched
      simp only [applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact (hi.set (by rintro m' n' ⟨rfl, rfl⟩; exact ⟨hb, hu⟩)).deliver c _
      · cases hr
    · -- an entry: erased, which keeps both halves of the invariant
      simp only [applyEffects, List.foldl, applyEffect] at hs'
      rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
      · exact (hi.set (by rintro m' n' ⟨rfl, rfl⟩; exact ⟨hb.erase t, hu.erase t⟩)).deliver c _
      · cases hr
  | reply r =>
    simp only [beh, applyEffects, List.foldl] at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨_, hr, _⟩
    · exact hi.set (by rintro m' n' ⟨rfl, rfl⟩; exact ⟨hb, hu⟩)
    · cases hr

/-- Nobody links, traps or signals, so a signal step pops the queue and
either vanishes or kills its target. -/
theorem Inv.signal {a b : Sys St Msg} (h : signalE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨q, _, _, rest, _, hc⟩ := signalE_cases h
  have hpop : Inv { a with signals := rest } := fun p m n h => hi p m n h
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact hpop
  · exact hpop.deliver q _
  · exact hpop
  · exact hpop.terminate q .error
  · exact hpop.terminate q .error

/-- No DOWN codec is declared, so a DOWN step only pops the queue. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, rest, _, hc⟩ := downE_cases h
  rcases hc with ⟨codec, hcodec, _, _⟩ | rfl
  · exact absurd hcodec (by simp [Gen.TableRegistry.sig])
  · exact fun p m n h => hi p m n h

/-- A timer firing is a delivery (this program arms none). -/
theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b := by
  obtain ⟨to, msg, _, rfl⟩ := timerE_cases h
  have herase : Inv { a with timers := a.timers.eraseIdx i } := fun p m n h => hi p m n h
  exact herase.deliver to msg

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  cases h with
  | run p _ hrun => exact hi.run hrun
  | signal _ hsig => exact hi.signal hsig
  | down _ hdown => exact hi.down hdown
  | timer i _ htimer => exact hi.timer htimer

theorem init_inv : Inv init := by
  intro p m n h
  by_cases h0 : p = 0
  · subst h0
    simp only [init, stateOf, Config.get] at h
    obtain ⟨rfl, rfl⟩ := (by simpa using h : m = [] ∧ 0 = n)
    exact ⟨Bounded.nil 0, AssocList.uniq_nil⟩
  · simp [init, stateOf, Config.get, h0] at h

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv (fun h hi => Inv.step h hi) init_inv

/-! ### The two properties -/

/-- **A team id maps to at most one reference.** -/
theorem team_has_one_ref {s : Sys St Msg} (hr : SysReach beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t r r' : Term} (h1 : (t, r) ∈ m) (h2 : (t, r') ∈ m) : r = r' :=
  ((reach_inv hr) p m n hs).2.key_inj h1 h2

/-- **Distinct teams hold distinct references**: if two teams are mapped
to the same ETS table they are the same team. -/
theorem refs_unique {s : Sys St Msg} (hr : SysReach beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t t' r : Term} (h1 : (t, r) ∈ m) (h2 : (t', r) ∈ m) : t = t' :=
  ((reach_inv hr) p m n hs).2.val_inj h1 h2

/-- The same two, for the generated behaviour, through `beh_eq_gen`. -/
theorem refs_unique_gen {s : Sys St Msg} (hr : SysReach Gen.TableRegistry.beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t t' r : Term} (h1 : (t, r) ∈ m) (h2 : (t', r) ∈ m) : t = t' := by
  rw [beh_eq_gen] at hr
  exact refs_unique hr hs h1 h2

theorem team_has_one_ref_gen {s : Sys St Msg} (hr : SysReach Gen.TableRegistry.beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t r r' : Term} (h1 : (t, r) ∈ m) (h2 : (t, r') ∈ m) : r = r' := by
  rw [beh_eq_gen] at hr
  exact team_has_one_ref hr hs h1 h2

end Leanactors.Examples.TableRegistry
