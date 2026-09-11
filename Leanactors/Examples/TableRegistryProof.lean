import Leanactors.Examples.TableRegistry
/-!
# Leanactors.Examples.TableRegistryProof

The safety proof for `Loom.Teams.TableRegistry`, the first module in this
repository that was not written for it: `elixir/real/table_registry.ex` is
a byte-for-byte copy of a module from a real project, translated with no
annotations and no edits (see `Leanactors.Examples.TableRegistry` for the
model and the bounded check).

**What is proved.** For every configuration reachable from `init` under
unbounded scheduling — any interleaving of runs, signals, DOWNs and
timers, any sequence of `{:create, team}`, `{:get, team}` and
`{:delete, team}` calls from anywhere:

* `refs_distinct` — two *different* team ids never map to the same ETS
  table reference. Ask the registry for team `t` and for team `t'`; if
  `t ≠ t'` the two answers are different references.
* `refs_below_counter` — every reference the registry stores was created
  before the counter reached its current value. This is the half that
  makes the first one inductive: `create` inserts `Term.mk n` where `n`
  is the counter, and the bound says no entry already holds that.
* `team_has_one_ref` — a team id maps to at most one reference (the map
  has no repeated key).

Each is stated twice: once for the hand-written `beh` and once for
`Gen.TableRegistry.beh`, the behaviour the translator emitted, which
`beh_eq_gen` says is the same function.

**What is not proved, and cannot be.** These are properties of the
*registry's own map of references*, not of ETS:

* An ETS table is an opaque `Term` (`Leanactors/Term.lean`) handed out by
  a counter. `:ets.new/2` is modelled as "a fresh value, distinct from
  every value handed out before"; nothing else about it is modelled.
* `:ets.delete/1` and its `try ... rescue ArgumentError` wrapper are
  dropped by the translator, so this proof says nothing about whether a
  deleted table is really gone, whether a reference outlives its table, or
  what any reader of the table sees. `delete` here only drops the map
  entry.
* Nothing is claimed about the contents of a table, about concurrent
  readers reaching ETS directly (they bypass the registry and so bypass
  this model), or about the module's public API wrappers
  (`create_table/1` and friends are `GenServer.call` shims the translator
  does not translate; the proof is about the callbacks they call).
* The registry is proved as a closed system: one actor, callers outside
  it. A caller that crashed mid-call, and the reply it never reads, are
  not part of the statement.

Under those abstractions the claim "two teams never share a table" holds
for the real file as written, and the mutant in
`Leanactors.Examples.TableRegistry` (`behSameRef`, `:ets.new` without the
counter bump) is the one-line change that breaks it.

## The recipe

The `SysProps` recipe, as in `LockProof` and `TtlProof`: state `Inv` over
a whole `Sys`, prove it is kept by each of the four `SysStep` cases
(`Inv.run`, `Inv.signal`, `Inv.down`, `Inv.timer`, assembled into
`Inv.step`), prove `init_inv`, and get `reach_inv` from
`SysReach.inv`. The corollaries then read the invariant off any reachable
state.
-/

namespace Leanactors.Examples.TableRegistry

open Leanactors Config Sys

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

/-! ### The properties

The three headline statements. `refs_distinct` is the one the module
exists for; the other two are the halves it is built from. -/

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

/-! ### The headline statements

The two above are stated over membership in the map, which is how the
invariant is carried. These are the same facts as the registry's callers
see them: what `{:get, team}` answers is `AssocList.get?`, so a question
about two teams' answers is a question about two `get?`s. -/

/-- **Distinct team ids map to distinct ETS references.** If the registry
answers team `t` with reference `r` and team `t'` with reference `r'`, and
`t` and `t'` are different teams, then `r` and `r'` are different tables.
Holds in every reachable configuration, for every registry in it. -/
theorem refs_distinct {s : Sys St Msg} (hr : SysReach beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t t' r r' : Term} (hne : t ≠ t')
    (h1 : AssocList.get? m t = some r) (h2 : AssocList.get? m t' = some r') :
    r ≠ r' := by
  intro e
  subst e
  exact hne (refs_unique hr hs (AssocList.mem_of_get? h1) (AssocList.mem_of_get? h2))

/-- **Every stored reference is below the counter.** The `k`-th table the
registry hands out is `Term.mk k` and the counter is the number handed out
so far, so a reference in the map was created strictly before now. This is
what makes `refs_distinct` inductive: the reference `create` is about to
insert is `Term.mk n`, and by this bound no entry holds it yet. -/
theorem refs_below_counter {s : Sys St Msg} (hr : SysReach beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t r : Term} (h : AssocList.get? m t = some r) : r.id < n :=
  ((reach_inv hr) p m n hs).1 (t, r) (AssocList.mem_of_get? h)

/-- `refs_distinct` for the translated behaviour: this is the statement
about the real file. -/
theorem refs_distinct_gen {s : Sys St Msg} (hr : SysReach Gen.TableRegistry.beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t t' r r' : Term} (hne : t ≠ t')
    (h1 : AssocList.get? m t = some r) (h2 : AssocList.get? m t' = some r') :
    r ≠ r' := by
  rw [beh_eq_gen] at hr
  exact refs_distinct hr hs hne h1 h2

/-- `refs_below_counter` for the translated behaviour. -/
theorem refs_below_counter_gen {s : Sys St Msg} (hr : SysReach Gen.TableRegistry.beh sig init s)
    {p : Pid} {m : List (Term × Term)} {n : Nat}
    (hs : s.cfg.stateOf p = some (.table_registry m n))
    {t r : Term} (h : AssocList.get? m t = some r) : r.id < n := by
  rw [beh_eq_gen] at hr
  exact refs_below_counter hr hs h

end Leanactors.Examples.TableRegistry
