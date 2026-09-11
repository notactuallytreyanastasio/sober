import Leanactors.Explore
import Leanactors.SysProps
import Leanactors.Gen.Ringlog
/-!
# Leanactors.Examples.Ringlog

A ring buffer of log entries, translated from `elixir/src/ringlog.ex` (a
reduction of a real Phoenix application's `LogStore`). The GenServer's state
is its own struct, `defstruct entries: :queue.new(), count: 0, max_entries: 3`,
so the translator flattens it into one `St` constructor with a field per
struct field: `.ringlog (entries : List Entry) (count : Nat) (max_entries : Nat)`.
The Erlang queue is the list, oldest first; an entry is the Lean structure
`Entry` with defaults (`level := .info`, `msg := 0`). A cast `{:push, entry}`
appends and drops the oldest when the buffer is full; the calls `:get_entries`
and `{:by_level, lv}` reply with the list and with `Enum.filter(&(&1.level ==
lv))`. A reader asks through blocking calls and remembers how many entries
came back.

**Property.** `count` is the length of `entries` and never exceeds
`max_entries`: the counter the module keeps by hand agrees with the queue it
describes, and the buffer is bounded. Checked by `exploreWith` over every
interleaving of the two actors and the environment, then proved: `ok_step`
says one behaviour step preserves it and `count_invariant` lifts that to
every configuration reachable under unbounded scheduling.
-/

namespace Leanactors.Examples.Ringlog

open Leanactors Config Sys

export Leanactors.Gen.Ringlog (Level Entry Msg St ringlog sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, _, .ringlog es c mx, .get_entries caller => (.ringlog es c mx, [.send caller (.reply es)])
  | _, _, .ringlog es c mx, .by_level caller lv =>
      (.ringlog es c mx, [.send caller (.reply (es.filter fun e => e.level = lv))])
  | _, _, .ringlog es c mx, .push e =>
      if c ≥ mx then (.ringlog (es.tail ++ [e]) c mx, [])
      else (.ringlog (es ++ [e]) (c + 1) mx, [])
  | me, _, .reader _, .ask_all => (.reader_await0, [.send ringlog (.get_entries me)])
  | me, _, .reader _, .ask_errors => (.reader_await1, [.send ringlog (.by_level me .error)])
  | _, _, .reader n, .log lv => (.reader n, [.send ringlog (.push { level := lv, msg := n })])
  | _, _, .reader_await0, .reply r => (.reader r.length, [])
  | me, _, .reader_await0, m => (.reader_await0, [.send me m])
  | _, _, .reader_await1, .reply r => (.reader r.length, [])
  | me, _, .reader_await1, m => (.reader_await1, [.send me m])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Ringlog.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;> first | rfl | simp [Gen.Ringlog.beh, beh]

/-- The store at pid 0, empty with room for two entries (small enough that
the bounded search reaches a full buffer), and one reader at pid 1 that has
seen nothing. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.ringlog [] 0 2, []⟩
                     else if p = 1 then some ⟨.reader 0, []⟩ else none⟩
    next := 2, links := [], signals := [] }

/-! ## The property, as a bounded check -/

/-- `count` is the length of `entries`, and no more than `max_entries`. -/
def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.ringlog es c mx) => c == es.length && c ≤ mx
  | _ => false

/-- The environment: anyone may push a debug or an error entry into the
store, and may ask the reader to read or to log. -/
def envMsgs : Pid → List Msg
  | 0 => [.push { level := .debug, msg := 1 }, .push { level := .error, msg := 2 }]
  | 1 => [.ask_all, .ask_errors, .log .error]
  | _ => []

def explore (b : EBehavior St Msg) (chk : Sys St Msg → Bool) (s : Sys St Msg)
    (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sig chk envMsgs s depth env

#eval explore beh checkInv init 7 3

/-- **Mutant**: the full buffer forgets to drop its oldest entry (the
`{_, q} = :queue.out(state.entries)` line is left out). The count then
lags behind the queue, which is exactly what `checkInv` watches. -/
def behNoDrop : EBehavior St Msg
  | _, _, .ringlog es c mx, .push e =>
      if c ≥ mx then (.ringlog (es ++ [e]) c mx, [])
      else (.ringlog (es ++ [e]) (c + 1) mx, [])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behNoDrop checkInv init 7 3

/-- **Mutant**: the buffer counts every push, full or not. `count` then
overshoots `max_entries`. -/
def behAlwaysCount : EBehavior St Msg
  | _, _, .ringlog es c mx, .push e =>
      if c ≥ mx then (.ringlog (es.tail ++ [e]) (c + 1) mx, [])
      else (.ringlog (es ++ [e]) (c + 1) mx, [])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behAlwaysCount checkInv init 7 3

/-! ## Concrete traces -/

/-- Four pushes into a buffer of three: the oldest entry is gone and the
count has stopped at three. -/
def filled : Sys St Msg :=
  let msgs : List Msg :=
    [.push { level := .info, msg := 1 }, .push { level := .error, msg := 2 },
     .push { level := .info, msg := 3 }, .push { level := .error, msg := 4 }]
  runSys beh sig { init with cfg := msgs.foldl (fun c m => c.deliver 0 m) init.cfg }
    [.run 0, .run 0, .run 0, .run 0]

/-- The reader asks for the error entries: the blocking call leaves it in
its await state until the reply comes back, and it then remembers two. -/
def read : Sys St Msg :=
  runSys beh sig { filled with cfg := filled.cfg.deliver 1 .ask_errors } [.run 1, .run 0, .run 1]

#eval (filled.cfg.stateOf 0, checkInv filled)
#eval (read.cfg.stateOf 0, read.cfg.stateOf 1)

/-! ## The proof

`Ok` is the property as a `Prop` on one actor's state; `ok_step` says the
behaviour preserves it, and since the behaviour never spawns, that is
enough to lift it to every reachable configuration. -/

/-- The store's counter matches its queue and stays under the cap; the
reader has nothing to say. -/
def Ok : St → Prop
  | .ringlog es c mx => c = es.length ∧ c ≤ mx ∧ 1 ≤ mx
  | _ => True

/-- One behaviour step preserves `Ok`. The full case is the interesting
one: `count ≥ max_entries ≥ 1` forces the queue to be non-empty, so
dropping its head and appending keeps the length. -/
theorem ok_step (me fresh : Pid) (st : St) (m : Msg) (h : Ok st) : Ok (beh me fresh st m).1 := by
  cases st with
  | ringlog es c mx =>
    obtain ⟨hlen, hcap, hmx⟩ := h
    cases m with
    | push e =>
      by_cases hfull : c ≥ mx
      · simp only [beh, hfull, if_pos]
        refine ⟨?_, hcap, hmx⟩
        cases es with
        | nil => simp at hlen ⊢; omega
        | cons a rest => simpa using hlen
      · simp only [beh, hfull, if_neg, not_false_eq_true]
        exact ⟨by simpa using hlen, by omega, hmx⟩
    | _ => exact ⟨hlen, hcap, hmx⟩
  | reader n => cases m <;> trivial
  | reader_await0 => cases m <;> trivial
  | reader_await1 => cases m <;> trivial

/-- The behaviour never spawns: every effect it emits carries no initial
state, so a step can only change the state of the actor that ran. -/
theorem beh_no_spawn (me fresh : Pid) (st : St) (m : Msg) :
    ∀ e ∈ (beh me fresh st m).2, e.init? = none := by
  intro e he
  cases st <;> cases m <;> revert he <;> simp only [beh] <;> (try split) <;> intro he <;>
    first
      | (simp at he; done)
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at he
         subst he
         simp [Effect.init?])

/-- Every live actor satisfies `Ok`. -/
def AllOk (s : Sys St Msg) : Prop := ∀ q st, s.cfg.stateOf q = some st → Ok st

theorem allOk_step {s s' : Sys St Msg} (hst : SysStep beh sig s s') (h : AllOk s) : AllOk s' := by
  intro q st hq
  rcases hst.stateOf_spawn_cases q with hc | hc | ⟨p, x, m, rest, hget, rfl, hc⟩ |
    ⟨p, x, m, rest, _, e, he, hc⟩
  · exact h q st (hc ▸ hq)
  · rw [hc] at hq; exact absurd hq (by simp)
  · rw [hc] at hq
    have hst' : st = (beh q s.next x m).1 := (Option.some.inj hq).symm
    subst hst'
    exact ok_step _ _ x m (h q x (by simp [stateOf, hget]))
  · rw [← hc, beh_no_spawn p s.next x m e he] at hq
    exact absurd hq (by simp)

theorem allOk_reach {s s' : Sys St Msg} (hr : SysReach beh sig s s') (h : AllOk s) : AllOk s' := by
  induction hr with
  | refl => exact h
  | step hst _ ih => exact ih (allOk_step hst h)

theorem allOk_init : AllOk init := by
  intro q st hq
  by_cases h0 : q = 0
  · subst h0; simp [init, stateOf, Config.get] at hq; subst hq; exact ⟨rfl, by omega, by omega⟩
  · by_cases h1 : q = 1
    · subst h1; simp [init, stateOf, Config.get] at hq; subst hq; trivial
    · simp [init, stateOf, Config.get, h0, h1] at hq

/-- **The count invariant.** In every configuration reachable from `init`
under unbounded scheduling, the store's `count` is the length of its
`entries` and does not exceed `max_entries`. -/
theorem count_invariant {s : Sys St Msg} (hr : SysReach beh sig init s)
    {es : List Entry} {c mx : Nat} (hs : s.cfg.stateOf 0 = some (.ringlog es c mx)) :
    c = es.length ∧ c ≤ mx :=
  let ⟨h1, h2, _⟩ := allOk_reach hr allOk_init 0 _ hs
  ⟨h1, h2⟩

end Leanactors.Examples.Ringlog
