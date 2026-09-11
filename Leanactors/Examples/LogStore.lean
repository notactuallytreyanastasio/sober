import Leanactors.Explore
import Leanactors.Gen.LogStore
/-!
# Leanactors.Examples.LogStore

`Ensemble.LogStore`, copied verbatim into `elixir/real/log_store.ex` from a
real project (an in-memory ring buffer of log entries that also broadcasts
each entry on PubSub) and translated by `elixir/to_lean.exs` with no
annotations: the module carries no `@type` at all.

What the translator inferred, and why each piece looks the way it does:

* **Messages.** `{:push, entry}` from the one `handle_cast` clause,
  `:get_entries` from the one `handle_call` clause (so it carries a
  leading `caller : Pid`), and `{:new_log_entry, entry}` because the
  module broadcasts it and nothing here handles it.
* **Reply.** The only reply is `:queue.to_list(state.entries)`, which is
  not a literal, so there is no union to infer — but it does have a type.
  The translator renders the clauses once with the reply left out, sees
  that every reply expression is a `List Term`, and compiles the file
  again with that as `@type reply`: `Msg.reply` carries a `List Term`
  rather than collapsing to the opaque `Term`.
* **State.** `defstruct entries: :queue.new(), count: 0, max_entries:
  @default_max_entries` with `init/1` returning `%__MODULE__{max_entries:
  max_entries}`, flattened into the state constructor. A queue is the list
  oldest-first, so `entries : List Term`; the two integer defaults make
  `count` and `max_entries` `Nat`.
* **Registration.** `name: Keyword.get(opts, :name, __MODULE__)`. The
  option list a real `start_link` is handed is not modelled, so the model
  takes the literal default — the translator warns about exactly that.

Logging is not modelled and neither is what a log entry *is*: an entry is
a `Term`, so this is a model of the buffer, not of the messages in it.

**Property.** `count` never exceeds `max_entries`: the counter only moves
on the branch that tested `count < max_entries`, which is what makes the
buffer bounded. Checked below over every interleaving to depth 9, and
checked to fail for the mutant that bumps the counter on both branches.
-/

namespace Leanactors.Examples.LogStore

open Leanactors Config Sys

export Leanactors.Gen.LogStore (Msg St log_store sig)

/-- The behaviour, hand-written. A `push` broadcasts the entry and then
either drops the oldest (the buffer is full, the count stays) or appends
and counts one more; `get_entries` answers with the buffer, oldest first. -/
def beh : EBehavior St Msg
  | _, _, .log_store es n cap, .get_entries c => (.log_store es n cap, [.send c (.reply es)])
  | _, _, .log_store es n cap, .push e =>
      (if n ≥ cap then .log_store (es.tail ++ [e]) n cap
       else .log_store (es ++ [e]) (n + 1) cap,
       [.broadcast "logs" (.new_log_entry e)])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.LogStore.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;>
    first
      | rfl
      | (simp only [Gen.LogStore.beh, beh]; split <;> rfl)

/-- The store alone, empty, with room for two entries. Callers are outside
the system (pid 1 is not an actor), which is how the real module is used:
the caller blocks in `GenServer.call`. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.log_store [] 0 2, []⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## The property, as a bounded check -/

/-- The ring-buffer invariant, in full: the count is the buffer's real
length, and the buffer never exceeds the cap.

The round-8 verifier found the earlier version of this check (`n ≤ cap`
alone) to be nearly vacuous: a behaviour that maintained the counter but
never appended to the buffer passed it. Tying `n` to `es.length` is what
makes the check discriminate. -/
def checkBounded (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.log_store es n cap) => n == es.length && es.length ≤ cap
  | _ => false

def e1 : Term := Term.mk 1
def e2 : Term := Term.mk 2
def e3 : Term := Term.mk 3

def envMsgs : Pid → List Msg
  | 0 => [.push e1, .push e2, .push e3, .get_entries 1]
  | _ => []

def explore (b : EBehavior St Msg) (sg : Signals St Msg) (chk : Sys St Msg → Bool)
    (s : Sys St Msg) (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sg chk envMsgs s depth env

#eval explore beh sig checkBounded init 9 4

/-- **Mutant**: the counter is bumped on both branches, as it would be if
the `else` arm's `state.count` were copied into the full arm. The buffer
still holds at most `max_entries` entries, but the count runs away, and
the checker finds it. -/
def behRunaway : EBehavior St Msg
  | _, _, .log_store es n cap, .push e =>
      (if n ≥ cap then .log_store (es.tail ++ [e]) (n + 1) cap
       else .log_store (es ++ [e]) (n + 1) cap,
       [.broadcast "logs" (.new_log_entry e)])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behRunaway sig checkBounded init 9 4

/-- **Mutant**: the counter is maintained correctly but the buffer is
never appended to. This is the mutant the round-8 verifier used to show
the old `n ≤ cap` check was vacuous; the strengthened check catches it. -/
def behNoAppend : EBehavior St Msg
  | _, _, .log_store es n cap, .push e =>
      (if n ≥ cap then .log_store es n cap else .log_store es (n + 1) cap,
       [.broadcast "logs" (.new_log_entry e)])
  | me, fresh, s, msg => beh me fresh s msg

#eval explore behNoAppend sig checkBounded init 9 4

/-! ## A concrete trace: the ring drops the oldest -/

/-- Three pushes into a buffer of two: the first entry is gone and the
last two are in order. -/
def three : Sys St Msg :=
  [e1, e2, e3].foldl (fun s e => runSys beh sig { s with cfg := s.cfg.deliver 0 (.push e) } [.run 0]) init

#eval three.cfg.stateOf 0

end Leanactors.Examples.LogStore
