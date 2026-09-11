import Leanactors.Explore
import Leanactors.Gen.LogsLive
/-!
# Leanactors.Examples.LogsLive

`EnsembleWeb.LogsLive`, copied verbatim into `elixir/real/logs_live.ex`
from a real project and translated by `elixir/to_lean.exs` with no
annotations: the LiveView that shows the entries
`Leanactors.Examples.LogStore` broadcasts on the topic `"logs"`.

A LiveView socket is a struct with an `assigns` map, and Phoenix's
imported `assign/2,3` is a functional update of it, so the translator
models the socket as the record of the assigns this module's callbacks
touch: the only one is `entries`, and the only thing done to it is
`socket.assigns.entries ++ [entry]`, so the state is
`logs_live (entries : List Term)`. The module declares no `@type` and has
no `init/1`, so the messages come from the `handle_info` patterns —
`{:new_log_entry, entry}`, which is exactly what the store broadcasts.

**What is not here.** Only the pure assigns updates a `handle_info`
performs are modelled. `mount/3` is the LiveView lifecycle, so the initial
entry list comes from the spawn site the way a GenServer's state does when
it has no `init/1`; `render/1` is not a transition at all; and
`handle_event/3` — the browser clicking *Clear* or typing in the search
box — is driven by the channel rather than by this mailbox, so it is not a
clause of `beh`. That last one *is* a transition the real process makes,
so the generated file says so in its header and the property below is a
property of the module's message handling only.

**Property.** Message handling is append-only: whatever the view is
already showing stays, in order, at the front of what it shows next. Start
the view with two entries and check that they are still a prefix of the
list in every reachable configuration — to depth 8, over every
interleaving of four broadcasts of two entries. The mutant that prepends instead of
appending (the easy mistake, and the one that makes a log read backwards)
is caught.
-/

namespace Leanactors.Examples.LogsLive

open Leanactors Config Sys

export Leanactors.Gen.LogsLive (Msg St sig)

/-- The behaviour, hand-written: a new entry goes on the end of the list
the socket is showing, and nothing else reaches this mailbox. -/
def beh : EBehavior St Msg
  | _, _, .logs_live es, .new_log_entry e => (.logs_live (es ++ [e]), [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.LogsLive.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;> rfl

def e1 : Term := Term.mk 1
def e2 : Term := Term.mk 2
def e3 : Term := Term.mk 3

/-- The seed the view is already showing when the check starts. -/
def shown : List Term := [e1, e2]

/-- One view, mounted with `shown`. The store is not in this system: its
broadcasts arrive here as environment messages. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.logs_live shown, []⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## The property, as a bounded check -/

/-- What the view was already showing is still a prefix of what it shows. -/
def checkAppendOnly (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.logs_live es) => shown.isPrefixOf es
  | _ => false

def envMsgs : Pid → List Msg
  | 0 => [.new_log_entry e3, .new_log_entry e1]
  | _ => []

def explore (b : EBehavior St Msg) (sg : Signals St Msg) (chk : Sys St Msg → Bool)
    (s : Sys St Msg) (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sg chk envMsgs s depth env

#eval explore beh sig checkAppendOnly init 8 4

/-- **Mutant**: the new entry goes on the front, as `[entry | entries]`
would. The view still holds every entry, so nothing is lost — but the
order is wrong, and the prefix check finds it after one message. -/
def behPrepend : EBehavior St Msg
  | _, _, .logs_live es, .new_log_entry e => (.logs_live (e :: es), [])

#eval explore behPrepend sig checkAppendOnly init 8 4

/-! ## What the bounded check cannot say

The round-8 verifier showed that `checkAppendOnly` alone is weak: a
behaviour that DROPS every entry passes it (the seed stays a prefix of
itself), and so does one that appends each entry TWICE. The property that
excludes those is about a *step*, not about a state, so the bounded
explorer cannot express it and it is proven here instead.

`stepConserves`: handling one message moves exactly one entry out of the
mailbox and onto the end of the view. Nothing is dropped, nothing is
duplicated, nothing is reordered. -/
theorem stepConserves (es : List Term) (e : Term) (me fresh : Pid) :
    beh me fresh (.logs_live es) (.new_log_entry e) = (.logs_live (es ++ [e]), []) := rfl

/-- The two mutants the verifier used, refuted by that equation: neither
drops nor duplicates is the translated behaviour. -/
theorem not_dropping (es : List Term) (e : Term) :
    beh 0 0 (.logs_live es) (.new_log_entry e) ≠ (.logs_live es, []) := by
  simp [stepConserves]

theorem not_duplicating (es : List Term) (e : Term) :
    beh 0 0 (.logs_live es) (.new_log_entry e) ≠ (.logs_live (es ++ [e, e]), []) := by
  simp [stepConserves]

/-! ## A concrete trace -/

/-- Two broadcasts arrive: the view appends both, in arrival order. -/
def shownAfter : Sys St Msg :=
  [e3, e1].foldl
    (fun s e => runSys beh sig { s with cfg := s.cfg.deliver 0 (.new_log_entry e) } [.run 0]) init

#eval shownAfter.cfg.stateOf 0

end Leanactors.Examples.LogsLive
