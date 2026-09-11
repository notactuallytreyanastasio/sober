import Leanactors.Explore
import Leanactors.Gen.RadioLive
/-!
# Leanactors.Examples.RadioLive

`BobsBroadcastWeb.RadioLive`, copied verbatim into
`elixir/real/radio_live.ex` from a real project and translated by
`elixir/to_lean.exs` with no annotations: the LiveView of an internet
radio station, subscribed to `"radio:now_playing"`.

Two things the translator had to do for this file. The source updates its
socket with a *chain* of assigns —
`socket |> assign(:now_playing, track_info) |> assign(:playing, ...)` —
whose inner socket is no longer a variable; the chain is folded into the
single record update `%{socket | now_playing: .., playing: ..}`, which is
what the chain means, because the intermediate socket is anonymous and
every value in it reads the original. And the body writes
`track_info != nil`: the model has nil only at an `Option` type, so the
payload of `{:now_playing, track_info}` is inferred `term() | nil` rather
than the opaque `term()` a payload gets by default — a nil comparison is
written only about a value that may be absent, and in a module with no
`@type` that test is the only evidence there is. The comparison is then a
`Bool`, which is where the `playing` assign gets its field type.

**What is not here.** `mount/3` is the LiveView lifecycle, so the socket
the station starts with comes from the spawn site the way a GenServer's
state does when it has no `init/1`; `render/1` is not a transition; and
`handle_event/3` — the browser pressing *Play* or *Stop* — is driven by
the channel rather than by this mailbox, so it is not a clause of `beh`.
The generated file says so in its own header.

**Property.** The button and the track agree: `playing` is true exactly
when `now_playing` holds a track. That is what the broadcast handler
maintains — it writes both fields from the same payload — and it is what
`mount/3` establishes, since it assigns both from the same
`Broadcaster.now_playing()`. It is a property of this mailbox and not of
the running view: `handle_event("play", ..)` sets `playing` to `true` on
its own, without a track, and that transition is the one the model does
not carry. The mutant that keeps the old `playing` instead of rewriting it
is caught as soon as the station goes off the air.
-/

namespace Leanactors.Examples.RadioLive

open Leanactors Config Sys

export Leanactors.Gen.RadioLive (Msg St sig)

/-- The behaviour, hand-written: a broadcast rewrites both assigns from the
same payload — the track, and whether there is one. -/
def beh : EBehavior St Msg
  | _, _, .radio_live _ _, .now_playing track => (.radio_live track (track ≠ none), [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.RadioLive.beh = beh := by
  funext me fresh s m
  cases s <;> cases m <;> rfl

def t1 : Term := Term.mk 1
def t2 : Term := Term.mk 2

/-- One view, mounted while `t1` is on the air. The broadcaster is not in
this system: its `"radio:now_playing"` messages arrive as environment
messages. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.radio_live (some t1) true, []⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## The property, as a bounded check -/

/-- The button agrees with the track. -/
def checkAgrees (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.radio_live track playing) => playing = track.isSome
  | _ => false

/-- What the broadcaster can say: a new track, and going off the air. -/
def envMsgs : Pid → List Msg
  | 0 => [.now_playing (some t2), .now_playing none]
  | _ => []

def explore (b : EBehavior St Msg) (sg : Signals St Msg) (chk : Sys St Msg → Bool)
    (s : Sys St Msg) (depth env : Nat) : Nat × Option (List String) :=
  exploreWith b sg chk envMsgs s depth env

#eval explore beh sig checkAgrees init 8 4

/-- **Mutant**: the handler stores the track but leaves `playing` alone —
the one-line slip of writing `assign(:now_playing, track_info)` and
forgetting the second link of the chain. The Stop button then stays up
after the station goes off the air, which the check finds in one message. -/
def behKeepPlaying : EBehavior St Msg
  | _, _, .radio_live _ playing, .now_playing track => (.radio_live track playing, [])

#eval explore behKeepPlaying sig checkAgrees init 8 4

/-! ## The property, proved -/

/-- The invariant, on one view's state. -/
def Agrees : St → Prop
  | .radio_live track playing => playing = track.isSome

/-- Every state the behaviour produces satisfies it, whatever it started
from: both fields come from the same payload. -/
theorem agrees_step (me fresh : Pid) (s : St) (m : Msg) : Agrees (beh me fresh s m).1 := by
  cases s <;> cases m <;> (rename_i track; cases track <;> simp [beh, Agrees])

/-! ## A concrete trace -/

/-- A new track, then the station goes off the air: the button follows. -/
def afterOffAir : Sys St Msg :=
  [some t2, none].foldl
    (fun s t => runSys beh sig { s with cfg := s.cfg.deliver 0 (.now_playing t) } [.run 0]) init

#eval afterOffAir.cfg.stateOf 0

end Leanactors.Examples.RadioLive
