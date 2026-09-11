import Leanactors.Explore
import Leanactors.SysProps
import Leanactors.Gen.Feed
/-!
# Leanactors.Examples.Feed

A feed over PubSub, translated from `elixir/src/feed.ex`: a publisher
broadcasts `post n` on the topic `"feed"` at every `tick` (`n` counting
from 1), two subscribers spawned at `start` subscribe in their `init/1`
(the translator emits the `subscribe` at the spawn site, for the child's
pid) and count the posts they receive; a subscriber told to `leave`
unsubscribes.

**Property (checked).** Every subscriber has received a prefix of the
published sequence: with `seen` posts counted, its mailbox holds exactly
`post (seen + 1), …, post (seen + k)` in that order with `seen + k ≤ n`
(`n` posts published so far), and a subscriber that is still subscribed
(`on = true`) has `seen + k = n`: nothing it is owed is missing. Its flag
agrees with `Sys.subs`. Two mutants (a subscriber that forgets to
unsubscribe; a publisher that broadcasts the stale number) are caught.

**Proved.** Every subscription in a reachable system is `("feed", q)` with
`q ≠ 0`: the publisher never subscribes itself (`subs_feed_only`, through
`SysStep.mem_subs_cases`; the prefix property itself is checked, not yet
proved).
-/

namespace Leanactors.Examples.Feed

open Leanactors Config Sys

export Leanactors.Gen.Feed (Msg St publisher sig)

/-- The behaviour, hand-written. -/
def beh : EBehavior St Msg
  | _, fresh, .publisher n, .start =>
      (.publisher n, [.spawnLink (.subscriber 0 true), .subscribe fresh "feed",
                      .spawnLink (.subscriber 0 true), .subscribe (fresh + 1) "feed"])
  | _, _, .publisher n, .tick => (.publisher (n + 1), [.broadcast "feed" (.post (n + 1))])
  | _, _, .subscriber seen on, .post _ => (.subscriber (seen + 1) on, [])
  | me, _, .subscriber seen true, .leave => (.subscriber seen false, [.unsubscribe me "feed"])
  | _, _, .subscriber seen false, .leave => (.subscriber seen false, [])
  | _, _, s, _ => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Feed.beh = beh := by
  funext me fresh s m
  cases s with
  | publisher n => cases m <;> rfl
  | subscriber seen on => cases on <;> cases m <;> rfl

/-- The publisher at pid 0 with `start` in its mailbox; pids 1 and 2 are fresh. -/
def init : Sys St Msg :=
  { cfg := ⟨fun p => if p = 0 then some ⟨.publisher 0, [.start]⟩ else none⟩
    next := 1, links := [], signals := [] }

/-! ## Bounded model check -/

/-- The post numbers in a mailbox, in order. -/
def posts : List Msg → List Nat
  | [] => []
  | .post n :: rest => n :: posts rest
  | _ :: rest => posts rest

/-- Pid `q`, if it is a subscriber, has seen a prefix of the `n` posts and
the rest of what it is owed is in its mailbox in order; its flag agrees
with the subscription list. -/
def prefixOk (n : Nat) (s : Sys St Msg) (q : Pid) : Bool :=
  match s.cfg.get q with
  | some ⟨.subscriber seen on, mb⟩ =>
    let ps := posts mb
    ps == List.range' (seen + 1) ps.length && seen + ps.length ≤ n &&
      (!on || seen + ps.length == n) && (s.subs.contains ("feed", q) == on)
  | _ => true

def checkInv (s : Sys St Msg) : Bool :=
  match s.cfg.stateOf 0 with
  | some (.publisher n) => (List.range s.next).all (prefixOk n s)
  | _ => false

/-- The environment ticks the publisher and tells subscribers to leave. -/
def envMsgs : Pid → List Msg
  | 0 => [.tick]
  | _ => [.leave]

#eval exploreWith beh sig checkInv envMsgs init 9 4

/-- **Mutant**: a subscriber that forgets to unsubscribe on `leave`. Caught
by the flag check: it keeps receiving. -/
def behNoUnsub : EBehavior St Msg
  | _, fresh, .publisher n, .start =>
      (.publisher n, [.spawnLink (.subscriber 0 true), .subscribe fresh "feed",
                      .spawnLink (.subscriber 0 true), .subscribe (fresh + 1) "feed"])
  | _, _, .publisher n, .tick => (.publisher (n + 1), [.broadcast "feed" (.post (n + 1))])
  | _, _, .subscriber seen on, .post _ => (.subscriber (seen + 1) on, [])
  | _, _, .subscriber seen true, .leave => (.subscriber seen false, [])
  | _, _, .subscriber seen false, .leave => (.subscriber seen false, [])
  | _, _, s, _ => (s, [])

#eval exploreWith behNoUnsub sig checkInv envMsgs init 9 4

/-- **Mutant**: the publisher broadcasts the stale number `n` instead of
`n + 1`. Caught by the prefix check at the first post. -/
def behStale : EBehavior St Msg
  | _, fresh, .publisher n, .start =>
      (.publisher n, [.spawnLink (.subscriber 0 true), .subscribe fresh "feed",
                      .spawnLink (.subscriber 0 true), .subscribe (fresh + 1) "feed"])
  | _, _, .publisher n, .tick => (.publisher (n + 1), [.broadcast "feed" (.post n)])
  | _, _, .subscriber seen on, .post _ => (.subscriber (seen + 1) on, [])
  | me, _, .subscriber seen true, .leave => (.subscriber seen false, [.unsubscribe me "feed"])
  | _, _, .subscriber seen false, .leave => (.subscriber seen false, [])
  | _, _, s, _ => (s, [])

#eval exploreWith behStale sig checkInv envMsgs init 9 4

/-- The driver's script (`elixir/feed.exs`): start, three ticks, subscriber 1
leaves, two more ticks. -/
def script : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0]
  let s2 := runSys beh sig { s1 with cfg := ((s1.cfg.deliver 0 .tick).deliver 0 .tick).deliver 0 .tick }
    [.run 0, .run 0, .run 0, .run 1, .run 1, .run 1, .run 2, .run 2, .run 2]
  let s3 := runSys beh sig { s2 with cfg := s2.cfg.deliver 1 .leave } [.run 1]
  runSys beh sig { s3 with cfg := (s3.cfg.deliver 0 .tick).deliver 0 .tick } [.run 0, .run 0, .run 2, .run 2]

-- (publisher 5, subscriber 3 false, subscriber 5 true, [("feed", 2)]), as on the BEAM
#eval (script.cfg.stateOf 0, script.cfg.stateOf 1, script.cfg.stateOf 2, script.subs)

/-! ## Where subscriptions come from -/

/-- The fresh counter is positive and every subscription is to `"feed"` by a
pid other than the publisher's. -/
structure Inv (s : Sys St Msg) : Prop where
  next_pos : 0 < s.next
  subs_feed : ∀ x ∈ s.subs, x.1 = "feed" ∧ x.2 ≠ 0

/-- Only the publisher's `start` clause subscribes anyone, and it subscribes
the two fresh pids. -/
theorem subscribe_of_beh {p fresh : Pid} {st : St} {m : Msg} {x : String × Pid}
    (h : Effect.subscribe x.2 x.1 ∈ (beh p fresh st m).2) :
    x.1 = "feed" ∧ (x.2 = fresh ∨ x.2 = fresh + 1) := by
  cases st with
  | publisher n =>
    cases m with
    | start =>
      simp [beh] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h2, Or.inl h1⟩
      · exact ⟨h2, Or.inr h1⟩
    | _ => simp [beh] at h
  | subscriber seen on => cases on <;> cases m <;> simp [beh] at h

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos h.next_mono, ?_⟩
  intro x hx
  rcases h.mem_subs_cases hx with hold | ⟨p, st, m, rest, _, hmem⟩
  · exact hi.subs_feed x hold
  · obtain ⟨ht, hq⟩ := subscribe_of_beh hmem
    refine ⟨ht, ?_⟩
    rcases hq with hq | hq
    · rw [hq]; exact Nat.ne_of_gt hi.next_pos
    · rw [hq]; exact Nat.succ_ne_zero _

theorem init_inv : Inv init := ⟨Nat.zero_lt_one, fun _ hx => by cases hx⟩

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv Inv.step init_inv

/-- **Every subscription is `("feed", q)` with `q ≠ 0`** in every reachable system. -/
theorem subs_feed_only {s : Sys St Msg} (hr : SysReach beh sig init s) :
    ∀ x ∈ s.subs, x.1 = "feed" ∧ x.2 ≠ 0 :=
  (reach_inv hr).subs_feed

/-- The same for the generated behaviour. -/
theorem subs_feed_only_gen {s : Sys St Msg} (hr : SysReach Gen.Feed.beh sig init s) :
    ∀ x ∈ s.subs, x.1 = "feed" ∧ x.2 ≠ 0 :=
  subs_feed_only (beh_eq_gen ▸ hr)

end Leanactors.Examples.Feed
