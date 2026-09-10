import Leanactors.Examples.LockProof
/-!
# Leanactors.Examples.LockFcfs

**Bounded waiting / first-come-first-served.** A client queued at rank `r`
(with `r` clients ahead of it) sees exactly one rank decrease per lock
handover and is never overtaken: after `k` handovers while it waits its
rank is `r - k`, so it holds the lock after at most `r` handovers.

This is the first property in the development where mailbox FIFO is
load-bearing. Without it the server could process a client's *next*
`acquire` before its pending `release`, enqueue the current holder, and a
later handover would pop that stale entry without changing rank. The
invariant fields `ordered` (no `acquire h` ahead of a `release h` in the
server's mailbox) and `holder_not_queued` exclude that, and both are
inductive only because `Step.queue` says sends append at the tail.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Lock

open Leanactors Config

def queueOf (c : Config St Msg) : List Pid :=
  match c.stateOf server with
  | some (.lock _ q) => q
  | _ => []

def holderOf (c : Config St Msg) : Option Pid :=
  match c.stateOf server with
  | some (.lock h _) => h
  | _ => none

/-- Number of clients ahead of `x` in a queue (length if absent). -/
def rank : List Pid → Pid → Nat
  | [], _ => 0
  | y :: ys, x => if y = x then 0 else rank ys x + 1

/-- 1 if the lock passed from one client to a different one. -/
def transfers (a b : Config St Msg) : Nat :=
  match holderOf a, holderOf b with
  | some h, some h' => if h = h' then 0 else 1
  | _, _ => 0

theorem rank_append_of_mem {l : List Pid} {x : Pid} (hx : x ∈ l) (l' : List Pid) :
    rank (l ++ l') x = rank l x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.cons_append, rank]
    by_cases hy : y = x
    · simp [hy]
    · simp only [hy, if_false]
      rcases List.mem_cons.mp hx with h | h
      · exact absurd h.symm hy
      · rw [ih h]

theorem transfers_self (a : Config St Msg) : transfers a a = 0 := by
  unfold transfers
  cases holderOf a <;> simp

/-- Environment ticks touch no server state. -/
theorem queueOf_deliver (c : Config St Msg) (p : Pid) (m : Msg) :
    queueOf (c.deliver p m) = queueOf c ∧ holderOf (c.deliver p m) = holderOf c := by
  simp [queueOf, holderOf, stateOf_deliver]

/-- **One step.** While `x` stays queued, its rank drops by exactly the
number of handovers (0 or 1) in that step. -/
theorem Step.rank_step {a b : Config St Msg} (hi : Inv a) (h : Step beh a b) {x : Pid}
    (hx : x ∈ queueOf a) (hx' : x ∈ queueOf b) :
    rank (queueOf b) x + transfers a b = rank (queueOf a) x := by
  obtain ⟨p, s, m, rest, hget, hstate, -, -⟩ := h.chars
  obtain ⟨h0, q0, hsrv⟩ := hi.hasServer
  by_cases hp : p = server
  · subst hp
    have hsp : a.stateOf server = some s := by simp [stateOf, hget]
    rw [hsrv] at hsp
    injection hsp with hs
    subst hs
    have hb : b.stateOf server = some (beh server (.lock h0 q0) m).1 := by rw [hstate]; simp
    simp only [queueOf, holderOf, hsrv] at hx ⊢
    simp only [queueOf, hb] at hx'
    simp only [transfers, holderOf, hsrv, hb]
    cases m with
    | tick => cases h0 <;> simp [beh]
    | reply r => cases r; cases h0 <;> simp [beh]
    | acquire y =>
      cases h0 with
      | none =>
        have := hi.queue_empty q0 hsrv
        subst this
        simp at hx
      | some hh =>
        simp [beh]
        exact rank_append_of_mem hx _
    | release y =>
      cases h0 with
      | none => simp [beh]
      | some hh =>
        by_cases hy : y = hh
        · subst hy
          cases q0 with
          | nil => simp at hx
          | cons n rest' =>
            simp only [beh, if_true, eq_self_iff_true] at hx' ⊢
            -- the new holder is not the old one, so this is a handover
            have hnq := hi.holder_not_queued y (n :: rest') hsrv
            have hny : n ≠ y := by
              intro e; subst e; simp [List.count_cons] at hnq
            -- and the new holder is not queued behind itself, so `x ≠ n`
            have hnn : rest'.count n = 0 := by
              have old := hi.nonholder (some y) (n :: rest') hsrv n (by simp [Ne.symm hny])
              have := w_le a n
              simp [List.count_cons] at old
              omega
            have hxn : n ≠ x := by
              intro e; subst e
              exact (List.count_eq_zero.mp hnn) hx'
            simp [rank, hxn, Ne.symm hny]
        · simp [beh, hy]
  · have hb : b.stateOf server = a.stateOf server := by rw [hstate]; simp [Ne.symm hp]
    simp only [queueOf, holderOf, transfers, hb]
    cases a.stateOf server with
    | none => simp
    | some s' =>
      cases s' with
      | lock h q => cases h <;> simp
      | client _ => simp
      | client_await0 => simp

/-- A run during which client `x` is queued in every configuration,
counting lock handovers. Environment ticks are allowed and never hand over. -/
inductive Waiting (x : Pid) : Config St Msg → Config St Msg → Nat → Prop
  | refl (c) (hx : x ∈ queueOf c) : Waiting x c c 0
  | step {a b c k} (hx : x ∈ queueOf a) (h : Step beh a b) (w : Waiting x b c k) :
      Waiting x a c (k + transfers a b)
  | env {a b c k} (hx : x ∈ queueOf a) (h : EnvStep a b) (w : Waiting x b c k) :
      Waiting x a c k

theorem Waiting.mem_start {x : Pid} {a c : Config St Msg} {k : Nat} (w : Waiting x a c k) :
    x ∈ queueOf a := by
  cases w <;> assumption

/-- **Bounded waiting.** Rank plus handovers seen is constant while queued. -/
theorem bounded_waiting {x : Pid} {c c' : Config St Msg} {k : Nat}
    (w : Waiting x c c' k) (hi : Inv c) :
    rank (queueOf c') x + k = rank (queueOf c) x := by
  induction w with
  | refl c hx => simp
  | step hx h w ih =>
    have := Step.rank_step hi h hx w.mem_start
    have ih := ih (Inv.step h hi)
    omega
  | env hx h w ih =>
    cases h with
    | tick p =>
      have ih := ih (Inv.env (EnvStep.tick _ p) hi)
      rw [(queueOf_deliver _ p .tick).1] at ih
      exact ih

/-- **FCFS in reachable configurations.** A client with `r` clients ahead of
it sees at most `r` handovers before it holds the lock; nobody overtakes it. -/
theorem fcfs (n : Nat) {c c' : Config St Msg} (hr : ReachEnv (initCfg n) c)
    {x : Pid} {k : Nat} (w : Waiting x c c' k) :
    k ≤ rank (queueOf c) x ∧ rank (queueOf c') x = rank (queueOf c) x - k := by
  have := bounded_waiting w (hr.inv (initCfg_inv n))
  omega

end Leanactors.Examples.Lock
