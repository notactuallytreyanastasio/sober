import Leanactors.Fair
import Leanactors.Examples.LockFcfs
/-!
# Leanactors.Examples.LockLive

**Liveness of the lock.** `mutex_forever` and `progress_forever` say what
never happens; this file says what must happen: along a fair run, a client
blocked in `GenServer.call(Lock, :acquire)` eventually holds the lock
(`eventually_holds`).

The run is a `CRun beh EnvStep` (actor steps interleaved with environment
ticks) started from `initCfg n`. Fairness:

* `hfair : ∀ p, ρ.WeakFair (.run p)`: every actor with a message is
  eventually scheduled (weak fairness of every `run` choice), and
* `henv : ∀ h, ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)`: a
  client that holds the lock from some time on is eventually ticked by the
  environment (it does not sit in the critical section forever).

The proof follows the token invariant of `LockProof`: while `x` is blocked,
its `acquire` is in the server's mailbox, or `x` is queued, or the server's
`reply ok` is in `x`'s mailbox. Each phase is a `LeadsTo` built from the
`Fair` workhorses:

* `requested_leadsTo` (`rank_leads_to_run server`): the position of
  `acquire x` in the server's mailbox drops at every server step, so the
  server eventually pops it and either grants (`reply ok` to `x`) or
  enqueues `x`.
* `queued_leadsTo_granted` (`LeadsTo.rank_induction` on `rank (queueOf c) x`):
  while `x` is queued the lock is held by some `h ≠ x`; `h`'s token is its
  in-flight grant, its `holding` phase, or its in-flight `release`. Four
  `LeadsTo`s drive it through those phases (`h` processes its grant, the
  environment ticks `h`, `h` processes the tick and sends `release h`, the
  server processes `release h`), and the handover strictly decreases `x`'s
  rank (`Step.rank_step`) or grants `x`.
* `granted_leadsTo_holds` (`rank_leads_to_run x`): the position of
  `reply ok` in `x`'s mailbox drops at every `x` step (a blocked client
  defers everything else by re-enqueueing it at the tail), so `x`
  eventually pops it and enters `holding`.

Only one measure is used throughout: `idxOf c q m`, the index of the first
`m` in `q`'s mailbox. A step by any other actor and an environment tick
only append to a mailbox, so the index is unchanged; a step by `q` pops the
head, so the index drops by one unless the head *is* `m`.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Lock

open Leanactors Config

/-! ## Predicates -/

/-- `x` is blocked in `GenServer.call`. -/
def Waits (x : Pid) (c : Config St Msg) : Prop := c.stateOf x = some .client_await0
/-- `x` is in the critical section. -/
def Holds (x : Pid) (c : Config St Msg) : Prop := c.stateOf x = some (.client .holding)
/-- Message `m` is somewhere in `q`'s mailbox. -/
def Has (c : Config St Msg) (q : Pid) (m : Msg) : Prop := ∃ mb, c.mboxOf q = some mb ∧ m ∈ mb
/-- The server holds `h`. -/
def HolderIs (h : Pid) (c : Config St Msg) : Prop := holderOf c = some h

/-- Index of the first `m` in a list (its length if absent). -/
def idx : List Msg → Msg → Nat
  | [], _ => 0
  | y :: ys, m => if y = m then 0 else idx ys m + 1

/-- Index of the first `m` in `q`'s mailbox. -/
def idxOf (c : Config St Msg) (q : Pid) (m : Msg) : Nat :=
  match c.mboxOf q with
  | some mb => idx mb m
  | none => 0

theorem idx_append_of_mem {l : List Msg} {m : Msg} (hm : m ∈ l) (l' : List Msg) :
    idx (l ++ l') m = idx l m := by
  induction l with
  | nil => simp at hm
  | cons y ys ih =>
    simp only [List.cons_append, idx]
    by_cases hy : y = m
    · simp [hy]
    · simp only [hy, if_false]
      rcases List.mem_cons.mp hm with h | h
      · exact absurd h.symm hy
      · rw [ih h]

theorem idx_cons_of_ne {y m : Msg} (hy : y ≠ m) (ys : List Msg) :
    idx (y :: ys) m = idx ys m + 1 := by
  simp [idx, hy]

/-! ## Mailbox membership and how a step moves it -/

theorem Has.enabled {c : Config St Msg} {q : Pid} {m : Msg} (h : Has c q m) :
    CEnabled c (.run q) := by
  obtain ⟨mb, hmb, hm⟩ := h
  exact (CEnabled_run_iff c q).mpr ⟨mb, hmb, fun e => by subst e; simp at hm⟩

theorem Has.of_mcount_pos {c : Config St Msg} {q : Pid} {m : Msg} (h : 0 < c.mcount q m) :
    Has c q m := by
  unfold mcount at h
  cases hg : c.get q with
  | none => rw [hg] at h; simp at h
  | some a =>
    rw [hg] at h
    exact ⟨a.mailbox, by simp [mboxOf, hg], List.count_pos_iff.mp h⟩

theorem Has.mcount_pos {c : Config St Msg} {q : Pid} {m : Msg} (h : Has c q m) :
    0 < c.mcount q m := by
  obtain ⟨mb, hmb, hm⟩ := h
  rw [mcount_eq_of_mboxOf hmb]
  exact List.count_pos_iff.mpr hm

/-- A mailbox that only grew keeps `m` at the same index. -/
theorem Has.append {a b : Config St Msg} {q : Pid} {m : Msg} {new : List Msg}
    (hmb : b.mboxOf q = (a.mboxOf q).map (· ++ new)) (h : Has a q m) :
    Has b q m ∧ idxOf b q m = idxOf a q m := by
  obtain ⟨mb, hmb', hm⟩ := h
  rw [hmb'] at hmb
  simp at hmb
  refine ⟨⟨mb ++ new, hmb, List.mem_append_left _ hm⟩, ?_⟩
  simp [idxOf, hmb, hmb', idx_append_of_mem hm]

/-- A live actor that is sent `m` has it. -/
theorem Has.of_send {a b : Config St Msg} {q : Pid} {m : Msg} {new : List Msg} {s : St}
    (halive : a.stateOf q = some s) (hmb : b.mboxOf q = (a.mboxOf q).map (· ++ new))
    (hm : m ∈ new) : Has b q m := by
  unfold stateOf at halive
  cases hg : a.get q with
  | none => rw [hg] at halive; simp at halive
  | some x =>
    have hmb0 : a.mboxOf q = some x.mailbox := by simp [mboxOf, hg]
    rw [hmb0] at hmb
    exact ⟨_, hmb, List.mem_append_right _ hm⟩

/-- Popping a head that is not `m` moves `m` one place forward. -/
theorem Has.pop {a b : Config St Msg} {p : Pid} {s : St} {m₀ m : Msg} {rest new : List Msg}
    (hget : a.get p = some ⟨s, m₀ :: rest⟩) (hmb : b.mboxOf p = some (rest ++ new))
    (h : Has a p m) (hne : m₀ ≠ m) : Has b p m ∧ idxOf b p m + 1 = idxOf a p m := by
  obtain ⟨mb, hmb', hm⟩ := h
  have hmb'' : mb = m₀ :: rest := by
    unfold mboxOf at hmb'; rw [hget] at hmb'; simp at hmb'; exact hmb'.symm
  subst hmb''
  have hm' : m ∈ rest := by
    rcases List.mem_cons.mp hm with e | e
    · exact absurd e.symm hne
    · exact e
  refine ⟨⟨_, hmb, List.mem_append_left _ hm'⟩, ?_⟩
  simp [idxOf, hmb, hmb', idx_append_of_mem hm', idx_cons_of_ne hne]

/-! ## What one step does

`run_facts` is `Step.chars` without the counts, for a labelled run step;
`env_facts` is the environment tick. -/

theorem _root_.Leanactors.CStepL.run_facts {a b : Config St Msg} {p : Pid}
    (h : CStepL beh EnvStep (.run p) a b) :
    ∃ s m rest, a.get p = some ⟨s, m :: rest⟩ ∧
      (∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q) ∧
      (∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q)) := by
  cases h with
  | run _ _ s m rest hget =>
    exact ⟨s, m, rest, hget, fun q => by rw [stateOf_deliverAll, stateOf_set],
      fun q => by rw [mboxOf_deliverAll_eq, mboxOf_set]⟩

theorem EnvStep.facts {a b : Config St Msg} (h : EnvStep a b) :
    ∃ p, (∀ q, b.stateOf q = a.stateOf q) ∧
      (∀ q, b.mboxOf q = (a.mboxOf q).map (· ++ if q = p then [.tick] else [])) ∧
      holderOf b = holderOf a ∧ queueOf b = queueOf a := by
  cases h with
  | tick p =>
    exact ⟨p, fun q => stateOf_deliver _ p q _, fun q => mboxOf_deliver_eq _ p q _,
      (queueOf_deliver _ p .tick).2, (queueOf_deliver _ p .tick).1⟩

/-- The state of the stepping actor, from its `get`. -/
theorem stateOf_of_get {a : Config St Msg} {p : Pid} {s : St} {mb : List Msg}
    (hget : a.get p = some ⟨s, mb⟩) : a.stateOf p = some s := by
  simp [stateOf, hget]

theorem mboxOf_of_get {a : Config St Msg} {p : Pid} {s : St} {mb : List Msg}
    (hget : a.get p = some ⟨s, mb⟩) : a.mboxOf p = some mb := by
  simp [mboxOf, hget]

/-- A blocked client stays blocked unless it pops `reply ok`, in which case
it enters `holding`. -/
theorem Waits.step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    {x : Pid} (hx : Waits x a) :
    (Waits x b ∧ (p = x → m ≠ .reply .ok)) ∨ (p = x ∧ m = .reply .ok ∧ Holds x b) := by
  by_cases hp : p = x
  · subst hp
    have hs : s = .client_await0 := by
      have := stateOf_of_get hget; unfold Waits at hx; rw [this] at hx; exact Option.some.inj hx
    subst hs
    cases m with
    | reply r =>
      cases r
      right
      exact ⟨rfl, rfl, by unfold Holds; rw [hst]; simp [beh]⟩
    | tick => left; exact ⟨by unfold Waits; rw [hst]; simp [beh], fun _ e => by cases e⟩
    | acquire y => left; exact ⟨by unfold Waits; rw [hst]; simp [beh], fun _ e => by cases e⟩
    | release y => left; exact ⟨by unfold Waits; rw [hst]; simp [beh], fun _ e => by cases e⟩
  · left
    exact ⟨by unfold Waits at *; rw [hst]; simp [Ne.symm hp, hx], fun e => absurd e hp⟩

/-- A blocked client that pops something other than `reply ok` sends it
back to itself. -/
theorem beh_await_defer (me : Pid) {m : Msg} (hm : m ≠ .reply .ok) :
    beh me .client_await0 m = (.client_await0, [(me, m)]) := by
  cases m with
  | reply r => cases r; exact absurd rfl hm
  | tick => rfl
  | acquire y => rfl
  | release y => rfl

/-- A holding client stays holding unless it pops `tick`, in which case it
goes idle and sends `release`. -/
theorem Holds.step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    {h : Pid} (hh : Holds h a) :
    (Holds h b ∧ (p = h → m ≠ .tick ∧ (beh p s m).2 = [])) ∨
    (p = h ∧ m = .tick ∧ s = .client .holding ∧ b.stateOf h = some (.client .idle)) := by
  by_cases hp : p = h
  · subst hp
    have hs : s = .client .holding := by
      have := stateOf_of_get hget; unfold Holds at hh; rw [this] at hh; exact Option.some.inj hh
    subst hs
    cases m with
    | tick => right; exact ⟨rfl, rfl, rfl, by rw [hst]; simp [beh]⟩
    | reply r => cases r; left; exact ⟨by unfold Holds; rw [hst]; simp [beh], fun _ => ⟨by simp, rfl⟩⟩
    | acquire y => left; exact ⟨by unfold Holds; rw [hst]; simp [beh], fun _ => ⟨by simp, rfl⟩⟩
    | release y => left; exact ⟨by unfold Holds; rw [hst]; simp [beh], fun _ => ⟨by simp, rfl⟩⟩
  · left
    exact ⟨by unfold Holds at *; rw [hst]; simp [Ne.symm hp, hh], fun e => absurd e hp⟩

/-! ## Facts from the invariant -/

theorem Inv.a_le_one {c : Config St Msg} (hi : Inv c) (x : Pid) : a c x ≤ 1 := by
  obtain ⟨h0, q0, hs⟩ := hi.hasServer
  have := w_le c x
  by_cases hx : h0 = some x
  · subst hx
    have := hi.holder x q0 hs
    have := hd_le c x
    omega
  · have := hi.nonholder h0 q0 hs x hx
    omega

theorem Inv.g_le_one {c : Config St Msg} (hi : Inv c) (x : Pid) : g c x ≤ 1 := by
  obtain ⟨h0, q0, hs⟩ := hi.hasServer
  by_cases hx : h0 = some x
  · subst hx
    have := hi.holder x q0 hs
    omega
  · have := hi.nonholder h0 q0 hs x hx
    omega

/-- The server's state, given the holder. -/
theorem HolderIs.srv {c : Config St Msg} (hi : Inv c) {h : Pid} (hh : HolderIs h c) :
    c.stateOf server = some (.lock (some h) (queueOf c)) := by
  obtain ⟨h0, q0, hs⟩ := hi.hasServer
  unfold HolderIs holderOf at hh
  rw [hs] at hh
  simp at hh
  subst hh
  simp [queueOf, hs]

/-- A queued client is not the holder. -/
theorem HolderIs.ne_of_mem {c : Config St Msg} (hi : Inv c) {h x : Pid} (hh : HolderIs h c)
    (hx : x ∈ queueOf c) : x ≠ h := by
  intro e
  subst e
  have := hi.holder_not_queued x _ (hh.srv hi)
  exact (List.count_eq_zero.mp this) hx

/-- A queued client has no grant in flight. -/
theorem HolderIs.g_queued {c : Config St Msg} (hi : Inv c) {h x : Pid} (hh : HolderIs h c)
    (hx : x ∈ queueOf c) : g c x = 0 :=
  (hi.nonholder (some h) _ (hh.srv hi) x (by simp [Ne.symm (hh.ne_of_mem hi hx)])).1

/-- The holder's token is in exactly one place. -/
theorem HolderIs.token {c : Config St Msg} (hi : Inv c) {h : Pid} (hh : HolderIs h c) :
    Has c h (.reply .ok) ∨ Holds h c ∨ Has c server (.release h) := by
  have := (hi.holder h _ (hh.srv hi)).1
  by_cases hg : g c h = 1
  · exact Or.inl (Has.of_mcount_pos (by unfold g at hg; omega))
  · by_cases hhd : hd c h = 1
    · exact Or.inr (Or.inl (hd_eq_one hhd))
    · exact Or.inr (Or.inr (Has.of_mcount_pos (by unfold r at *; omega)))

/-- A holder with its grant in flight is still blocked, and has no release
in flight. -/
theorem HolderIs.of_granted {c : Config St Msg} (hi : Inv c) {h : Pid} (hh : HolderIs h c)
    (hg : Has c h (.reply .ok)) : Waits h c ∧ c.mcount server (.release h) = 0 := by
  have old := hi.holder h _ (hh.srv hi)
  have hg' := hg.mcount_pos
  have hg1 : g c h = 1 := by have := old.1; unfold g at this ⊢; omega
  refine ⟨w_eq_one (old.2.1 hg1).1, ?_⟩
  have := hg.mcount_pos
  have := hd_le c h
  unfold g r at old
  omega

/-- A holder in the critical section has no release in flight. -/
theorem HolderIs.of_holds {c : Config St Msg} (hi : Inv c) {h : Pid} (hh : HolderIs h c)
    (hd' : Holds h c) : c.mcount server (.release h) = 0 := by
  have old := (hi.holder h _ (hh.srv hi)).1
  have := (w_hd_of_state hd').2
  simp at this
  unfold r at old
  omega

/-- The token argument for a blocked client: its request is in the server's
mailbox, or it is queued, or its grant is in its own mailbox. -/
theorem Waits.token {c : Config St Msg} (hi : Inv c) {x : Pid} (hx : Waits x c) :
    Has c server (.acquire x) ∨ x ∈ queueOf c ∨ Has c x (.reply .ok) := by
  obtain ⟨h0, q0, hs⟩ := hi.hasServer
  have hw : w c x = 1 := (w_hd_of_await hx).1
  have hq : queueOf c = q0 := by simp [queueOf, hs]
  have key : a c x + q0.count x = 1 ∨ g c x = 1 := by
    by_cases hhx : h0 = some x
    · subst hhx
      have old := hi.holder x q0 hs
      have hhd : hd c x = 0 := (w_hd_of_await hx).2
      omega
    · have := hi.nonholder h0 q0 hs x hhx
      omega
  rcases key with key | key
  · by_cases ha : a c x = 1
    · exact Or.inl (Has.of_mcount_pos (by unfold a at ha; omega))
    · right; left
      rw [hq]
      exact List.count_pos_iff.mp (by omega)
  · right; right
    exact Has.of_mcount_pos (by unfold g at key; omega)

/-- A non-empty queue has a holder. -/
theorem holder_of_queued {c : Config St Msg} (hi : Inv c) {x : Pid} (hx : x ∈ queueOf c) :
    ∃ h, HolderIs h c := by
  obtain ⟨h0, q0, hs⟩ := hi.hasServer
  cases h0 with
  | some h => exact ⟨h, by simp [HolderIs, holderOf, hs]⟩
  | none =>
    have := hi.queue_empty q0 hs
    subst this
    simp [queueOf, hs] at hx

/-! ## The server's step, seen from the holder -/

/-- While `h` holds, a step keeps `h` the holder and every queued client at
its rank, unless it is the server popping `release h`: then the lock is
freed (empty queue) or handed to the head of the queue, which is granted. -/
theorem HolderIs.step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    {h : Pid} (hh : HolderIs h a) :
    (HolderIs h b ∧ (∀ x ∈ queueOf a, x ∈ queueOf b ∧ rank (queueOf b) x = rank (queueOf a) x) ∧
      ¬ (p = server ∧ m = .release h) ∧ (p = server → (beh p s m).2 = [])) ∨
    (p = server ∧ m = .release h ∧
      ((queueOf a = [] ∧ holderOf b = none ∧ (beh p s m).2 = []) ∨
       ∃ y rest', queueOf a = y :: rest' ∧ HolderIs y b ∧ queueOf b = rest' ∧
         (beh p s m).2 = [(y, .reply .ok)])) := by
  by_cases hp : p = server
  · subst hp
    have hsa := hh.srv hi
    have hs : s = .lock (some h) (queueOf a) := by
      have := stateOf_of_get hget; rw [this] at hsa; exact Option.some.inj hsa
    subst hs
    have hb : b.stateOf server = some (beh server (.lock (some h) (queueOf a)) m).1 := by
      rw [hst]; simp
    cases m with
    | acquire y =>
      left
      refine ⟨by simp [HolderIs, holderOf, hb, beh], ?_, by simp, fun _ => by simp [beh]⟩
      intro x hx
      have hqb : queueOf b = queueOf a ++ [y] := by simp [queueOf, hb, beh]
      rw [hqb]
      exact ⟨List.mem_append_left _ hx, rank_append_of_mem hx _⟩
    | release y =>
      by_cases hy : y = h
      · subst hy
        right
        refine ⟨rfl, rfl, ?_⟩
        cases hq : queueOf a with
        | nil =>
          left
          rw [hq] at hb
          exact ⟨rfl, by simp [holderOf, hb, beh], by simp [beh]⟩
        | cons n rest' =>
          right
          rw [hq] at hb
          exact ⟨n, rest', rfl, by simp [HolderIs, holderOf, hb, beh], by simp [queueOf, hb, beh],
            by simp [beh]⟩
      · left
        refine ⟨by simp [HolderIs, holderOf, hb, beh, hy], ?_, by simp [hy], fun _ => by simp [beh, hy]⟩
        intro x hx
        have hqb : queueOf b = queueOf a := by simp [queueOf, hb, beh, hy]
        rw [hqb]
        exact ⟨hx, rfl⟩
    | reply r =>
      cases r
      left
      refine ⟨by simp [HolderIs, holderOf, hb, beh], ?_, by simp, fun _ => by simp [beh]⟩
      intro x hx
      have hqb : queueOf b = queueOf a := by simp [queueOf, hb, beh]
      rw [hqb]
      exact ⟨hx, rfl⟩
    | tick =>
      left
      refine ⟨by simp [HolderIs, holderOf, hb, beh], ?_, by simp, fun _ => by simp [beh]⟩
      intro x hx
      have hqb : queueOf b = queueOf a := by simp [queueOf, hb, beh]
      rw [hqb]
      exact ⟨hx, rfl⟩
  · left
    have hb : b.stateOf server = a.stateOf server := by rw [hst]; simp [Ne.symm hp]
    refine ⟨by unfold HolderIs holderOf at *; rw [hb]; exact hh, ?_, fun e => hp e.1, fun e => absurd e hp⟩
    intro x hx
    have hqb : queueOf b = queueOf a := by simp [queueOf, hb]
    rw [hqb]
    exact ⟨hx, rfl⟩

/-- `HolderIs.step` for a queued, blocked client `x`: `x` stays blocked; either
everything it cares about is unchanged, or the server hands over and `x` is
granted (it was the head) or moves up one rank. -/
theorem queued_step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {x h : Pid} (hx : Waits x a) (hq : x ∈ queueOf a) (hh : HolderIs h a) :
    (Waits x b ∧ x ∈ queueOf b ∧ rank (queueOf b) x = rank (queueOf a) x ∧ HolderIs h b ∧
      ¬ (p = server ∧ m = .release h) ∧ (p = server → (beh p s m).2 = [])) ∨
    (p = server ∧ m = .release h ∧ Waits x b ∧ ¬ HolderIs h b ∧
      (Has b x (.reply .ok) ∨ (x ∈ queueOf b ∧ rank (queueOf b) x + 1 = rank (queueOf a) x))) := by
  have hxb : Waits x b := by
    rcases Waits.step hget hst hx with ⟨hw, _⟩ | ⟨hp, hm, _⟩
    · exact hw
    · exfalso
      subst hp; subst hm
      have h0 := hh.g_queued hi hq
      have h1 := mcount_of_get hget (.reply .ok)
      unfold g at h0
      simp at h1
      omega
  rcases HolderIs.step hi hget hst hh with ⟨hhb, hrk, hnot, hsends⟩ | ⟨hp, hm, hcase⟩
  · left
    exact ⟨hxb, (hrk x hq).1, (hrk x hq).2, hhb, hnot, hsends⟩
  · right
    subst hp; subst hm
    refine ⟨rfl, rfl, hxb, ?_, ?_⟩
    · rcases hcase with ⟨_, hnone, _⟩ | ⟨y, rest', hqa, hyb, _, _⟩
      · unfold HolderIs; rw [hnone]; simp
      · intro hhb
        have := hh.ne_of_mem hi (by rw [hqa]; exact List.mem_cons_self)
        unfold HolderIs at hhb hyb
        rw [hhb] at hyb
        exact this (Option.some.inj hyb.symm)
    · rcases hcase with ⟨hqa, _, _⟩ | ⟨y, rest', hqa, hyb, hqb, hsends⟩
      · rw [hqa] at hq; simp at hq
      · rw [hqa] at hq
        by_cases hyx : y = x
        · have hyx' := hyx.symm
          subst hyx'
          left
          have hxs : x ≠ server := ne_server_of_await hi hx
          have hmbx := hmb x
          rw [hsends] at hmbx
          simp [hxs, sendsTo] at hmbx
          exact Has.of_send hx hmbx (by simp)
        · right
          rw [hqb, hqa]
          refine ⟨?_, ?_⟩
          · rcases List.mem_cons.mp hq with e | e
            · exact absurd e.symm hyx
            · exact e
          · simp [rank, hyx]

/-! ## Along a run -/

theorem _root_.Leanactors.ReachE.lockInv {a c : Config St Msg} (h : ReachE beh EnvStep a c) (hi : Inv a) : Inv c :=
  h.inv Inv.step Inv.env hi

/-! ## Phase 1: the request is in the server's mailbox -/

/-- A server step with `acquire x` still in its mailbox afterwards moved it
one place forward (it did not pop it: under `Inv` there is only one copy,
and the server never sends to itself). -/
theorem requested_srv_step {a b : Config St Msg} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get server = some ⟨s, m :: rest⟩)
    (hmb : ∀ q, b.mboxOf q = (if q = server then some rest else a.mboxOf q).map (· ++ sendsTo (beh server s m).2 q))
    {x : Pid} (hx : Waits x a) (hreq : Has a server (.acquire x)) (hreqb : Has b server (.acquire x)) :
    idxOf b server (.acquire x) < idxOf a server (.acquire x) := by
  have hmbs := hmb server
  simp at hmbs
  by_cases hm : m = .acquire x
  · exfalso
    subst hm
    obtain ⟨h0, q0, hsa⟩ := hi.hasServer
    have hs' : s = .lock h0 q0 := by
      have := stateOf_of_get hget; rw [this] at hsa; exact Option.some.inj hsa
    subst hs'
    have hxs : x ≠ server := ne_server_of_await hi hx
    have hcnt := mcount_of_get hget (.acquire x)
    have hle := hi.a_le_one x
    unfold Lock.a at hle
    simp at hcnt
    have hrest : rest.count (.acquire x) = 0 := by omega
    have hsend : sendsTo (beh server (.lock h0 q0) (.acquire x)).2 server = [] := by
      cases h0 <;> simp [beh, sendsTo, hxs]
    rw [hsend, List.append_nil] at hmbs
    obtain ⟨mb, hmb', hm'⟩ := hreqb
    rw [hmbs] at hmb'
    have := Option.some.inj hmb'
    subst this
    exact (List.count_eq_zero.mp hrest) hm'
  · have := (Has.pop hget hmbs hreq hm).2
    omega

/-- **Phase 1.** A blocked client whose `acquire` is in the server's mailbox
is eventually queued or granted (fairness of the server). -/
theorem requested_leadsTo (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0))
    (hfair : ρ.WeakFair (.run server)) (x : Pid) :
    LeadsTo ρ.st (fun c => Waits x c ∧ Has c server (.acquire x))
      (fun c => Waits x c ∧ (x ∈ queueOf c ∨ Has c x (.reply .ok))) := by
  apply ρ.rank_leads_to_run server (fun c => idxOf c server (.acquire x)) hfair
  · intro a b hr hs ⟨hx, hreq⟩ hnq
    have hi := hr.lockInv hi0
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    have hxb : Waits x b := by
      rcases Waits.step hget hst hx with ⟨hw, _⟩ | ⟨hp, hm, _⟩
      · exact hw
      · exfalso
        subst hp; subst hm
        exact hnq ⟨hx, Or.inr ⟨_, mboxOf_of_get hget, List.mem_cons_self⟩⟩
    by_cases hps : p = server
    · subst hps
      obtain ⟨h0, q0, hsa⟩ := hi.hasServer
      have hs' : s = .lock h0 q0 := by
        have := stateOf_of_get hget; rw [this] at hsa; exact Option.some.inj hsa
      subst hs'
      have hb : b.stateOf server = some (beh server (.lock h0 q0) m).1 := by rw [hst]; simp
      by_cases hm : m = .acquire x
      · subst hm
        right
        refine ⟨hxb, ?_⟩
        cases h0 with
        | none =>
          right
          have hxs : x ≠ server := ne_server_of_await hi hx
          have hmbx := hmb x
          simp [beh, hxs, sendsTo] at hmbx
          exact Has.of_send hx hmbx (by simp)
        | some h =>
          left
          simp [queueOf, hb, beh]
      · left
        refine ⟨hxb, ?_⟩
        have hmbs := hmb server
        simp at hmbs
        exact (Has.pop hget hmbs hreq hm).1
    · left
      refine ⟨hxb, ?_⟩
      have hmbs := hmb server
      simp [Ne.symm hps] at hmbs
      exact (Has.append hmbs hreq).1
  · intro a b _ he ⟨hx, hreq⟩ _
    obtain ⟨p, hst, hmb, _, _⟩ := he.facts
    left
    exact ⟨by unfold Waits at *; rw [hst]; exact hx, (Has.append (hmb server) hreq).1⟩
  · intro ch a b hr hstep ⟨hx, hreq⟩ _ ⟨_, hreqb⟩
    have hi := hr.lockInv hi0
    cases ch with
    | env =>
      cases hstep with
      | env _ _ he =>
        obtain ⟨p, _, hmb, _, _⟩ := he.facts
        exact Nat.le_of_eq (Has.append (hmb server) hreq).2
    | run p =>
      obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
      by_cases hps : p = server
      · subst hps
        exact Nat.le_of_lt (requested_srv_step hi hget hmb hx hreq hreqb)
      · have hmbs := hmb server
        simp [Ne.symm hps] at hmbs
        exact Nat.le_of_eq (Has.append hmbs hreq).2
  · intro a _ ⟨_, hreq⟩ _
    exact hreq.enabled
  · intro a b hr hstep ⟨hx, hreq⟩ _ ⟨_, hreqb⟩
    have hi := hr.lockInv hi0
    obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
    exact requested_srv_step hi hget hmb hx hreq hreqb

/-! ## Phase 3: the grant is in the client's mailbox -/

/-- A step while `x` is blocked with its grant in flight, after which the
grant is still in flight: the grant moved forward if `x` stepped (it
deferred the head), and stayed put otherwise. -/
theorem granted_run {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {x : Pid} (hx : Waits x a) (hg : Has a x (.reply .ok)) (hgb : Has b x (.reply .ok)) :
    idxOf b x (.reply .ok) ≤ idxOf a x (.reply .ok) ∧
      (p = x → idxOf b x (.reply .ok) < idxOf a x (.reply .ok)) := by
  by_cases hpx : p = x
  · subst hpx
    have hs : s = .client_await0 := by
      have := stateOf_of_get hget; unfold Waits at hx; rw [this] at hx; exact Option.some.inj hx
    subst hs
    have hmbx := hmb p
    simp at hmbx
    by_cases hm : m = .reply .ok
    · exfalso
      subst hm
      have hcnt := mcount_of_get hget (.reply .ok)
      have hle := hi.g_le_one p
      unfold g at hle
      simp at hcnt
      have hrest : rest.count (.reply .ok) = 0 := by omega
      simp [beh, sendsTo] at hmbx
      obtain ⟨mb, hmb', hm'⟩ := hgb
      rw [hmbx] at hmb'
      have := Option.some.inj hmb'
      subst this
      exact (List.count_eq_zero.mp hrest) hm'
    · have := (Has.pop hget hmbx hg hm).2
      exact ⟨by omega, fun _ => by omega⟩
  · have hmbx := hmb x
    simp [Ne.symm hpx] at hmbx
    have := (Has.append hmbx hg).2
    exact ⟨Nat.le_of_eq this, fun e => absurd e hpx⟩

/-- **Phase 3.** A blocked client with its grant in flight eventually holds
the lock (fairness of the client): everything ahead of the grant is deferred
by re-enqueueing, so the grant reaches the head. -/
theorem granted_leadsTo_holds (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0)) {x : Pid}
    (hfair : ρ.WeakFair (.run x)) :
    LeadsTo ρ.st (fun c => Waits x c ∧ Has c x (.reply .ok)) (Holds x) := by
  apply ρ.rank_leads_to_run x (fun c => idxOf c x (.reply .ok)) hfair
  · intro a b _ hs ⟨hx, hg⟩ _
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    rcases Waits.step hget hst hx with ⟨hw, hne⟩ | ⟨_, _, hh⟩
    · left
      refine ⟨hw, ?_⟩
      by_cases hpx : p = x
      · subst hpx
        have hmbx := hmb p
        simp at hmbx
        exact (Has.pop hget hmbx hg (hne rfl)).1
      · have hmbx := hmb x
        simp [Ne.symm hpx] at hmbx
        exact (Has.append hmbx hg).1
    · right; exact hh
  · intro a b _ he ⟨hx, hg⟩ _
    obtain ⟨p, hst, hmb, _, _⟩ := he.facts
    left
    exact ⟨by unfold Waits at *; rw [hst]; exact hx, (Has.append (hmb x) hg).1⟩
  · intro ch a b hr hstep ⟨hx, hg⟩ _ ⟨_, hgb⟩
    have hi := hr.lockInv hi0
    cases ch with
    | env =>
      cases hstep with
      | env _ _ he =>
        obtain ⟨p, _, hmb, _, _⟩ := he.facts
        exact Nat.le_of_eq (Has.append (hmb x) hg).2
    | run p =>
      obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
      exact (granted_run hi hget hmb hx hg hgb).1
  · intro a _ ⟨_, hg⟩ _
    exact hg.enabled
  · intro a b hr hstep ⟨hx, hg⟩ _ ⟨_, hgb⟩
    have hi := hr.lockInv hi0
    obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
    exact (granted_run hi hget hmb hx hg hgb).2 rfl

/-! ## Phase 2: queued

While `x` is queued at rank `n` some `h ≠ x` holds the lock. `R x n` is the
phase, `G x n` its exit: `x` granted, or still queued at a smaller rank. The
four lemmas below drive the holder's token around the protocol (grant in
flight, holding, ticked, release in flight); the handover then exits the
phase (`queued_step`). -/

def Queued (x : Pid) (c : Config St Msg) : Prop := Waits x c ∧ x ∈ queueOf c
def Granted (x : Pid) (c : Config St Msg) : Prop := Waits x c ∧ Has c x (.reply .ok)
def R (x : Pid) (n : Nat) (c : Config St Msg) : Prop := Queued x c ∧ rank (queueOf c) x = n
def G (x : Pid) (n : Nat) (c : Config St Msg) : Prop :=
  Granted x c ∨ (Queued x c ∧ rank (queueOf c) x < n)

/-- `queued_step` phrased with `R`/`G`. -/
theorem R.step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {x h : Pid} {n : Nat} (hr : R x n a) (hh : HolderIs h a) :
    (R x n b ∧ HolderIs h b ∧ ¬ (p = server ∧ m = .release h) ∧ (p = server → (beh p s m).2 = [])) ∨
    (p = server ∧ m = .release h ∧ ¬ HolderIs h b ∧ G x n b) := by
  obtain ⟨⟨hx, hq⟩, hrk⟩ := hr
  rcases queued_step hi hget hst hmb hx hq hh with ⟨hxb, hqb, hrkb, hhb, hnot, hsends⟩ | ⟨hp, hm, hxb, hhb, hcase⟩
  · left
    exact ⟨⟨⟨hxb, hqb⟩, by rw [hrkb, hrk]⟩, hhb, hnot, hsends⟩
  · right
    refine ⟨hp, hm, hhb, ?_⟩
    rcases hcase with hg | ⟨hqb, hrkb⟩
    · exact Or.inl ⟨hxb, hg⟩
    · exact Or.inr ⟨⟨hxb, hqb⟩, by omega⟩

theorem R.env {a b : Config St Msg} (he : EnvStep a b) {x h : Pid} {n : Nat}
    (hr : R x n a) (hh : HolderIs h a) : R x n b ∧ HolderIs h b := by
  obtain ⟨p, hst, _, hho, hqu⟩ := he.facts
  obtain ⟨⟨hx, hq⟩, hrk⟩ := hr
  exact ⟨⟨⟨by unfold Waits at *; rw [hst]; exact hx, by rw [hqu]; exact hq⟩, by rw [hqu]; exact hrk⟩,
    by unfold HolderIs at *; rw [hho]; exact hh⟩

/-- A holding client that goes idle sends `release` to the server. -/
theorem released_of_tick {a b : Config St Msg} {h : Pid} {rest : List Msg}
    (hi : Inv a) (hh : HolderIs h a) (hhd : Holds h a)
    (hmb : ∀ q, b.mboxOf q = (if q = h then some rest else a.mboxOf q).map
      (· ++ sendsTo (beh h (.client .holding) .tick).2 q)) :
    Has b server (.release h) := by
  have hhs : h ≠ server := ne_server_of_cli hi hhd
  have hmbs := hmb server
  simp [Ne.symm hhs, beh, sendsTo] at hmbs
  exact Has.of_send (hh.srv hi) hmbs (by simp)

/-- **Phase 2a.** The holder's grant is in flight: the holder (blocked, with
`reply ok` somewhere in its mailbox) eventually pops it and holds. -/
theorem holder_granted_leadsTo (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0)) {h : Pid}
    (hfair : ρ.WeakFair (.run h)) (x : Pid) (n : Nat) :
    LeadsTo ρ.st (fun c => R x n c ∧ HolderIs h c ∧ Has c h (.reply .ok))
      (fun c => R x n c ∧ HolderIs h c ∧ Holds h c) := by
  apply ρ.rank_leads_to_run h (fun c => idxOf c h (.reply .ok)) hfair
  · intro a b hr hs ⟨hR, hh, hg⟩ _
    have hi := hr.lockInv hi0
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    rcases R.step hi hget hst hmb hR hh with ⟨hRb, hhb, _, _⟩ | ⟨hp, hm, _, _⟩
    · have hwh := (hh.of_granted hi hg).1
      by_cases hph : p = h
      · subst hph
        rcases Waits.step hget hst hwh with ⟨_, hne⟩ | ⟨_, _, hhd⟩
        · left
          have hmbh := hmb p
          simp at hmbh
          exact ⟨hRb, hhb, (Has.pop hget hmbh hg (hne rfl)).1⟩
        · right
          exact ⟨hRb, hhb, hhd⟩
      · left
        have hmbh := hmb h
        simp [Ne.symm hph] at hmbh
        exact ⟨hRb, hhb, (Has.append hmbh hg).1⟩
    · exfalso
      subst hp; subst hm
      have h0 := (hh.of_granted hi hg).2
      have h1 := mcount_of_get hget (.release h)
      simp at h1
      omega
  · intro a b _ he ⟨hR, hh, hg⟩ _
    obtain ⟨hRb, hhb⟩ := R.env he hR hh
    obtain ⟨p, _, hmb, _, _⟩ := he.facts
    exact Or.inl ⟨hRb, hhb, (Has.append (hmb h) hg).1⟩
  · intro ch a b hr hstep ⟨_, hh, hg⟩ _ ⟨_, _, hgb⟩
    have hi := hr.lockInv hi0
    cases ch with
    | env =>
      cases hstep with
      | env _ _ he =>
        obtain ⟨p, _, hmb, _, _⟩ := he.facts
        exact Nat.le_of_eq (Has.append (hmb h) hg).2
    | run p =>
      obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
      exact (granted_run hi hget hmb (hh.of_granted hi hg).1 hg hgb).1
  · intro a _ ⟨_, _, hg⟩ _
    exact hg.enabled
  · intro a b hr hstep ⟨_, hh, hg⟩ _ ⟨_, _, hgb⟩
    have hi := hr.lockInv hi0
    obtain ⟨s, m, rest, hget, _, hmb⟩ := hstep.run_facts
    exact (granted_run hi hget hmb (hh.of_granted hi hg).1 hg hgb).2 rfl

/-- The holder is in the critical section: a step keeps it there (and keeps
`x` queued at its rank) unless it is the holder popping a `tick`, in which
case its `release` is now in the server's mailbox. -/
theorem holder_holds_step {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {x h : Pid} {n : Nat} (hR : R x n a) (hh : HolderIs h a) (hhd : Holds h a) :
    (R x n b ∧ HolderIs h b ∧ Holds h b ∧ (p = h → m ≠ .tick ∧ (beh p s m).2 = [])) ∨
    (p = h ∧ m = .tick ∧ R x n b ∧ HolderIs h b ∧ Has b server (.release h)) := by
  rcases R.step hi hget hst hmb hR hh with ⟨hRb, hhb, _, _⟩ | ⟨hp, hm, _, _⟩
  · rcases Holds.step hget hst hhd with ⟨hhdb, hne⟩ | ⟨hp, hm, hs, _⟩
    · exact Or.inl ⟨hRb, hhb, hhdb, hne⟩
    · right
      subst hp; subst hm; subst hs
      exact ⟨rfl, rfl, hRb, hhb, released_of_tick hi hh hhd hmb⟩
  · exfalso
    subst hp; subst hm
    have h0 := hh.of_holds hi hhd
    have h1 := mcount_of_get hget (.release h)
    simp at h1
    omega

/-- **Phase 2b.** The holder is in the critical section: the environment
eventually ticks it (or it has already been ticked and released). -/
theorem holder_holds_leadsTo (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0)) {h : Pid}
    (henv : ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)) (x : Pid) (n : Nat) :
    LeadsTo ρ.st (fun c => R x n c ∧ HolderIs h c ∧ Holds h c)
      (fun c => (R x n c ∧ HolderIs h c ∧ Holds h c ∧ Has c h .tick) ∨
        (R x n c ∧ HolderIs h c ∧ Has c server (.release h))) := by
  apply ρ.stable_until_env henv
  · intro a b hr hs ⟨hR, hh, hhd⟩ _
    have hi := hr.lockInv hi0
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    rcases holder_holds_step hi hget hst hmb hR hh hhd with ⟨hRb, hhb, hhdb, _⟩ | ⟨_, _, hRb, hhb, hrel⟩
    · exact Or.inl ⟨hRb, hhb, hhdb⟩
    · exact Or.inr (Or.inr ⟨hRb, hhb, hrel⟩)
  · intro a b _ he ⟨hR, hh, hhd⟩ _
    obtain ⟨hRb, hhb⟩ := R.env he hR hh
    obtain ⟨p, hst, _, _, _⟩ := he.facts
    exact Or.inl ⟨hRb, hhb, by unfold Holds at *; rw [hst]; exact hhd⟩
  · intro a _ ⟨_, _, hhd⟩ _
    exact hhd
  · intro a b _ he heq ⟨hR, hh, hhd⟩ _
    obtain ⟨hRb, hhb⟩ := R.env he hR hh
    subst heq
    left
    refine ⟨hRb, hhb, by unfold Holds at *; rw [stateOf_deliver]; exact hhd, ?_⟩
    have hmbh := mboxOf_deliver_eq a h h .tick
    simp at hmbh
    exact Has.of_send hhd hmbh (by simp)

/-- A step while the holder is in the critical section with a `tick` in its
mailbox, after which it still is: the tick moved forward if the holder
stepped (it ignored the head), and stayed put otherwise. -/
theorem ticked_run {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {h : Pid} (hhd : Holds h a) (ht : Has a h .tick) (hhdb : Holds h b) :
    idxOf b h .tick ≤ idxOf a h .tick ∧ (p = h → idxOf b h .tick < idxOf a h .tick) := by
  by_cases hph : p = h
  · subst hph
    rcases Holds.step hget hst hhd with ⟨_, hne⟩ | ⟨_, _, _, hidle⟩
    · have hmbh := hmb p
      simp at hmbh
      have := (Has.pop hget hmbh ht (hne rfl).1).2
      exact ⟨by omega, fun _ => by omega⟩
    · exfalso
      unfold Holds at hhdb
      rw [hidle] at hhdb
      cases hhdb
  · have hmbh := hmb h
    simp [Ne.symm hph] at hmbh
    have := (Has.append hmbh ht).2
    exact ⟨Nat.le_of_eq this, fun e => absurd e hph⟩

/-- **Phase 2c.** The holder has been ticked: it eventually pops the tick
(fairness of the holder) and its `release` is in the server's mailbox. -/
theorem holder_ticked_leadsTo (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0)) {h : Pid}
    (hfair : ρ.WeakFair (.run h)) (x : Pid) (n : Nat) :
    LeadsTo ρ.st (fun c => R x n c ∧ HolderIs h c ∧ Holds h c ∧ Has c h .tick)
      (fun c => R x n c ∧ HolderIs h c ∧ Has c server (.release h)) := by
  apply ρ.rank_leads_to_run h (fun c => idxOf c h .tick) hfair
  · intro a b hr hs ⟨hR, hh, hhd, ht⟩ _
    have hi := hr.lockInv hi0
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    rcases holder_holds_step hi hget hst hmb hR hh hhd with ⟨hRb, hhb, hhdb, hne⟩ | ⟨_, _, hRb, hhb, hrel⟩
    · left
      refine ⟨hRb, hhb, hhdb, ?_⟩
      by_cases hph : p = h
      · subst hph
        have hmbh := hmb p
        simp at hmbh
        exact (Has.pop hget hmbh ht (hne rfl).1).1
      · have hmbh := hmb h
        simp [Ne.symm hph] at hmbh
        exact (Has.append hmbh ht).1
    · exact Or.inr ⟨hRb, hhb, hrel⟩
  · intro a b _ he ⟨hR, hh, hhd, ht⟩ _
    obtain ⟨hRb, hhb⟩ := R.env he hR hh
    obtain ⟨p, hst, hmb, _, _⟩ := he.facts
    exact Or.inl ⟨hRb, hhb, by unfold Holds at *; rw [hst]; exact hhd, (Has.append (hmb h) ht).1⟩
  · intro ch a b _ hstep ⟨_, _, hhd, ht⟩ _ ⟨_, _, hhdb, _⟩
    cases ch with
    | env =>
      cases hstep with
      | env _ _ he =>
        obtain ⟨p, _, hmb, _, _⟩ := he.facts
        exact Nat.le_of_eq (Has.append (hmb h) ht).2
    | run p =>
      obtain ⟨s, m, rest, hget, hst, hmb⟩ := hstep.run_facts
      exact (ticked_run hget hst hmb hhd ht hhdb).1
  · intro a _ ⟨_, _, _, ht⟩ _
    exact ht.enabled
  · intro a b _ hstep ⟨_, _, hhd, ht⟩ _ ⟨_, _, hhdb, _⟩
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hstep.run_facts
    exact (ticked_run hget hst hmb hhd ht hhdb).2 rfl

/-- A step while the holder's `release` is in the server's mailbox, after
which `h` still holds: the release moved forward if the server stepped (it
popped something else), and stayed put otherwise. -/
theorem released_run {a b : Config St Msg} {p : Pid} {s : St} {m : Msg} {rest : List Msg}
    (hi : Inv a) (hget : a.get p = some ⟨s, m :: rest⟩)
    (hst : ∀ q, b.stateOf q = if q = p then some (beh p s m).1 else a.stateOf q)
    (hmb : ∀ q, b.mboxOf q = (if q = p then some rest else a.mboxOf q).map (· ++ sendsTo (beh p s m).2 q))
    {x h : Pid} {n : Nat} (hR : R x n a) (hh : HolderIs h a) (hrel : Has a server (.release h))
    (hhb : HolderIs h b) :
    idxOf b server (.release h) ≤ idxOf a server (.release h) ∧
      (p = server → idxOf b server (.release h) < idxOf a server (.release h)) := by
  rcases R.step hi hget hst hmb hR hh with ⟨_, _, hnot, _⟩ | ⟨_, _, hnhb, _⟩
  · by_cases hps : p = server
    · subst hps
      have hmbs := hmb server
      simp at hmbs
      have := (Has.pop hget hmbs hrel (fun e => hnot ⟨rfl, e⟩)).2
      exact ⟨by omega, fun _ => by omega⟩
    · have hmbs := hmb server
      simp [Ne.symm hps] at hmbs
      have := (Has.append hmbs hrel).2
      exact ⟨Nat.le_of_eq this, fun e => absurd e hps⟩
  · exact absurd hhb hnhb

/-- **Phase 2d.** The holder's `release` is in the server's mailbox: the
server eventually pops it (fairness of the server) and hands the lock over,
granting `x` or moving it up one rank. -/
theorem holder_released_leadsTo (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0))
    (hfair : ρ.WeakFair (.run server)) (x h : Pid) (n : Nat) :
    LeadsTo ρ.st (fun c => R x n c ∧ HolderIs h c ∧ Has c server (.release h)) (G x n) := by
  apply ρ.rank_leads_to_run server (fun c => idxOf c server (.release h)) hfair
  · intro a b hr hs ⟨hR, hh, hrel⟩ _
    have hi := hr.lockInv hi0
    obtain ⟨p, hp⟩ := hs.exists_cStepL EnvStep
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hp.run_facts
    rcases R.step hi hget hst hmb hR hh with ⟨hRb, hhb, hnot, _⟩ | ⟨_, _, _, hG⟩
    · left
      refine ⟨hRb, hhb, ?_⟩
      by_cases hps : p = server
      · subst hps
        have hmbs := hmb server
        simp at hmbs
        exact (Has.pop hget hmbs hrel (fun e => hnot ⟨rfl, e⟩)).1
      · have hmbs := hmb server
        simp [Ne.symm hps] at hmbs
        exact (Has.append hmbs hrel).1
    · exact Or.inr hG
  · intro a b _ he ⟨hR, hh, hrel⟩ _
    obtain ⟨hRb, hhb⟩ := R.env he hR hh
    obtain ⟨p, _, hmb, _, _⟩ := he.facts
    exact Or.inl ⟨hRb, hhb, (Has.append (hmb server) hrel).1⟩
  · intro ch a b hr hstep ⟨hR, hh, hrel⟩ _ ⟨_, hhb, _⟩
    have hi := hr.lockInv hi0
    cases ch with
    | env =>
      cases hstep with
      | env _ _ he =>
        obtain ⟨p, _, hmb, _, _⟩ := he.facts
        exact Nat.le_of_eq (Has.append (hmb server) hrel).2
    | run p =>
      obtain ⟨s, m, rest, hget, hst, hmb⟩ := hstep.run_facts
      exact (released_run hi hget hst hmb hR hh hrel hhb).1
  · intro a _ ⟨_, _, hrel⟩ _
    exact hrel.enabled
  · intro a b hr hstep ⟨hR, hh, hrel⟩ _ ⟨_, hhb, _⟩
    have hi := hr.lockInv hi0
    obtain ⟨s, m, rest, hget, hst, hmb⟩ := hstep.run_facts
    exact (released_run hi hget hst hmb hR hh hrel hhb).2 rfl

/-- **Phase 2, one rank.** From rank `n`, `x` is granted or reaches a smaller
rank: find the holder, locate its token, and chain 2a-2d. -/
theorem R_leadsTo_G (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0))
    (hfair : ∀ p, ρ.WeakFair (.run p))
    (henv : ∀ h, ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)) (x : Pid) (n : Nat) :
    LeadsTo ρ.st (R x n) (G x n) := by
  intro t hR
  have hi := (ρ.reach t).lockInv hi0
  obtain ⟨h, hh⟩ := holder_of_queued hi hR.1.2
  have L1 := holder_granted_leadsTo ρ hi0 (hfair h) x n
  have L2 := holder_holds_leadsTo ρ hi0 (henv h) x n
  have L3 := holder_ticked_leadsTo ρ hi0 (hfair h) x n
  have L4 := holder_released_leadsTo ρ hi0 (hfair server) x h n
  have L2' := L2.trans ((L3.trans L4).or L4)
  rcases hh.token hi with hg | hhd | hrel
  · exact (L1.trans L2') t ⟨hR, hh, hg⟩
  · exact L2' t ⟨hR, hh, hhd⟩
  · exact L4 t ⟨hR, hh, hrel⟩

/-- **Phase 2.** A queued client is eventually granted: rank induction on
its position in the queue. -/
theorem queued_leadsTo_granted (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0))
    (hfair : ∀ p, ρ.WeakFair (.run p))
    (henv : ∀ h, ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)) (x : Pid) :
    LeadsTo ρ.st (Queued x) (Granted x) :=
  LeadsTo.rank_induction (fun c => rank (queueOf c) x) (fun n => R_leadsTo_G ρ hi0 hfair henv x n)

/-! ## The theorem -/

/-- A blocked client eventually holds the lock: locate its token
(`Waits.token`) and chain the phases. -/
theorem waits_leadsTo_holds (ρ : CRun beh EnvStep) (hi0 : Inv (ρ.st 0))
    (hfair : ∀ p, ρ.WeakFair (.run p))
    (henv : ∀ h, ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)) (x : Pid) :
    LeadsTo ρ.st (Waits x) (Holds x) := by
  intro t hx
  have hi := (ρ.reach t).lockInv hi0
  have LA := requested_leadsTo ρ hi0 (hfair server) x
  have LB := queued_leadsTo_granted ρ hi0 hfair henv x
  have LC := granted_leadsTo_holds ρ hi0 (hfair x)
  have LBC : LeadsTo ρ.st (fun c => Waits x c ∧ (x ∈ queueOf c ∨ Has c x (.reply .ok))) (Holds x) := by
    refine (LeadsTo.mono (P := fun c => Queued x c ∨ Granted x c) ?_ (fun _ h => h)
      (LB.or (LeadsTo.refl _ _))).trans LC
    intro c ⟨hw, h⟩
    rcases h with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  rcases hx.token hi with hreq | hq | hg
  · exact (LA.trans LBC) t ⟨hx, hreq⟩
  · exact (LB.trans LC) t ⟨hx, hq⟩
  · exact LC t ⟨hx, hg⟩

/-- **Lock liveness.** Along any run of the lock system from `initCfg n`
(actor steps and environment ticks in any order) in which every actor is
scheduled weakly fairly and a client that keeps holding the lock is
eventually ticked, a client blocked in `GenServer.call(Lock, :acquire)`
eventually holds the lock. -/
theorem eventually_holds (n : Nat) (ρ : CRun beh EnvStep) (h0 : ρ.st 0 = initCfg n)
    (hfair : ∀ p, ρ.WeakFair (.run p))
    (henv : ∀ h, ρ.EnvFair (Holds h) (fun a b => b = a.deliver h .tick)) :
    ∀ t x, (ρ.st t).stateOf x = some .client_await0 →
      ∃ t' ≥ t, (ρ.st t').stateOf x = some (.client .holding) :=
  fun t x hx => waits_leadsTo_holds ρ (h0 ▸ initCfg_inv n) hfair henv x t hx

end Leanactors.Examples.Lock
