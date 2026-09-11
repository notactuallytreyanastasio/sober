import Leanactors.Fair
import Leanactors.Examples.SupervisorLive
import Leanactors.Examples.WatchdogProof
/-!
# Leanactors.Examples.WatchdogLive

**Liveness of the watchdog.** Two theorems along fair `SysRun`s, both
from any `Good` system (the safety invariant `Inv`, no pending kill aimed
at the watchdog, `ChildNe`, and two further invariants introduced here:
`Armed`, a watchdog that expects a pong has its timeout pending or already
in its mailbox, and `ChildLt`, the current worker's pid is below the fresh
counter).

* `restart_eventually`: the supervisor's statement for the watchdog. Under
  weak fairness of `signal` and of `run 0`, a dead current worker is
  eventually replaced by a live one. Same two `rank_leads_to` stages as
  `SupervisorLive` (position of the pending signal in the FIFO signal
  queue, then position of the `EXIT` in the watchdog's mailbox); the only
  new work is `dog_run_cases`, since a `run 0` step that is not a restart
  may still send a ping, re-arm the timer, or queue the kill.

* `worker_replaced` (and its corollary `hung_worker_replaced`): the
  timer-driven property. If at time `t` the watchdog is `.watchdog (some
  w) true` (it has pinged `w` and is waiting for the pong or the timeout),
  then under fairness of the timeout timer, of `run 0` and of `signal`, at
  some `t' ≥ t` the current worker is a live pid other than `w`. Nothing is
  assumed about `w` itself: it may be hung, healthy or already dead, and
  no fairness of `run w` is needed (the kill is untrappable and does not
  need the worker to run). Timers are untimed, so this is exactly the
  over-approximation of `Watchdog.lean`: a fair run kills every worker
  eventually, healthy or not.

**Timer fairness.** Timers live in a list whose indices shift when an
earlier timer fires, so `WeakFair (.timer i)` for a fixed `i` is not the
right assumption. `SysRun.TimerFair to m` says: if a timer `(to, m)` is
pending from some time on, some timer step that fires a `(to, m)` timer is
eventually taken. It is derived from `∀ i, ρ.WeakFair (.timer i)`
(`SysRun.timerFair_of_weakFair_timers`): the index of the first `(to, m)`
timer never increases (steps only append to `timers`, and a firing removes
one index), so it stabilises at some `j`, and weak fairness of `timer j`
then fires it. `worker_replaced` takes `TimerFair 0 .timeout`;
`worker_replaced_of_weakFair` takes the `∀ i` form.

**The chain** for `worker_replaced`, each stage a `LeadsTo`:

* Stage 0 (`waiting_leadsTo`, `SysRun.stable_until_timer` on `TimerFair`):
  from `.watchdog (some w) true`, `Armed` keeps the timeout pending until
  it fires, and firing puts `.timeout` in the mailbox (`TimeoutInbox`),
  unless a restart happens first (`Replaced`) or the timeout was already
  there.
* Stage 1 (`timeoutInbox_leadsTo`, `rank_leads_to_of_step` on `run 0`,
  rank the position of the first `.timeout` in the mailbox): pongs and
  other messages ahead of it are popped one by one; the watchdog stays
  `(some w) true` while doing so (a pong re-pings and re-arms), and popping
  the timeout queues the kill (`KillPending`).
* Stage 2 (`killPending_leadsTo`, `rank_leads_to_of_step` on `signal`,
  rank the position of `(w, 0, .kill)` in the signal queue): the kill is
  delivered and `w` is dead (`Dead`; `kill_head_dead` covers both a live
  `w`, killed whatever it traps, and a `w` that was already gone).
* Stage 3 (`dead_leadsTo`): `restart_eventually` from the dead worker
  gives a live worker, which is not `w` because `w` stays dead
  (`SysReach.stateOf_none`, which needs `w < next`: `ChildLt`).

**Non-vacuity.** `dead_worker_reachable` exhibits a closed-reachable
system with a dead current worker (start, timer fires, kill, kill
delivered); `hung` is an environment-reachable one with a hung worker and
the watchdog waiting (`hung_worker_reachable`: start, `hang` to the
worker, the worker pongs then hangs, the watchdog re-pings). From `hung`
there is a run that is weakly fair for `signal`, `run 0`, every `timer i`
and `run 1` (`hung_fair_run`), so the hypotheses of both theorems are
jointly satisfiable on a reachable start. The run cycles timer, run 0,
signal, signal, run 0 forever, killing worker `k` and spawning `k + 1`
each time; it is built by `SysRun.exists_of_inv` from the phase invariant
`Cyc` (the exact shape of the system at each of the five phases, with
`next = k + 1`) and the one-phase lemma `cyc_step`, so no state of the run
is ever written down. Worker 1 dies in the first cycle and is never
resurrected, which is what makes `run 1` fair (disabled from time 3 on).
-/

set_option linter.unusedSimpArgs false

namespace Leanactors

/-! ## Two more list facts -/

theorem List.mem_eraseIdx_of_ne {α : Type} {l : List α} {i : Nat} {x y : α}
    (hx : x ∈ l) (hy : l[i]? = some y) (hne : y ≠ x) : x ∈ l.eraseIdx i := by
  induction l generalizing i with
  | nil => cases hx
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      rw [List.eraseIdx_cons_zero]
      rcases List.mem_cons.mp hx with rfl | h
      · exact absurd rfl hne
      · exact h
    | succ i =>
      rw [List.eraseIdx_cons_succ]
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h (by simpa using hy))

/-- Removing an index other than the first hit does not move the first hit
later. -/
theorem List.findIdx_eraseIdx_le {α : Type} {p : α → Bool} {l : List α} {i : Nat}
    (hi : i ≠ l.findIdx p) (hex : ∃ x ∈ l, p x = true) :
    (l.eraseIdx i).findIdx p ≤ l.findIdx p := by
  induction l generalizing i with
  | nil => obtain ⟨x, hx, _⟩ := hex; cases hx
  | cons a l ih =>
    cases i with
    | zero =>
      rw [List.eraseIdx_cons_zero]
      cases hpa : p a with
      | true => exact absurd (by rw [List.findIdx_cons, hpa, cond_true]) hi
      | false => rw [List.findIdx_cons, hpa, cond_false]; exact Nat.le_succ _
    | succ i =>
      rw [List.eraseIdx_cons_succ, List.findIdx_cons, List.findIdx_cons]
      cases hpa : p a with
      | true => simp
      | false =>
        simp only [cond_false]
        apply Nat.succ_le_succ
        apply ih
        · intro h; apply hi; rw [List.findIdx_cons, hpa, cond_false, h]
        · obtain ⟨x, hx, hpx⟩ := hex
          rcases List.mem_cons.mp hx with rfl | hx'
          · rw [hpa] at hpx; cases hpx
          · exact ⟨x, hx', hpx⟩

/-- A non-increasing `Nat` sequence is eventually constant. -/
theorem exists_stable_of_nonincreasing (f : Nat → Nat) (t : Nat) (h : ∀ u ≥ t, f (u+1) ≤ f u) :
    ∃ t0 ≥ t, ∀ u ≥ t0, f u = f t0 := by
  have hle : ∀ t, (∀ u ≥ t, f (u+1) ≤ f u) → ∀ u ≥ t, f u ≤ f t := by
    intro t h u hu
    have : ∀ d, f (t + d) ≤ f t := by
      intro d
      induction d with
      | zero => exact Nat.le_refl _
      | succ d ih => exact Nat.le_trans (h (t + d) (Nat.le_add_right _ _)) ih
    have := this (u - t)
    rwa [Nat.add_sub_of_le hu] at this
  suffices ∀ k t, f t ≤ k → (∀ u ≥ t, f (u+1) ≤ f u) → ∃ t0 ≥ t, ∀ u ≥ t0, f u = f t0 from
    this _ t (Nat.le_refl _) h
  intro k
  induction k with
  | zero =>
    intro t hk h
    refine ⟨t, Nat.le_refl _, fun u hu => ?_⟩
    have := hle t h u hu
    omega
  | succ k ih =>
    intro t hk h
    by_cases hlt : ∃ u ≥ t, f u < f t
    · obtain ⟨u, hu, hfu⟩ := hlt
      obtain ⟨t0, ht0, hst⟩ := ih u (by omega) (fun v hv => h v (Nat.le_trans hu hv))
      exact ⟨t0, Nat.le_trans hu ht0, hst⟩
    · refine ⟨t, Nat.le_refl _, fun u hu => ?_⟩
      have h1 := hle t h u hu
      have h2 : ¬ f u < f t := fun hc => hlt ⟨u, hu, hc⟩
      omega

/-! ## Generic `Sys` plumbing: timers only grow, except when one fires -/

variable {σ μ : Type}

namespace Sys

theorem timers_applyEffect_append (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) :
    ∃ new, (applyEffect p (s, d) e).1.timers = s.timers ++ new := by
  cases e with
  | link q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | monitor q' => exact ⟨[], by simp only [applyEffect]; split <;> simp⟩
  | sendAfter to m => exact ⟨_, rfl⟩
  | _ => exact ⟨[], by simp [applyEffect]⟩

theorem timers_foldl_applyEffect_append (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) :
    ∃ new, (effs.foldl (applyEffect p) (s, d)).1.timers = s.timers ++ new := by
  induction effs generalizing s d with
  | nil => exact ⟨[], by simp⟩
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h1 := timers_applyEffect_append p s d e
    revert h1
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h1
    obtain ⟨n1, h1⟩ := h1
    obtain ⟨n2, h2⟩ := ih s1 d1
    exact ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc]⟩

/-- A `runE` only appends to `timers`. -/
theorem runE_timers_append {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') : ∃ new, s'.timers = s.timers ++ new := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  obtain ⟨new, hnew⟩ := timers_foldl_applyEffect_append p (beh p s.next st m).2
    { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } none
  simp only at hnew
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨new, hnew⟩
  · exact ⟨new, by rw [terminate_timers]; exact hnew⟩

theorem signalE_timers {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s') :
    s'.timers = s.timers := by
  obtain ⟨_, _, _, _, _, hc⟩ := signalE_cases h
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

theorem downE_timers {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    s'.timers = s.timers := by
  obtain ⟨_, _, _, _, _, hc⟩ := downE_cases h
  rcases hc with ⟨_, _, _, rfl⟩ | rfl <;> rfl

end Sys

theorem Config.get_of_stateOf {c : Config σ μ} {q : Pid} {x : σ} (h : c.stateOf q = some x) :
    ∃ mb, c.get q = some ⟨x, mb⟩ := by
  unfold Config.stateOf at h
  cases hget : c.get q with
  | none => rw [hget] at h; cases h
  | some a =>
    rw [hget] at h
    obtain ⟨st, mb⟩ := a
    simp at h
    exact ⟨mb, by rw [h]⟩

theorem Config.isSome_eq_false_iff_stateOf_none (c : Config σ μ) (q : Pid) :
    (c.get q).isSome = false ↔ c.stateOf q = none := by
  unfold Config.stateOf
  cases c.get q <;> simp

theorem SysStepI.eq_of_none {beh : EBehavior σ μ} {sig : Signals σ μ} {a b : Sys σ μ}
    (h : SysStepI beh sig none a b) : b = a := by
  cases h; rfl

/-! ## Timer fairness -/

namespace SysRun

variable {beh : EBehavior σ μ} {sig : Signals σ μ}

/-- Fairness of a timer addressed to `to` carrying `m`: if such a timer is
pending from some time on, some timer step firing one is eventually taken.
Timer indices shift when earlier timers fire, so this, not `WeakFair
(.timer i)` for a fixed `i`, is the assumption a liveness proof wants; it
follows from `∀ i, WeakFair (.timer i)` (`timerFair_of_weakFair_timers`). -/
def TimerFair (ρ : SysRun beh sig) (to : Pid) (m : μ) : Prop :=
  ∀ t, (∀ t' ≥ t, (to, m) ∈ (ρ.st t').timers) →
    ∃ t' ≥ t, ∃ i, ρ.ch t' = some (.timer i) ∧ (ρ.st t').timers[i]? = some (to, m)

theorem TimerFair.weakFairOn {ρ : SysRun beh sig} {to : Pid} {m : μ} (h : ρ.TimerFair to m) :
    WeakFairOn (fun t => (to, m) ∈ (ρ.st t).timers)
      (fun t => ∃ i, ρ.ch t = some (.timer i) ∧ (ρ.st t).timers[i]? = some (to, m)) :=
  WeakFairOn.of_taken h

/-- Weak fairness of every timer index gives `TimerFair`: the index of the
first `(to, m)` timer never increases along the run (steps only append
timers, a firing at another index removes one entry at most), so it is
eventually constant, and weak fairness of that index fires it. -/
theorem timerFair_of_weakFair_timers [DecidableEq μ] (ρ : SysRun beh sig) {to : Pid} {m : μ}
    (h : ∀ i, ρ.WeakFair (.timer i)) : ρ.TimerFair to m := by
  intro t hmem
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ t' ≥ t, ∀ i, ρ.ch t' = some (.timer i) → (ρ.st t').timers[i]? ≠ some (to, m) :=
    fun t' ht' i hch heq => hno ⟨t', ht', i, hch, heq⟩
  let p : Pid × μ → Bool := fun x => decide (x = (to, m))
  let f : Nat → Nat := fun u => (ρ.st u).timers.findIdx p
  have hex : ∀ u ≥ t, ∃ x ∈ (ρ.st u).timers, p x = true :=
    fun u hu => ⟨(to, m), hmem u hu, by simp [p]⟩
  have hstep : ∀ u ≥ t, f (u+1) ≤ f u := by
    intro u hu
    rcases hch : ρ.ch u with _ | c
    · have hs := ρ.step u
      rw [hch] at hs
      show (ρ.st (u+1)).timers.findIdx p ≤ (ρ.st u).timers.findIdx p
      rw [hs.eq_of_none]
      exact Nat.le_refl _
    · have hl := ρ.step_at hch
      show (ρ.st (u+1)).timers.findIdx p ≤ (ρ.st u).timers.findIdx p
      cases hl with
      | run _ q _ hrun =>
        obtain ⟨new, hnew⟩ := Sys.runE_timers_append hrun
        rw [hnew, List.findIdx_append_of_mem (hex u hu)]
        exact Nat.le_refl _
      | signal _ _ hsig => rw [Sys.signalE_timers hsig]; exact Nat.le_refl _
      | down _ _ hdown => rw [Sys.downE_timers hdown]; exact Nat.le_refl _
      | timer _ i _ htimer =>
        obtain ⟨to', m', hi, hb⟩ := Sys.timerE_cases htimer
        rw [hb]
        show ((ρ.st u).timers.eraseIdx i).findIdx p ≤ (ρ.st u).timers.findIdx p
        apply List.findIdx_eraseIdx_le _ (hex u hu)
        intro heq
        apply hno' u hu i hch
        have hl := List.findIdx_lt_length_of_exists (hex u hu)
        have hp := @List.findIdx_getElem _ p (ρ.st u).timers hl
        simp only [p, decide_eq_true_eq] at hp
        rw [heq, List.getElem?_eq_getElem hl, hp]
  obtain ⟨t0, ht0, hst⟩ := exists_stable_of_nonincreasing f t hstep
  have hen : ∀ u ≥ t0, SysEnabled (ρ.st u) (.timer (f t0)) := by
    intro u hu
    show f t0 < (ρ.st u).timers.length
    rw [← hst u hu]
    exact List.findIdx_lt_length_of_exists (hex u (Nat.le_trans ht0 hu))
  obtain ⟨u, hu, hch⟩ := (h (f t0)).taken hen
  apply hno' u (Nat.le_trans ht0 hu) _ hch
  rw [← hst u hu]
  have hl := List.findIdx_lt_length_of_exists (hex u (Nat.le_trans ht0 hu))
  have hp := @List.findIdx_getElem _ p (ρ.st u).timers hl
  simp only [p, decide_eq_true_eq] at hp
  show (ρ.st u).timers[(ρ.st u).timers.findIdx p]? = some (to, m)
  rw [List.getElem?_eq_getElem hl, hp]

/-- `stable_until` for a fair timer `(to, m)`: the goal is established by
any timer step that fires a `(to, m)` timer, and such a timer is pending
in every `P ∧ ¬Q` state. -/
theorem stable_until_timer (ρ : SysRun beh sig) {to : Pid} {m : μ} (hfair : ρ.TimerFair to m)
    {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b → P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → (to, m) ∈ a.timers)
    (htaken : ∀ {a b i}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig (.timer i) a b →
      a.timers[i]? = some (to, m) → P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.sysStep_or u with hs | heq
    · exact hstable (ρ.reach u) hs hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq ⟨i, hch, hi⟩
    exact htaken (ρ.reach u) (ρ.step_at hch) hi hp hq

/-- **A run from a phase invariant.** If from every `I t` system the
choice `c t` can be taken into an `I (t+1)` system, there is a run from
any `I 0` system that takes `c t` at every time `t` and satisfies `I t`
throughout. This is how an explicit infinite fair run is exhibited
without writing its states down: `I` is the shape of the system at each
phase. -/
theorem exists_of_inv (beh : EBehavior σ μ) (sig : Signals σ μ) {I : Nat → Sys σ μ → Prop}
    (c : Nat → SysChoice) {s0 : Sys σ μ} (h0 : I 0 s0)
    (hstep : ∀ t s, I t s → ∃ s', SysStepL beh sig (c t) s s' ∧ I (t+1) s') :
    ∃ ρ : SysRun beh sig, ρ.st 0 = s0 ∧ (∀ t, ρ.ch t = some (c t)) ∧ ∀ t, I t (ρ.st t) := by
  let next : (t : Nat) → {s // I t s} → {s // I (t+1) s} := fun t p =>
    ⟨Classical.choose (hstep t p.1 p.2), (Classical.choose_spec (hstep t p.1 p.2)).2⟩
  let seq : (t : Nat) → {s // I t s} := fun t =>
    Nat.rec (motive := fun t => {s // I t s}) ⟨s0, h0⟩ (fun t p => next t p) t
  refine ⟨⟨fun t => (seq t).1, fun t => some (c t), fun t => ?_⟩, rfl, fun _ => rfl, fun t => (seq t).2⟩
  exact .step _ _ _ (Classical.choose_spec (hstep t (seq t).1 (seq t).2)).1

end SysRun

/-! ## The watchdog -/

namespace Examples.Watchdog

open Leanactors Config Sys

/-- The watchdog has a live worker. -/
def Live (s : Sys St Msg) : Prop :=
  ∃ c bb, s.cfg.stateOf 0 = some (.watchdog (some c) bb) ∧ ((s.cfg.get c).isSome = true)

/-- The watchdog's current worker is `c`. -/
def DogChild (c : Pid) (s : Sys St Msg) : Prop := ∃ bb, s.cfg.stateOf 0 = some (.watchdog (some c) bb)

/-- The current worker is `c` and its exit signal is pending. -/
def SigPending (c : Pid) (s : Sys St Msg) : Prop := DogChild c s ∧ ∃ r, (0, c, r) ∈ s.signals

/-- The current worker is `c` and its `EXIT` is in the watchdog's mailbox. -/
def MsgPending (c : Pid) (s : Sys St Msg) : Prop :=
  DogChild c s ∧ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ ∃ r, (.EXIT c r : Msg) ∈ mb

/-- A signal addressed to the watchdog from `c`. -/
def isSig (c : Pid) (x : Pid × Pid × Reason) : Bool := decide (x.1 = 0 ∧ x.2.1 = c)

/-- The `EXIT` of `c`, whatever the reason. -/
def isExit (c : Pid) : Msg → Bool
  | .EXIT who _ => decide (who = c)
  | _ => false

def rankSig (c : Pid) (s : Sys St Msg) : Nat := s.signals.findIdx (isSig c)

def rankMsg (c : Pid) (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf 0 with
  | some mb => mb.findIdx (isExit c)
  | none => 0

theorem isSig_self (c : Pid) (r : Reason) : isSig c (0, c, r) = true := by simp [isSig]

theorem isExit_self (c : Pid) (r : Reason) : isExit c (.EXIT c r) = true := by simp [isExit]

theorem isExit_false {c : Pid} {m : Msg} (h : ∀ r, m ≠ .EXIT c r) : isExit c m = false := by
  cases m with
  | EXIT who r =>
    simp only [isExit, decide_eq_false_iff_not]
    intro hw; exact h r (by rw [hw])
  | _ => rfl

theorem rankSig_append {c : Pid} {l new : List (Pid × Pid × Reason)} {r : Reason}
    (h : (0, c, r) ∈ l) : (l ++ new).findIdx (isSig c) = l.findIdx (isSig c) :=
  List.findIdx_append_of_mem ⟨_, h, isSig_self c r⟩

theorem rankMsg_append {c : Pid} {mb new : List Msg} {r : Reason} (h : (.EXIT c r : Msg) ∈ mb) :
    (mb ++ new).findIdx (isExit c) = mb.findIdx (isExit c) :=
  List.findIdx_append_of_mem ⟨_, h, isExit_self c r⟩

theorem rankMsg_of_mboxOf {c : Pid} {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf 0 = some mb) :
    rankMsg c s = mb.findIdx (isExit c) := by
  unfold rankMsg; rw [h]

/-! ### Two more invariants, and `Good` -/

/-- A watchdog waiting for a pong has its timeout pending or already in
its mailbox: `start`, `pong` and the restart all arm it, and only handling
the timeout (which clears the flag) consumes it. -/
def Armed (s : Sys St Msg) : Prop :=
  ∀ w, s.cfg.stateOf 0 = some (.watchdog (some w) true) →
    (0, .timeout) ∈ s.timers ∨ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ (.timeout : Msg) ∈ mb

/-- The current worker was spawned, so its pid is below the counter. -/
def ChildLt (s : Sys St Msg) : Prop :=
  ∀ w bb, s.cfg.stateOf 0 = some (.watchdog (some w) bb) → w < s.next

/-- What the liveness arguments need of a start system. -/
structure Good (s : Sys St Msg) : Prop where
  inv : Inv s
  noKill : s.NoKillTo 0
  childNe : ChildNe s
  armed : Armed s
  childLt : ChildLt s

/-! ### The watchdog's own steps, concretely -/

/-- The restart: a fresh worker, linked, pinged, timer armed. -/
def spawnAt (a : Sys St Msg) (rest : List Msg) : Sys St Msg :=
  { a with cfg := ((a.cfg.set 0 ⟨.watchdog (some a.next) true, rest⟩).set a.next
             ⟨.worker false 0, []⟩).deliver a.next .ping,
           next := a.next + 1, links := (0, a.next) :: a.links, timers := a.timers ++ [(0, .timeout)] }

/-- A pong while waiting: re-ping, re-arm. -/
def pongAt (a : Sys St Msg) (w : Pid) (rest : List Msg) : Sys St Msg :=
  { a with cfg := (a.cfg.set 0 ⟨.watchdog (some w) true, rest⟩).deliver w .ping,
           timers := a.timers ++ [(0, .timeout)] }

/-- The timeout while waiting: clear the flag, queue the kill. -/
def killAt (a : Sys St Msg) (w : Pid) (rest : List Msg) : Sys St Msg :=
  { a with cfg := a.cfg.set 0 ⟨.watchdog (some w) false, rest⟩, signals := a.signals ++ [(w, 0, .kill)] }

theorem spawnAt_stateOf (a : Sys St Msg) (rest : List Msg) (hn : 0 < a.next) :
    (spawnAt a rest).cfg.stateOf 0 = some (.watchdog (some a.next) true) := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hn
  simp [spawnAt, stateOf_deliver, stateOf_set, Ne.symm hn0]

theorem spawnAt_mboxOf (a : Sys St Msg) (rest : List Msg) (hn : 0 < a.next) :
    (spawnAt a rest).cfg.mboxOf 0 = some rest := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hn
  show (((a.cfg.set 0 _).set a.next _).deliver a.next .ping).mboxOf 0 = _
  rw [mboxOf_deliver_eq, mboxOf_set, if_neg (Ne.symm hn0), mboxOf_set, if_pos rfl]
  simp [Ne.symm hn0]

theorem Live.spawnAt (a : Sys St Msg) (rest : List Msg) (hn : 0 < a.next) : Live (spawnAt a rest) :=
  ⟨a.next, true, spawnAt_stateOf a rest hn, by simp [Watchdog.spawnAt, isSome_deliver, isSome_set]⟩

theorem Armed.spawnAt (a : Sys St Msg) (rest : List Msg) : Armed (spawnAt a rest) :=
  fun _ _ => Or.inl (by simp [Watchdog.spawnAt])

theorem ChildLt.spawnAt (a : Sys St Msg) (rest : List Msg) (hn : 0 < a.next) :
    ChildLt (spawnAt a rest) := by
  intro w bb hw
  rw [spawnAt_stateOf a rest hn] at hw
  simp at hw
  obtain ⟨rfl, _⟩ := hw
  show a.next < a.next + 1
  exact Nat.lt_succ_self _

theorem pongAt_stateOf (a : Sys St Msg) (w : Pid) (rest : List Msg) :
    (pongAt a w rest).cfg.stateOf 0 = some (.watchdog (some w) true) := by
  simp [pongAt, stateOf_deliver, stateOf_set]

theorem pongAt_mboxOf (a : Sys St Msg) (w : Pid) (rest : List Msg) :
    ∃ new, (pongAt a w rest).cfg.mboxOf 0 = some (rest ++ new) := by
  obtain ⟨new, hnew⟩ := mboxOf_deliver (a.cfg.set 0 ⟨.watchdog (some w) true, rest⟩) w 0 .ping
  refine ⟨new, ?_⟩
  show ((a.cfg.set 0 _).deliver w .ping).mboxOf 0 = _
  rw [hnew, mboxOf_set, if_pos rfl]; rfl

theorem killAt_stateOf (a : Sys St Msg) (w : Pid) (rest : List Msg) :
    (killAt a w rest).cfg.stateOf 0 = some (.watchdog (some w) false) := by
  simp [killAt, stateOf_set]

theorem killAt_mboxOf (a : Sys St Msg) (w : Pid) (rest : List Msg) :
    (killAt a w rest).cfg.mboxOf 0 = some rest := by
  simp [killAt, mboxOf_set]

/-- A `run 0` step while the worker is `w`: the restart on `EXIT w _`, a
pong while waiting, the timeout while waiting, or a plain pop that keeps
the state. -/
theorem dog_run_cases {a b : Sys St Msg} {w : Pid} {bb : Bool}
    (hc : a.cfg.stateOf 0 = some (.watchdog (some w) bb)) (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.watchdog (some w) bb, m :: rest⟩ ∧
      ((∃ r, m = .EXIT w r ∧ b = spawnAt a rest) ∨
       (bb = true ∧ m = .pong ∧ b = pongAt a w rest) ∨
       (bb = true ∧ m = .timeout ∧ b = killAt a w rest) ∨
       ((∀ r, m ≠ .EXIT w r) ∧ (bb = true → m ≠ .pong ∧ m ≠ .timeout) ∧
        b = { a with cfg := a.cfg.set 0 ⟨.watchdog (some w) bb, rest⟩ })) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · cases bb with
    | false =>
      cases m with
      | EXIT who r =>
        by_cases hw : who = w
        · subst hw
          exact Or.inl ⟨r, rfl, by simp only [beh, if_true, applyEffects, List.foldl, applyEffect, spawnAt]⟩
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
          · intro r' hr'; cases hr'; exact hw rfl
          · intro h; cases h
          · simp only [beh, hw, if_false, applyEffects, List.foldl]
      | start =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro h; cases h
        · simp only [beh, applyEffects, List.foldl]
      | pong =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro h; cases h
        · simp only [beh, applyEffects, List.foldl]
      | timeout =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro h; cases h
        · simp only [beh, applyEffects, List.foldl]
      | ping =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro h; cases h
        · simp only [beh, applyEffects, List.foldl]
      | hang =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro h; cases h
        · simp only [beh, applyEffects, List.foldl]
    | true =>
      cases m with
      | EXIT who r =>
        by_cases hw : who = w
        · subst hw
          exact Or.inl ⟨r, rfl, by simp only [beh, if_true, applyEffects, List.foldl, applyEffect, spawnAt]⟩
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
          · intro r' hr'; cases hr'; exact hw rfl
          · intro _; exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
          · simp only [beh, hw, if_false, applyEffects, List.foldl]
      | pong =>
        exact Or.inr (Or.inl ⟨rfl, rfl, by simp only [beh, applyEffects, List.foldl, applyEffect, pongAt]⟩)
      | timeout =>
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp only [beh, applyEffects, List.foldl, applyEffect, killAt]⟩))
      | start =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro _; exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · simp only [beh, applyEffects, List.foldl]
      | ping =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro _; exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · simp only [beh, applyEffects, List.foldl]
      | hang =>
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        · intro r' hr'; cases hr'
        · intro _; exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · simp only [beh, applyEffects, List.foldl]
  · exact absurd (applyEffects_snd_some _ _ _ hr) (dog_no_exit _ _ _ _ _ _)

/-- A `run 0` step before `start`: the spawn, or a plain pop. -/
theorem dog_run_none_cases {a b : Sys St Msg} {bb : Bool}
    (hc : a.cfg.stateOf 0 = some (.watchdog none bb)) (h : runE beh a 0 = some b) :
    ∃ m rest, a.cfg.get 0 = some ⟨.watchdog none bb, m :: rest⟩ ∧
      ((m = .start ∧ b = spawnAt a rest) ∨
       (m ≠ .start ∧ b = { a with cfg := a.cfg.set 0 ⟨.watchdog none bb, rest⟩ })) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp [stateOf, hget] at hc
  subst hc
  refine ⟨m, rest, hget, ?_⟩
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · cases m with
    | start =>
      exact Or.inl ⟨rfl, by simp only [beh, applyEffects, List.foldl, applyEffect, spawnAt]⟩
    | pong => exact Or.inr ⟨(fun h => nomatch h), by simp only [beh, applyEffects, List.foldl]⟩
    | timeout => exact Or.inr ⟨(fun h => nomatch h), by simp only [beh, applyEffects, List.foldl]⟩
    | EXIT who r => exact Or.inr ⟨(fun h => nomatch h), by simp only [beh, applyEffects, List.foldl]⟩
    | ping => exact Or.inr ⟨(fun h => nomatch h), by simp only [beh, applyEffects, List.foldl]⟩
    | hang => exact Or.inr ⟨(fun h => nomatch h), by simp only [beh, applyEffects, List.foldl]⟩
  · exact absurd (applyEffects_snd_some _ _ _ hr) (dog_no_exit _ _ _ _ _ _)

/-- A signal step in a good system: the watchdog's state and the timers
are untouched, the head signal is popped (and more may be appended), and
the watchdog's mailbox gains exactly the `EXIT` if the head was addressed
to it, nothing otherwise. -/
theorem dog_signal_cases {a b : Sys St Msg} (hi : Inv a) (hk : a.NoKillTo 0)
    (h : signalE sig a = some b) :
    ∃ q src r rest, a.signals = (q, src, r) :: rest ∧
      b.cfg.stateOf 0 = a.cfg.stateOf 0 ∧ (∃ new, b.signals = rest ++ new) ∧ b.timers = a.timers ∧
      ((q = 0 ∧ b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ [.EXIT src r])) ∨
       (q ≠ 0 ∧ b.cfg.mboxOf 0 = a.cfg.mboxOf 0)) := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  refine ⟨q, src, r, rest, hsg, ?_⟩
  by_cases hq : q = 0
  · subst hq
    rcases hc with ⟨hd, _⟩ | ⟨act, hget, _, _, rfl⟩ | ⟨act, hget, htr, _, _⟩ | ⟨act, hget, htr, _, _⟩
      | ⟨_, _, rfl, _⟩
    · obtain ⟨_, _, hdog⟩ := hi.dog_alive
      simp [stateOf, hd] at hdog
    · refine ⟨stateOf_deliver _ _ _ _, ⟨[], by simp⟩, rfl, Or.inl ⟨rfl, ?_⟩⟩
      show (a.cfg.deliver 0 (sig.exitMsg src r)).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl]; rfl
    · rw [dog_traps hi hget] at htr; cases htr
    · rw [dog_traps hi hget] at htr; cases htr
    · exact absurd (by rw [hsg]; exact List.mem_cons_self) (hk src)
  · rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact ⟨rfl, ⟨[], by simp⟩, rfl, Or.inr ⟨hq, rfl⟩⟩
    · refine ⟨stateOf_deliver _ _ _ _, ⟨[], by simp⟩, rfl, Or.inr ⟨hq, ?_⟩⟩
      show (a.cfg.deliver q (sig.exitMsg src r)).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_neg (Ne.symm hq)]; simp
    · exact ⟨rfl, ⟨[], by simp⟩, rfl, Or.inr ⟨hq, rfl⟩⟩
    · exact ⟨terminate_stateOf_ne _ _ _ (Ne.symm hq), ⟨_, terminate_signals _ _ _⟩, rfl,
        Or.inr ⟨hq, by show (Sys.cfg _).mboxOf 0 = _; simp only [terminate]; exact mboxOf_remove_ne _ (Ne.symm hq)⟩⟩
    · exact ⟨terminate_stateOf_ne _ _ _ (Ne.symm hq), ⟨_, terminate_signals _ _ _⟩, rfl,
        Or.inr ⟨hq, by show (Sys.cfg _).mboxOf 0 = _; simp only [terminate]; exact mboxOf_remove_ne _ (Ne.symm hq)⟩⟩

/-! ### `Good` is invariant -/

theorem Armed.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hg : Good a) : Armed b := by
  have hi := hg.inv
  cases h with
  | run p _ hrun =>
    by_cases hp : p = 0
    · subst hp
      obtain ⟨w0, b0, hdog⟩ := hi.dog_alive
      cases w0 with
      | none =>
        obtain ⟨m, rest, hget, hcase⟩ := dog_run_none_cases hdog hrun
        rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact Armed.spawnAt a rest
        · intro w hw; simp [stateOf_set] at hw
      | some w0 =>
        obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hdog hrun
        rcases hcase with ⟨r, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨hne, hnt, rfl⟩
        · exact Armed.spawnAt a rest
        · intro w _; left; simp [pongAt]
        · intro w hw; rw [killAt_stateOf] at hw; simp at hw
        · intro w hw
          simp [stateOf_set] at hw
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨_, hnt⟩ := hnt rfl
          rcases hg.armed w0 (by simp [stateOf, hget]) with ht | ⟨mb, hmb, hm⟩
          · exact Or.inl ht
          · right
            refine ⟨rest, by simp [mboxOf_set], ?_⟩
            simp [Config.mboxOf, hget] at hmb
            subst hmb
            rcases List.mem_cons.mp hm with h | h
            · exact absurd h.symm hnt
            · exact h
    · have hf := runE_frame hrun
      intro w hw
      rw [hf.stateOf 0 (Ne.symm hp) hi.next_pos] at hw
      rcases hg.armed w hw with ht | ⟨mb, hmb, hm⟩
      · exact Or.inl (hf.timers _ ht)
      · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp) hi.next_pos
        exact Or.inr ⟨mb ++ new, by rw [hnew, hmb]; rfl, List.mem_append_left _ hm⟩
  | signal _ hsig =>
    obtain ⟨q, src, r, rest, hsg, hst, _, htm, hmb⟩ := dog_signal_cases hi hg.noKill hsig
    intro w hw
    rw [hst] at hw
    rcases hg.armed w hw with ht | ⟨mb, hmb', hm⟩
    · exact Or.inl (htm ▸ ht)
    · right
      rcases hmb with ⟨_, hmb⟩ | ⟨_, hmb⟩
      · exact ⟨mb ++ [.EXIT src r], by rw [hmb, hmb']; rfl, List.mem_append_left _ hm⟩
      · exact ⟨mb, by rw [hmb, hmb'], hm⟩
  | down _ hdown =>
    obtain ⟨_, _, _, rest, _, hgr⟩ := downE_grows hdown
    intro w hw
    rw [downE_stateOf hdown] at hw
    rcases hg.armed w hw with ht | ⟨mb, hmb, hm⟩
    · exact Or.inl (hgr.timers _ ht)
    · obtain ⟨new, hnew⟩ := mboxOf_downE_append hdown 0
      exact Or.inr ⟨mb ++ new, by rw [hnew, hmb]; rfl, List.mem_append_left _ hm⟩
  | timer i _ htimer =>
    obtain ⟨to, m, hti, hb⟩ := timerE_cases htimer
    intro w hw
    rw [timerE_stateOf htimer] at hw
    by_cases hx : (to, m) = (0, .timeout)
    · right
      obtain ⟨mb, hget⟩ := Config.get_of_stateOf hw
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      refine ⟨mb ++ [.timeout], ?_, List.mem_append_right _ List.mem_cons_self⟩
      rw [hb]
      show (a.cfg.deliver 0 .timeout).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl]
      simp [Config.mboxOf, hget]
    · rcases hg.armed w hw with ht | ⟨mb, hmb, hm⟩
      · left
        rw [hb]
        exact List.mem_eraseIdx_of_ne ht hti hx
      · right
        obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
        exact ⟨mb ++ new, by rw [hnew, hmb]; rfl, List.mem_append_left _ hm⟩

theorem ChildLt.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hg : Good a) : ChildLt b := by
  have hi := hg.inv
  have hnext := h.next_mono
  cases h with
  | run p _ hrun =>
    by_cases hp : p = 0
    · subst hp
      obtain ⟨w0, b0, hdog⟩ := hi.dog_alive
      cases w0 with
      | none =>
        obtain ⟨m, rest, hget, hcase⟩ := dog_run_none_cases hdog hrun
        rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact ChildLt.spawnAt a rest hi.next_pos
        · intro w bb hw; simp [stateOf_set] at hw
      | some w0 =>
        obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hdog hrun
        rcases hcase with ⟨r, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
        · exact ChildLt.spawnAt a rest hi.next_pos
        · intro w bb hw
          rw [pongAt_stateOf] at hw
          simp at hw
          obtain ⟨rfl, _⟩ := hw
          exact hg.childLt _ _ hdog
        · intro w bb hw
          rw [killAt_stateOf] at hw
          simp at hw
          obtain ⟨rfl, _⟩ := hw
          exact hg.childLt _ _ hdog
        · intro w bb hw
          simp [stateOf_set] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact hg.childLt _ _ hdog
    · intro w bb hw
      rw [runE_stateOf_of_ne hrun (Ne.symm hp) hi.next_pos] at hw
      exact Nat.lt_of_lt_of_le (hg.childLt w bb hw) hnext
  | signal _ hsig =>
    obtain ⟨_, _, _, _, _, hst, _, _, _⟩ := dog_signal_cases hi hg.noKill hsig
    intro w bb hw
    rw [hst] at hw
    exact Nat.lt_of_lt_of_le (hg.childLt w bb hw) hnext
  | down _ hdown =>
    intro w bb hw
    rw [downE_stateOf hdown] at hw
    exact Nat.lt_of_lt_of_le (hg.childLt w bb hw) hnext
  | timer i _ htimer =>
    intro w bb hw
    rw [timerE_stateOf htimer] at hw
    exact Nat.lt_of_lt_of_le (hg.childLt w bb hw) hnext

theorem Good.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hg : Good a) : Good b :=
  ⟨Inv.step h hg.inv hg.noKill, noKillTo_step h hg.noKill hg.childNe,
   childNe_step h hg.childNe hg.inv.next_pos, Armed.step h hg, ChildLt.step h hg⟩

/-- An environment delivery keeps `Good`: states, signals and timers are
untouched and mailboxes only grow. -/
theorem Good.deliver {a : Sys St Msg} (p : Pid) (m : Msg) (hg : Good a) :
    Good { a with cfg := a.cfg.deliver p m } := by
  have hst : ∀ q, (a.cfg.deliver p m).stateOf q = a.cfg.stateOf q := fun q => stateOf_deliver _ _ _ _
  refine ⟨hg.inv.grows (grows_deliver a p m), hg.noKill.of_signals_eq rfl,
    fun q w bb hq => hg.childNe q w bb (by rw [← hst q]; exact hq), ?_,
    fun w bb hw => hg.childLt w bb (by rw [← hst 0]; exact hw)⟩
  intro w hw
  have hw' : a.cfg.stateOf 0 = some (.watchdog (some w) true) := by rw [← hst 0]; exact hw
  rcases hg.armed w hw' with ht | ⟨mb, hmb, hm⟩
  · exact Or.inl ht
  · obtain ⟨new, hnew⟩ := mboxOf_deliver a.cfg p 0 m
    exact Or.inr ⟨mb ++ new, by show (a.cfg.deliver p m).mboxOf 0 = _; rw [hnew, hmb]; rfl,
      List.mem_append_left _ hm⟩

theorem init_armed : Armed init := by
  intro w hw
  simp [init, stateOf, Config.get] at hw

theorem init_childLt : ChildLt init := by
  intro w bb hw
  simp [init, stateOf, Config.get] at hw

theorem Good.init : Good init := ⟨init_inv, init_noKillTo, init_childNe, init_armed, init_childLt⟩

/-- `Good` is kept along the (closed) steps of a run. -/
theorem reach_good {s₀ s : Sys St Msg} (hg : Good s₀) (hr : SysReach beh sig s₀ s) : Good s :=
  hr.inv (fun h hg => hg.step h) hg

/-- Every system the environment can drive the watchdog to from `init` is `Good`. -/
theorem reachEnv_good {s : Sys St Msg} (hr : SysReachEnv beh sig init s) : Good s :=
  hr.inv (fun h hg => hg.step h) (fun p m hg => hg.deliver p m) Good.init

theorem DogChild.get {c : Pid} {s : Sys St Msg} (h : DogChild c s) :
    ∃ bb mb, s.cfg.get 0 = some ⟨.watchdog (some c) bb, mb⟩ := by
  obtain ⟨bb, hb⟩ := h
  obtain ⟨mb, hget⟩ := Config.get_of_stateOf hb
  exact ⟨bb, mb, hget⟩

theorem DogChild.mboxOf {c : Pid} {s : Sys St Msg} (h : DogChild c s) :
    ∃ mb, s.cfg.mboxOf 0 = some mb := by
  obtain ⟨_, mb, hget⟩ := h.get
  exact ⟨mb, by simp [Config.mboxOf, hget]⟩

/-! ### `restart_eventually`: stage A, the pending signal is delivered -/

theorem sigPending_step {c : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : SigPending c a) :
    (Live b ∨ MsgPending c b) ∨
      (SigPending c b ∧ rankSig c b ≤ rankSig c a ∧ (ch = .signal → rankSig c b < rankSig c a)) := by
  have hi := hg.inv
  obtain ⟨⟨k, hc⟩, r, hs⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hc hrun
      rcases hcase with ⟨r', _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · exact Or.inl (Or.inl (Live.spawnAt a rest hi.next_pos))
      · exact Or.inr ⟨⟨⟨true, pongAt_stateOf a c rest⟩, r, hs⟩, Nat.le_refl _, fun h => nomatch h⟩
      · refine Or.inr ⟨⟨⟨false, killAt_stateOf a c rest⟩, r, List.mem_append_left _ hs⟩, ?_,
          fun h => nomatch h⟩
        show (a.signals ++ [(c, 0, Reason.kill)]).findIdx (isSig c) ≤ a.signals.findIdx (isSig c)
        rw [rankSig_append hs]; exact Nat.le_refl _
      · exact Or.inr ⟨⟨⟨k, by simp [stateOf_set]⟩, r, hs⟩, Nat.le_refl _, fun h => nomatch h⟩
    · obtain ⟨new, hnew⟩ := runE_signals_append hrun
      refine Or.inr ⟨⟨⟨k, ?_⟩, r, by rw [hnew]; exact List.mem_append_left _ hs⟩, ?_, fun h => nomatch h⟩
      · rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hc
      · unfold rankSig; rw [hnew, rankSig_append hs]; exact Nat.le_refl _
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, ⟨new, hnew⟩, _, hmb⟩ := dog_signal_cases hi hg.noKill hsig
    by_cases hhead : q = 0 ∧ src = c
    · obtain ⟨hq0, hsrc⟩ := hhead
      subst q; subst src
      rcases hmb with ⟨_, hmb⟩ | ⟨hne, _⟩
      · obtain ⟨mb, hmb'⟩ := DogChild.mboxOf (⟨k, hc⟩ : DogChild c a)
        refine Or.inl (Or.inr ⟨⟨k, by rw [hst]; exact hc⟩, mb ++ [.EXIT c r'], ?_, r', ?_⟩)
        · rw [hmb, hmb']; rfl
        · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd rfl hne
    · have hrest : (0, c, r) ∈ rest := by
        rw [hsg] at hs
        rcases List.mem_cons.mp hs with h | h
        · exact absurd ⟨(congrArg Prod.fst h).symm, (congrArg (·.2.1) h).symm⟩ hhead
        · exact h
      have hno : isSig c (q, src, r') = false := by
        simp only [isSig, decide_eq_false_iff_not]; exact hhead
      have hlt : rankSig c b < rankSig c a := by
        unfold rankSig
        rw [hnew, rankSig_append hrest, hsg, List.findIdx_cons_of_false hno]
        exact Nat.lt_succ_self _
      exact Or.inr ⟨⟨⟨k, by rw [hst]; exact hc⟩, r, by rw [hnew]; exact List.mem_append_left _ hrest⟩,
        Nat.le_of_lt hlt, fun _ => hlt⟩
  | down _ _ hdown =>
    refine Or.inr ⟨⟨⟨k, by rw [downE_stateOf hdown]; exact hc⟩, r, by rw [downE_signals hdown]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankSig; rw [downE_signals hdown]; exact Nat.le_refl _
  | timer _ i _ htimer =>
    refine Or.inr ⟨⟨⟨k, by rw [timerE_stateOf htimer]; exact hc⟩, r, by rw [timerE_signals htimer]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankSig; rw [timerE_signals htimer]; exact Nat.le_refl _

theorem sigPending_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hfair : ρ.WeakFair .signal)
    (c : Pid) : LeadsTo ρ.st (SigPending c) (fun s => Live s ∨ MsgPending c s) := by
  apply ρ.rank_leads_to_of_step .signal (rankSig c) hfair
  · intro ch a b hr hl hp _
    exact sigPending_step (reach_good h0 hr) hl hp
  · intro a _ ⟨_, r, hs⟩ _
    show a.signals ≠ []
    intro hnil; rw [hnil] at hs; cases hs

/-! ### Stage B: the `EXIT` message is processed -/

/-- The mailbox of the watchdog only grew: `MsgPending` and the rank are kept. -/
theorem msgPending_grow {c : Pid} {a b : Sys St Msg} {k : Bool}
    (hc : b.cfg.stateOf 0 = some (.watchdog (some c) k))
    {mb : List Msg} (hmb : a.cfg.mboxOf 0 = some mb) {r : Reason} (hr : (.EXIT c r : Msg) ∈ mb)
    {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new)) :
    MsgPending c b ∧ rankMsg c b ≤ rankMsg c a := by
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  refine ⟨⟨⟨k, hc⟩, mb ++ new, hnew, r, List.mem_append_left _ hr⟩, ?_⟩
  rw [rankMsg_of_mboxOf hnew, rankMsg_of_mboxOf hmb, rankMsg_append hr]
  exact Nat.le_refl _

/-- A `run 0` step that pops something other than the awaited `EXIT`: the
rank drops by one. -/
theorem msgPending_pop {c : Pid} {a b : Sys St Msg} {bb : Bool} {m : Msg} {rest : List Msg}
    (hget : a.cfg.get 0 = some ⟨.watchdog (some c) bb, m :: rest⟩) (hne : ∀ r, m ≠ .EXIT c r)
    {bb' : Bool} (hst : b.cfg.stateOf 0 = some (.watchdog (some c) bb'))
    {new : List Msg} (hmb : b.cfg.mboxOf 0 = some (rest ++ new))
    {r : Reason} (hr : (.EXIT c r : Msg) ∈ m :: rest) :
    MsgPending c b ∧ rankMsg c b < rankMsg c a := by
  have hrest : (.EXIT c r : Msg) ∈ rest := by
    rcases List.mem_cons.mp hr with h | h
    · exact absurd h.symm (hne r)
    · exact h
  refine ⟨⟨⟨bb', hst⟩, rest ++ new, hmb, r, List.mem_append_left _ hrest⟩, ?_⟩
  rw [rankMsg_of_mboxOf hmb, rankMsg_of_mboxOf (show a.cfg.mboxOf 0 = some (m :: rest) by simp [Config.mboxOf, hget]),
    rankMsg_append hrest, List.findIdx_cons_of_false (isExit_false hne)]
  exact Nat.lt_succ_self _

theorem msgPending_step {c : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : MsgPending c a) :
    Live b ∨ (MsgPending c b ∧ rankMsg c b ≤ rankMsg c a ∧ (ch = .run 0 → rankMsg c b < rankMsg c a)) := by
  have hi := hg.inv
  obtain ⟨⟨k, hc⟩, mb, hmb, r, hr⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hc hrun
      have hmb' : mb = m :: rest := by
        simp [Config.mboxOf, hget] at hmb; exact hmb.symm
      subst hmb'
      rcases hcase with ⟨r', _, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨hne, _, rfl⟩
      · exact Or.inl (Live.spawnAt a rest hi.next_pos)
      · obtain ⟨new, hnew⟩ := pongAt_mboxOf a c rest
        obtain ⟨h1, h2⟩ := msgPending_pop hget (fun _ h => nomatch h) (pongAt_stateOf a c rest) hnew hr
        exact Or.inr ⟨h1, Nat.le_of_lt h2, fun _ => h2⟩
      · have hmbb : (killAt a c rest).cfg.mboxOf 0 = some (rest ++ []) := by
          rw [killAt_mboxOf, List.append_nil]
        obtain ⟨h1, h2⟩ := msgPending_pop hget (fun _ h => nomatch h) (killAt_stateOf a c rest) hmbb hr
        exact Or.inr ⟨h1, Nat.le_of_lt h2, fun _ => h2⟩
      · have hst : ({ a with cfg := a.cfg.set 0 ⟨.watchdog (some c) k, rest⟩ } : Sys St Msg).cfg.stateOf 0 =
            some (.watchdog (some c) k) := by simp [stateOf_set]
        have hmbb : ({ a with cfg := a.cfg.set 0 ⟨.watchdog (some c) k, rest⟩ } : Sys St Msg).cfg.mboxOf 0 =
            some (rest ++ []) := by simp [mboxOf_set]
        obtain ⟨h1, h2⟩ := msgPending_pop hget hne hst hmbb hr
        exact Or.inr ⟨h1, Nat.le_of_lt h2, fun _ => h2⟩
    · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp0) hi.next_pos
      have hc' : b.cfg.stateOf 0 = some (.watchdog (some c) k) := by
        rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hc
      obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => absurd (SysChoice.run.inj h) hp0⟩
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, _, _, hmbc⟩ := dog_signal_cases hi hg.noKill hsig
    have hc' : b.cfg.stateOf 0 = some (.watchdog (some c) k) := by rw [hst]; exact hc
    rcases hmbc with ⟨_, hnew⟩ | ⟨_, hnew⟩
    · obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
    · obtain ⟨h1, h2⟩ := msgPending_grow hc' hmb hr (new := []) (by rw [hnew, hmb]; simp)
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | down _ _ hdown =>
    obtain ⟨new, hnew⟩ := mboxOf_downE_append hdown 0
    obtain ⟨h1, h2⟩ := msgPending_grow (by rw [downE_stateOf hdown]; exact hc) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
    obtain ⟨h1, h2⟩ := msgPending_grow (by rw [timerE_stateOf htimer]; exact hc) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

theorem msgPending_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hfair : ρ.WeakFair (.run 0))
    (c : Pid) : LeadsTo ρ.st (MsgPending c) Live := by
  apply ρ.rank_leads_to_of_step (.run 0) (rankMsg c) hfair
  · intro ch a b hr hl hp _
    exact msgPending_step (reach_good h0 hr) hl hp
  · intro a _ ⟨hsc, mb, hmb, r, hr⟩ _
    obtain ⟨k, mb', hget⟩ := hsc.get
    have : mb = mb' := by simp [Config.mboxOf, hget] at hmb; exact hmb.symm
    subst this
    cases mb with
    | nil => cases hr
    | cons m rest => exact ⟨_, m, rest, hget⟩

/-! ### The first theorem -/

/-- **A dead worker is eventually replaced.** Along any run from a `Good`
system in which the `signal` step and the `run 0` step are weakly fair:
if at time `t` the watchdog's current worker `w` is dead, then at some
`t' ≥ t` the watchdog's current worker is alive. Exactly the supervisor's
statement; no fairness of timers, `down` or the workers is needed. -/
theorem restart_eventually (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w bb, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) bb) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ w' bb', (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb') ∧
        ((ρ.st t').cfg.get w').isSome = true := by
  intro t w bb hc hdead
  have hg : Good (ρ.st t) := reach_good h0 (ρ.reach t)
  have hB := msgPending_leadsTo ρ h0 hrun w
  have hA := (sigPending_leadsTo ρ h0 hsig w).trans ((LeadsTo.refl ρ.st Live).or hB)
  rcases hg.inv.child_ok w bb hc with ⟨hal, _⟩ | ⟨r, hs⟩ | ⟨r, hm⟩
  · rw [hdead] at hal; cases hal
  · exact hA t ⟨⟨bb, hc⟩, r, hs⟩
  · refine hB t ⟨⟨bb, hc⟩, ?_⟩
    obtain ⟨_, mb, hget⟩ := DogChild.get (⟨bb, hc⟩ : DogChild w (ρ.st t))
    refine ⟨mb, by simp [Config.mboxOf, hget], r, ?_⟩
    unfold mcount at hm
    rw [hget] at hm
    exact List.count_pos_iff.mp hm

/-- The same from any system the environment can drive the watchdog to. -/
theorem restart_eventually_env (ρ : SysRun beh sig) (h0 : SysReachEnv beh sig init (ρ.st 0))
    (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w bb, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) bb) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ w' bb', (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb') ∧
        ((ρ.st t').cfg.get w').isSome = true :=
  restart_eventually ρ (reachEnv_good h0) hsig hrun

/-- From `init` itself. Unlike the supervisor's, this is not vacuous: the
watchdog kills its own worker when the timer fires, so a closed run from
`init` does reach a dead worker (`dead_worker_reachable`). -/
theorem restart_eventually_init (ρ : SysRun beh sig) (h0 : ρ.st 0 = init)
    (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w bb, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) bb) → ((ρ.st t).cfg.get w).isSome = false →
      ∃ t' ≥ t, ∃ w' bb', (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb') ∧
        ((ρ.st t').cfg.get w').isSome = true :=
  restart_eventually ρ (by rw [h0]; exact Good.init) hsig hrun

/-- The premise of `restart_eventually` is reachable by closed steps alone:
start, the timer fires, the watchdog handles the timeout (kill queued),
the kill is delivered. Worker 1 is dead and its exit signal is pending. -/
theorem dead_worker_reachable : ∃ s, SysReach beh sig init s ∧
    ∃ w bb, s.cfg.stateOf 0 = some (.watchdog (some w) bb) ∧ (s.cfg.get w).isSome = false :=
  ⟨_, .step (.run _ 0 _ rfl) (.step (.timer _ 0 _ rfl) (.step (.run _ 0 _ rfl)
      (.step (.signal _ _ rfl) (.refl _)))), 1, false, rfl, rfl⟩

/-! ### The timer-driven chain: predicates and ranks -/

/-- The watchdog has pinged `w` and waits for the pong or the timeout. -/
def Waiting (w : Pid) (s : Sys St Msg) : Prop := s.cfg.stateOf 0 = some (.watchdog (some w) true)

/-- Waiting for `w`, with the timeout already in the watchdog's mailbox. -/
def TimeoutInbox (w : Pid) (s : Sys St Msg) : Prop :=
  Waiting w s ∧ ∃ mb, s.cfg.mboxOf 0 = some mb ∧ (.timeout : Msg) ∈ mb

/-- The current worker is `w` and the kill aimed at it is queued. -/
def KillPending (w : Pid) (s : Sys St Msg) : Prop := DogChild w s ∧ (w, 0, Reason.kill) ∈ s.signals

/-- The current worker is `w` and it is dead. -/
def Dead (w : Pid) (s : Sys St Msg) : Prop := DogChild w s ∧ (s.cfg.get w).isSome = false

/-- The current worker is a live pid other than `w`. -/
def Replaced (w : Pid) (s : Sys St Msg) : Prop :=
  ∃ w' bb, s.cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧ (s.cfg.get w').isSome = true

def isTimeout : Msg → Bool
  | .timeout => true
  | _ => false

/-- Stage 1 rank: messages ahead of the first `timeout` in the watchdog's mailbox. -/
def rankTimeout (s : Sys St Msg) : Nat :=
  match s.cfg.mboxOf 0 with
  | some mb => mb.findIdx isTimeout
  | none => 0

def isKill (w : Pid) (x : Pid × Pid × Reason) : Bool := decide (x = (w, 0, .kill))

/-- Stage 2 rank: signals ahead of the kill aimed at `w`. -/
def rankKill (w : Pid) (s : Sys St Msg) : Nat := s.signals.findIdx (isKill w)

theorem isTimeout_false {m : Msg} (h : m ≠ .timeout) : isTimeout m = false := by
  cases m with
  | timeout => exact absurd rfl h
  | _ => rfl

theorem isKill_self (w : Pid) : isKill w (w, 0, .kill) = true := by simp [isKill]

theorem rankTimeout_of_mboxOf {s : Sys St Msg} {mb : List Msg} (h : s.cfg.mboxOf 0 = some mb) :
    rankTimeout s = mb.findIdx isTimeout := by
  unfold rankTimeout; rw [h]

theorem rankTimeout_append {mb new : List Msg} (h : (.timeout : Msg) ∈ mb) :
    (mb ++ new).findIdx isTimeout = mb.findIdx isTimeout :=
  List.findIdx_append_of_mem ⟨_, h, rfl⟩

theorem rankKill_append {w : Pid} {l new : List (Pid × Pid × Reason)} (h : (w, 0, Reason.kill) ∈ l) :
    (l ++ new).findIdx (isKill w) = l.findIdx (isKill w) :=
  List.findIdx_append_of_mem ⟨_, h, isKill_self w⟩

theorem Replaced.spawnAt (a : Sys St Msg) (rest : List Msg) {w : Pid} (hn : 0 < a.next)
    (hw : w < a.next) : Replaced w (spawnAt a rest) :=
  ⟨a.next, true, spawnAt_stateOf a rest hn, Nat.ne_of_gt hw,
   by simp [Watchdog.spawnAt, isSome_deliver, isSome_set]⟩

theorem Waiting.get {w : Pid} {s : Sys St Msg} (h : Waiting w s) :
    ∃ mb, s.cfg.get 0 = some ⟨.watchdog (some w) true, mb⟩ :=
  Config.get_of_stateOf h

/-! ### Stage 0: the timeout fires -/

/-- While waiting for `w` and without the timeout in the mailbox, a step
keeps the watchdog waiting for `w` or restarts. -/
theorem waiting_step {w : Pid} {a b : Sys St Msg} (hg : Good a) (h : SysStep beh sig a b)
    (hw : Waiting w a) (hn : ¬ TimeoutInbox w a) : Waiting w b ∨ Replaced w b := by
  have hi := hg.inv
  cases h with
  | run p _ hrun =>
    by_cases hp : p = 0
    · subst hp
      obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hw hrun
      rcases hcase with ⟨r, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, _, rfl⟩
      · exact Or.inr (Replaced.spawnAt a rest hi.next_pos (hg.childLt w true hw))
      · exact Or.inl (pongAt_stateOf a w rest)
      · exact absurd ⟨hw, .timeout :: rest, by simp [Config.mboxOf, hget], List.mem_cons_self⟩ hn
      · exact Or.inl (by simp [Waiting, stateOf_set])
    · exact Or.inl (by unfold Waiting; rw [runE_stateOf_of_ne hrun (Ne.symm hp) hi.next_pos]; exact hw)
  | signal _ hsig =>
    obtain ⟨_, _, _, _, _, hst, _, _, _⟩ := dog_signal_cases hi hg.noKill hsig
    exact Or.inl (by unfold Waiting; rw [hst]; exact hw)
  | down _ hdown => exact Or.inl (by unfold Waiting; rw [downE_stateOf hdown]; exact hw)
  | timer i _ htimer => exact Or.inl (by unfold Waiting; rw [timerE_stateOf htimer]; exact hw)

/-- **Stage 0.** With a fair `(0, timeout)` timer, waiting for `w` leads to
the timeout in the mailbox (still waiting for `w`) or to a restart. -/
theorem waiting_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hfair : ρ.TimerFair 0 .timeout)
    (w : Pid) : LeadsTo ρ.st (Waiting w) (fun s => TimeoutInbox w s ∨ Replaced w s) := by
  apply ρ.stable_until_timer hfair
  · intro a b hr hs hw hn
    rcases waiting_step (reach_good h0 hr) hs hw (fun h => hn (Or.inl h)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · intro a hr hw hn
    rcases (reach_good h0 hr).armed w hw with ht | ⟨mb, hmb, hm⟩
    · exact ht
    · exact absurd (Or.inl ⟨hw, mb, hmb, hm⟩) hn
  · intro a b i _ hl hi hw _
    cases hl with
    | timer _ _ _ htimer =>
      obtain ⟨to, m, hti, rfl⟩ := timerE_cases htimer
      rw [hi] at hti
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hti)
      obtain ⟨mb, hget⟩ := hw.get
      refine Or.inl ⟨by unfold Waiting; rw [stateOf_deliver]; exact hw, mb ++ [.timeout], ?_,
        List.mem_append_right _ List.mem_cons_self⟩
      show (a.cfg.deliver 0 .timeout).mboxOf 0 = _
      rw [mboxOf_deliver_eq, if_pos rfl]
      simp [Config.mboxOf, hget]

/-! ### Stage 1: the watchdog reaches the timeout -/

theorem timeoutInbox_grow {w : Pid} {a b : Sys St Msg} (hst : Waiting w b)
    {mb : List Msg} (hmb : a.cfg.mboxOf 0 = some mb) (hr : (.timeout : Msg) ∈ mb)
    {new : List Msg} (hnew : b.cfg.mboxOf 0 = (a.cfg.mboxOf 0).map (· ++ new)) :
    TimeoutInbox w b ∧ rankTimeout b ≤ rankTimeout a := by
  rw [hmb] at hnew
  simp only [Option.map_some] at hnew
  refine ⟨⟨hst, mb ++ new, hnew, List.mem_append_left _ hr⟩, ?_⟩
  rw [rankTimeout_of_mboxOf hnew, rankTimeout_of_mboxOf hmb, rankTimeout_append hr]
  exact Nat.le_refl _

theorem timeoutInbox_pop {w : Pid} {a b : Sys St Msg} {m : Msg} {rest : List Msg}
    (hget : a.cfg.get 0 = some ⟨.watchdog (some w) true, m :: rest⟩) (hne : m ≠ .timeout)
    (hst : Waiting w b) {new : List Msg} (hmb : b.cfg.mboxOf 0 = some (rest ++ new))
    (hr : (.timeout : Msg) ∈ m :: rest) : TimeoutInbox w b ∧ rankTimeout b < rankTimeout a := by
  have hrest : (.timeout : Msg) ∈ rest := by
    rcases List.mem_cons.mp hr with h | h
    · exact absurd h.symm hne
    · exact h
  refine ⟨⟨hst, rest ++ new, hmb, List.mem_append_left _ hrest⟩, ?_⟩
  rw [rankTimeout_of_mboxOf hmb,
    rankTimeout_of_mboxOf (show a.cfg.mboxOf 0 = some (m :: rest) by simp [Config.mboxOf, hget]),
    rankTimeout_append hrest, List.findIdx_cons_of_false (isTimeout_false hne)]
  exact Nat.lt_succ_self _

theorem timeoutInbox_step {w : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : TimeoutInbox w a) :
    (KillPending w b ∨ Replaced w b) ∨
      (TimeoutInbox w b ∧ rankTimeout b ≤ rankTimeout a ∧ (ch = .run 0 → rankTimeout b < rankTimeout a)) := by
  have hi := hg.inv
  obtain ⟨hw, mb, hmb, hr⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hw hrun
      have hmb' : mb = m :: rest := by
        simp [Config.mboxOf, hget] at hmb; exact hmb.symm
      subst hmb'
      rcases hcase with ⟨r, _, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, hnt, rfl⟩
      · exact Or.inl (Or.inr (Replaced.spawnAt a rest hi.next_pos (hg.childLt w true hw)))
      · obtain ⟨new, hnew⟩ := pongAt_mboxOf a w rest
        obtain ⟨h1, h2⟩ := timeoutInbox_pop hget (fun h => nomatch h) (pongAt_stateOf a w rest) hnew hr
        exact Or.inr ⟨h1, Nat.le_of_lt h2, fun _ => h2⟩
      · exact Or.inl (Or.inl ⟨⟨false, killAt_stateOf a w rest⟩, List.mem_append_right _ List.mem_cons_self⟩)
      · obtain ⟨_, hnt⟩ := hnt rfl
        have hst : Waiting w { a with cfg := a.cfg.set 0 ⟨.watchdog (some w) true, rest⟩ } := by
          simp [Waiting, stateOf_set]
        have hmbb : ({ a with cfg := a.cfg.set 0 ⟨.watchdog (some w) true, rest⟩ } : Sys St Msg).cfg.mboxOf 0 =
            some (rest ++ []) := by simp [mboxOf_set]
        obtain ⟨h1, h2⟩ := timeoutInbox_pop hget hnt hst hmbb hr
        exact Or.inr ⟨h1, Nat.le_of_lt h2, fun _ => h2⟩
    · obtain ⟨new, hnew⟩ := mboxOf_runE_append hrun (Ne.symm hp0) hi.next_pos
      have hst : Waiting w b := by
        unfold Waiting; rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hw
      obtain ⟨h1, h2⟩ := timeoutInbox_grow hst hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => absurd (SysChoice.run.inj h) hp0⟩
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, _, _, hmbc⟩ := dog_signal_cases hi hg.noKill hsig
    have hst' : Waiting w b := by unfold Waiting; rw [hst]; exact hw
    rcases hmbc with ⟨_, hnew⟩ | ⟨_, hnew⟩
    · obtain ⟨h1, h2⟩ := timeoutInbox_grow hst' hmb hr hnew
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
    · obtain ⟨h1, h2⟩ := timeoutInbox_grow hst' hmb hr (new := []) (by rw [hnew, hmb]; simp)
      exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | down _ _ hdown =>
    obtain ⟨new, hnew⟩ := mboxOf_downE_append hdown 0
    obtain ⟨h1, h2⟩ := timeoutInbox_grow (by unfold Waiting; rw [downE_stateOf hdown]; exact hw) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩
  | timer _ i _ htimer =>
    obtain ⟨new, hnew⟩ := mboxOf_timerE_append htimer 0
    obtain ⟨h1, h2⟩ := timeoutInbox_grow (by unfold Waiting; rw [timerE_stateOf htimer]; exact hw) hmb hr hnew
    exact Or.inr ⟨h1, h2, fun h => nomatch h⟩

/-- **Stage 1.** With a fair `run 0`, the timeout in the mailbox leads to
the kill being queued or to a restart. -/
theorem timeoutInbox_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hfair : ρ.WeakFair (.run 0))
    (w : Pid) : LeadsTo ρ.st (TimeoutInbox w) (fun s => KillPending w s ∨ Replaced w s) := by
  apply ρ.rank_leads_to_of_step (.run 0) rankTimeout hfair
  · intro ch a b hr hl hp _
    exact timeoutInbox_step (reach_good h0 hr) hl hp
  · intro a _ ⟨hw, mb, hmb, hr⟩ _
    obtain ⟨mb', hget⟩ := hw.get
    have : mb = mb' := by simp [Config.mboxOf, hget] at hmb; exact hmb.symm
    subst this
    cases mb with
    | nil => cases hr
    | cons m rest => exact ⟨_, m, rest, hget⟩

/-! ### Stage 2: the kill is delivered -/

/-- Delivering the head signal `(w, 0, kill)` leaves `w` dead, whether it
was alive (untrappable kill) or already gone. -/
theorem kill_head_dead {w : Pid} {a b : Sys St Msg} {rest : List (Pid × Pid × Reason)}
    (hsg : a.signals = (w, 0, .kill) :: rest) (h : signalE sig a = some b) :
    (b.cfg.get w).isSome = false := by
  obtain ⟨q, src, r, rest', hsg', hc⟩ := signalE_cases h
  rw [hsg] at hsg'
  obtain ⟨hx, _⟩ := List.cons.inj hsg'
  obtain ⟨hq, hx2⟩ := Prod.mk.inj hx
  subst hq
  obtain ⟨hsrc, hr⟩ := Prod.mk.inj hx2
  subst hsrc
  subst hr
  rcases hc with ⟨hd, rfl⟩ | ⟨_, _, _, hne, _⟩ | ⟨_, _, _, hne, _⟩ | ⟨_, _, _, hne, _⟩ | ⟨_, _, _, rfl⟩
  · show (a.cfg.get w).isSome = false
    rw [hd]; rfl
  · exact absurd rfl hne
  · cases hne
  · cases hne
  · show ((a.cfg.remove w).get w).isSome = false
    rw [get_remove_self]; rfl

theorem killPending_step {w : Pid} {ch : SysChoice} {a b : Sys St Msg} (hg : Good a)
    (h : SysStepL beh sig ch a b) (hp : KillPending w a) :
    (Dead w b ∨ Replaced w b) ∨
      (KillPending w b ∧ rankKill w b ≤ rankKill w a ∧ (ch = .signal → rankKill w b < rankKill w a)) := by
  have hi := hg.inv
  obtain ⟨⟨k, hc⟩, hs⟩ := hp
  cases h with
  | run _ p _ hrun =>
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨m, rest, hget, hcase⟩ := dog_run_cases hc hrun
      rcases hcase with ⟨r, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · exact Or.inl (Or.inr (Replaced.spawnAt a rest hi.next_pos (hg.childLt w k hc)))
      · exact Or.inr ⟨⟨⟨true, pongAt_stateOf a w rest⟩, hs⟩, Nat.le_refl _, fun h => nomatch h⟩
      · refine Or.inr ⟨⟨⟨false, killAt_stateOf a w rest⟩, List.mem_append_left _ hs⟩, ?_, fun h => nomatch h⟩
        show (a.signals ++ [(w, 0, Reason.kill)]).findIdx (isKill w) ≤ a.signals.findIdx (isKill w)
        rw [rankKill_append hs]; exact Nat.le_refl _
      · exact Or.inr ⟨⟨⟨k, by simp [stateOf_set]⟩, hs⟩, Nat.le_refl _, fun h => nomatch h⟩
    · obtain ⟨new, hnew⟩ := runE_signals_append hrun
      refine Or.inr ⟨⟨⟨k, ?_⟩, by rw [hnew]; exact List.mem_append_left _ hs⟩, ?_, fun h => nomatch h⟩
      · rw [runE_stateOf_of_ne hrun (Ne.symm hp0) hi.next_pos]; exact hc
      · unfold rankKill; rw [hnew, rankKill_append hs]; exact Nat.le_refl _
  | signal _ _ hsig =>
    obtain ⟨q, src, r', rest, hsg, hst, ⟨new, hnew⟩, _, _⟩ := dog_signal_cases hi hg.noKill hsig
    by_cases hhead : (q, src, r') = (w, 0, Reason.kill)
    · rw [hhead] at hsg
      exact Or.inl (Or.inl ⟨⟨k, by rw [hst]; exact hc⟩, kill_head_dead hsg hsig⟩)
    · have hrest : (w, 0, Reason.kill) ∈ rest := by
        rw [hsg] at hs
        rcases List.mem_cons.mp hs with h | h
        · exact absurd h.symm hhead
        · exact h
      have hno : isKill w (q, src, r') = false := by
        simp only [isKill, decide_eq_false_iff_not]; exact hhead
      have hlt : rankKill w b < rankKill w a := by
        unfold rankKill
        rw [hnew, rankKill_append hrest, hsg, List.findIdx_cons_of_false hno]
        exact Nat.lt_succ_self _
      exact Or.inr ⟨⟨⟨k, by rw [hst]; exact hc⟩, by rw [hnew]; exact List.mem_append_left _ hrest⟩,
        Nat.le_of_lt hlt, fun _ => hlt⟩
  | down _ _ hdown =>
    refine Or.inr ⟨⟨⟨k, by rw [downE_stateOf hdown]; exact hc⟩, by rw [downE_signals hdown]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankKill; rw [downE_signals hdown]; exact Nat.le_refl _
  | timer _ i _ htimer =>
    refine Or.inr ⟨⟨⟨k, by rw [timerE_stateOf htimer]; exact hc⟩, by rw [timerE_signals htimer]; exact hs⟩,
      ?_, fun h => nomatch h⟩
    unfold rankKill; rw [timerE_signals htimer]; exact Nat.le_refl _

/-- **Stage 2.** With a fair `signal` step, the queued kill leads to a dead
`w` (still the current worker) or to a restart. -/
theorem killPending_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hfair : ρ.WeakFair .signal)
    (w : Pid) : LeadsTo ρ.st (KillPending w) (fun s => Dead w s ∨ Replaced w s) := by
  apply ρ.rank_leads_to_of_step .signal (rankKill w) hfair
  · intro ch a b hr hl hp _
    exact killPending_step (reach_good h0 hr) hl hp
  · intro a _ ⟨_, hs⟩ _
    show a.signals ≠ []
    intro hnil; rw [hnil] at hs; cases hs

/-! ### Stage 3: the dead worker is replaced, and stays dead -/

/-- `restart_eventually` plus no resurrection: the live worker it produces
is not `w`, because `w` is dead and stays dead. -/
theorem dead_leadsTo (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (hsig : ρ.WeakFair .signal)
    (hrun : ρ.WeakFair (.run 0)) (w : Pid) : LeadsTo ρ.st (Dead w) (Replaced w) := by
  intro t hd
  obtain ⟨⟨bb, hc⟩, hdead⟩ := hd
  obtain ⟨t', ht', w', bb', hc', hal⟩ := restart_eventually ρ h0 hsig hrun t w bb hc hdead
  refine ⟨t', ht', w', bb', hc', ?_, hal⟩
  intro heq
  rw [heq] at hal
  have hg : Good (ρ.st t) := reach_good h0 (ρ.reach t)
  have hlt : w < (ρ.st t).next := hg.childLt w bb hc
  have hnone : (ρ.st t').cfg.stateOf w = none :=
    (ρ.reach_from ht').stateOf_none hlt ((Config.isSome_eq_false_iff_stateOf_none _ _).mp hdead)
  rw [(Config.isSome_eq_false_iff_stateOf_none _ _).mpr hnone] at hal
  cases hal

/-! ### The second theorem -/

/-- **A worker the watchdog is waiting on is eventually replaced.** Along
any run from a `Good` system in which the `(0, timeout)` timer, the
`signal` step and the `run 0` step are fair: if at time `t` the watchdog
is `.watchdog (some w) true`, then at some `t' ≥ t` its current worker is
a live pid other than `w`. Nothing is assumed about `w`: hung, healthy or
already dead, it is killed by the untrappable `kill` (or was dead) and the
`EXIT` triggers the restart; no fairness of `run w` is needed. -/
theorem worker_replaced (ρ : SysRun beh sig) (h0 : Good (ρ.st 0)) (htimer : ρ.TimerFair 0 .timeout)
    (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) true) →
      ∃ t' ≥ t, ∃ w' bb, (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧
        ((ρ.st t').cfg.get w').isSome = true := by
  intro t w hw
  have hR := LeadsTo.refl ρ.st (Replaced w)
  have h3 := dead_leadsTo ρ h0 hsig hrun w
  have h2 := (killPending_leadsTo ρ h0 hsig w).trans (h3.or hR)
  have h1 := (timeoutInbox_leadsTo ρ h0 hrun w).trans (h2.or hR)
  have h0' := (waiting_leadsTo ρ h0 htimer w).trans (h1.or hR)
  obtain ⟨t', ht', h⟩ := h0' t hw
  exact ⟨t', ht', h⟩

/-- `worker_replaced` under weak fairness of every timer index. -/
theorem worker_replaced_of_weakFair (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ∀ i, ρ.WeakFair (.timer i)) (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) true) →
      ∃ t' ≥ t, ∃ w' bb, (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧
        ((ρ.st t').cfg.get w').isSome = true :=
  worker_replaced ρ h0 (ρ.timerFair_of_weakFair_timers htimer) hsig hrun

/-- **A hung worker is eventually replaced.** The statement asked for: at
time `t` the worker `w` is alive and hung and the watchdog is waiting for
its pong; under weak fairness of every timer index, of `run 0`, of
`signal` and of `run w`, at some `t' ≥ t` the current worker is a live pid
other than `w`. The hypotheses on `w` (its state and its fairness) are not
used: `worker_replaced` needs neither. -/
theorem hung_worker_replaced (ρ : SysRun beh sig) (h0 : Good (ρ.st 0))
    (htimer : ∀ i, ρ.WeakFair (.timer i)) (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0))
    {t : Nat} {w : Pid} {n : Nat} (_hw : (ρ.st t).cfg.stateOf w = some (.worker true n))
    (_hrunw : ρ.WeakFair (.run w)) (hdog : (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) true)) :
    ∃ t' ≥ t, ∃ w' bb, (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧
      ((ρ.st t').cfg.get w').isSome = true :=
  worker_replaced_of_weakFair ρ h0 htimer hsig hrun t w hdog

/-- The same from any system the environment can drive the watchdog to. -/
theorem worker_replaced_env (ρ : SysRun beh sig) (h0 : SysReachEnv beh sig init (ρ.st 0))
    (htimer : ∀ i, ρ.WeakFair (.timer i)) (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) true) →
      ∃ t' ≥ t, ∃ w' bb, (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧
        ((ρ.st t').cfg.get w').isSome = true :=
  worker_replaced_of_weakFair ρ (reachEnv_good h0) htimer hsig hrun

/-- From `init` itself (not vacuous: `start` puts the watchdog in
`.watchdog (some 1) true` after one closed step). -/
theorem worker_replaced_init (ρ : SysRun beh sig) (h0 : ρ.st 0 = init)
    (htimer : ∀ i, ρ.WeakFair (.timer i)) (hsig : ρ.WeakFair .signal) (hrun : ρ.WeakFair (.run 0)) :
    ∀ t w, (ρ.st t).cfg.stateOf 0 = some (.watchdog (some w) true) →
      ∃ t' ≥ t, ∃ w' bb, (ρ.st t').cfg.stateOf 0 = some (.watchdog (some w') bb) ∧ w' ≠ w ∧
        ((ρ.st t').cfg.get w').isSome = true :=
  worker_replaced_of_weakFair ρ (by rw [h0]; exact Good.init) htimer hsig hrun

/-! ### Non-vacuity: a hung worker, and a fair run from it -/

/-- Start; the environment tells worker 1 to hang; the worker answers the
ping and then hangs; the watchdog handles the pong (re-ping, re-arm). -/
def hung : Sys St Msg :=
  let s1 := runSys beh sig init [.run 0]
  runSys beh sig { s1 with cfg := s1.cfg.deliver 1 .hang } [.run 1, .run 1, .run 0]

/-- The premise of `hung_worker_replaced` is reachable: worker 1 is alive
and hung, the watchdog waits for its pong. -/
theorem hung_worker_reachable : SysReachEnv beh sig init hung ∧
    hung.cfg.stateOf 0 = some (.watchdog (some 1) true) ∧ hung.cfg.stateOf 1 = some (.worker true 1) :=
  ⟨.step (.run _ 0 _ rfl) (.env 1 .hang (.step (.run _ 1 _ rfl) (.step (.run _ 1 _ rfl)
      (.step (.run _ 0 _ rfl) (.refl _))))), rfl, rfl⟩

/-- The schedule of one cycle: the timer fires, the watchdog handles the
timeout, the kill is delivered, the `EXIT` is delivered, the watchdog
restarts. The worker never runs. -/
def cycChoice : Nat → SysChoice
  | 0 => .timer 0
  | 1 => .run 0
  | 2 => .signal
  | 3 => .signal
  | _ => .run 0

/-- The shape of the system at phase `ph` of the cycle whose worker is `k`
(spawned at `k`, so `next = k + 1`). -/
def Cyc (ph : Nat) (k : Pid) (s : Sys St Msg) : Prop :=
  k ≠ 0 ∧ s.next = k + 1 ∧ s.monitors = [] ∧ s.downs = [] ∧
  match ph with
  | 0 => s.cfg.get 0 = some ⟨.watchdog (some k) true, []⟩ ∧ (s.cfg.get k).isSome = true ∧
         s.links = [(0, k)] ∧ s.signals = [] ∧ s.timers = [(0, .timeout), (0, .timeout)]
  | 1 => s.cfg.get 0 = some ⟨.watchdog (some k) true, [.timeout]⟩ ∧ (s.cfg.get k).isSome = true ∧
         s.links = [(0, k)] ∧ s.signals = [] ∧ s.timers = [(0, .timeout)]
  | 2 => s.cfg.get 0 = some ⟨.watchdog (some k) false, []⟩ ∧ (s.cfg.get k).isSome = true ∧
         s.links = [(0, k)] ∧ s.signals = [(k, 0, .kill)] ∧ s.timers = [(0, .timeout)]
  | 3 => s.cfg.get 0 = some ⟨.watchdog (some k) false, []⟩ ∧ s.cfg.get k = none ∧
         s.links = [] ∧ s.signals = [(0, k, .error)] ∧ s.timers = [(0, .timeout)]
  | _ => s.cfg.get 0 = some ⟨.watchdog (some k) false, [.EXIT k .error]⟩ ∧ s.cfg.get k = none ∧
         s.links = [] ∧ s.signals = [] ∧ s.timers = [(0, .timeout)]

theorem Config.get_deliver_of_get {c : Config St Msg} {p : Pid} {x : Actor St Msg}
    (h : c.get p = some x) (m : Msg) :
    (c.deliver p m).get p = some { x with mailbox := x.mailbox ++ [m] } := by
  have h' : c.actors p = some x := h
  simp only [Config.deliver, h', get_set_self]

theorem Config.get_deliver_ne (c : Config St Msg) {p q : Pid} (m : Msg) (h : q ≠ p) :
    (c.deliver p m).get q = c.get q := by
  unfold Config.deliver
  cases c.actors p with
  | none => rfl
  | some a => exact get_set_ne _ _ h

theorem cyc_start : Cyc 0 1 hung :=
  ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One phase of the cycle. -/
theorem cyc_step (ph : Nat) (hph : ph < 5) (k : Pid) (s : Sys St Msg) (h : Cyc ph k s) :
    ∃ s', SysStepL beh sig (cycChoice ph) s s' ∧ Cyc ((ph + 1) % 5) (if ph = 4 then k + 1 else k) s' := by
  obtain ⟨hk0, hnext, hmon, hdn, h⟩ := h
  have h0k : (0 : Pid) ≠ k := Ne.symm hk0
  rcases ph with _ | _ | _ | _ | _ | ph
  · -- the timer fires
    obtain ⟨hget0, hk, hl, hs, ht⟩ := h
    refine ⟨{ s with cfg := s.cfg.deliver 0 .timeout, timers := [(0, .timeout)] },
      .timer _ 0 _ (by simp [timerE, ht]), hk0, hnext, hmon, hdn, ?_, ?_, hl, hs, rfl⟩
    · show (s.cfg.deliver 0 .timeout).get 0 = some ⟨.watchdog (some k) true, [.timeout]⟩
      rw [Config.get_deliver_of_get hget0]; rfl
    · show ((s.cfg.deliver 0 .timeout).get k).isSome = true
      rw [Config.get_deliver_ne _ _ h0k.symm]; exact hk
  · -- the watchdog handles the timeout: kill queued
    obtain ⟨hget0, hk, hl, hs, ht⟩ := h
    refine ⟨killAt s k [], .run _ 0 _ ?_, hk0, hnext, hmon, hdn, ?_, ?_, hl, ?_, ht⟩
    · simp [runE, hget0, beh, applyEffects, applyEffect, killAt]
    · show (s.cfg.set 0 ⟨.watchdog (some k) false, []⟩).get 0 = some ⟨.watchdog (some k) false, []⟩
      exact get_set_self _ _ _
    · show ((s.cfg.set 0 ⟨.watchdog (some k) false, []⟩).get k).isSome = true
      rw [get_set_ne _ _ hk0]; exact hk
    · show s.signals ++ [(k, 0, Reason.kill)] = [(k, 0, Reason.kill)]
      rw [hs]; rfl
  · -- the kill lands: the worker dies, its EXIT is queued
    obtain ⟨hget0, hk, hl, hs, ht⟩ := h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hk
    refine ⟨({ s with signals := [] } : Sys St Msg).terminate k .error, .signal _ _ ?_,
      hk0, hnext, ?_, ?_, ?_, ?_, ?_, ?_, ht⟩
    · simp [signalE, hs, ha]
    · show unmonitor s.monitors k = []
      rw [hmon]; rfl
    · show s.downs ++ (watchers s.monitors k).map _ = []
      rw [hdn, hmon]; rfl
    · show (s.cfg.remove k).get 0 = some ⟨.watchdog (some k) false, []⟩
      rw [get_remove_ne _ h0k]; exact hget0
    · show (s.cfg.remove k).get k = none
      exact get_remove_self _ _
    · show unlink s.links k = []
      rw [hl]; simp [unlink, hk0]
    · show [] ++ (linkedTo s.links k).map (fun q => (q, k, Reason.error)) = [(0, k, Reason.error)]
      rw [hl]; simp [linkedTo, hk0, h0k]
  · -- the EXIT lands in the watchdog's mailbox
    obtain ⟨hget0, hk, hl, hs, ht⟩ := h
    refine ⟨{ s with signals := [], cfg := s.cfg.deliver 0 (.EXIT k .error) }, .signal _ _ ?_,
      hk0, hnext, hmon, hdn, ?_, ?_, hl, rfl, ht⟩
    · simp [signalE, hs, hget0, sig]
    · show (s.cfg.deliver 0 (.EXIT k .error)).get 0 = some ⟨.watchdog (some k) false, [.EXIT k .error]⟩
      rw [Config.get_deliver_of_get hget0]; rfl
    · show (s.cfg.deliver 0 (.EXIT k .error)).get k = none
      rw [Config.get_deliver_ne _ _ h0k.symm]; exact hk
  · -- the restart: a fresh worker at `s.next`, pinged, the timer armed
    obtain ⟨hget0, hk, hl, hs, ht⟩ := h
    have hn0 : s.next ≠ 0 := by rw [hnext]; exact Nat.succ_ne_zero _
    rw [if_pos rfl, ← hnext]
    refine ⟨spawnAt s [], .run _ 0 _ ?_, hn0, rfl, hmon, hdn, ?_, ?_, ?_, hs, ?_⟩
    · simp [runE, hget0, beh, applyEffects, applyEffect, spawnAt]
    · show (((s.cfg.set 0 ⟨.watchdog (some s.next) true, []⟩).set s.next ⟨.worker false 0, []⟩).deliver
          s.next .ping).get 0 = some ⟨.watchdog (some s.next) true, []⟩
      rw [Config.get_deliver_ne _ _ hn0.symm, get_set_ne _ _ hn0.symm, get_set_self]
    · show ((((s.cfg.set 0 ⟨.watchdog (some s.next) true, []⟩).set s.next ⟨.worker false 0, []⟩).deliver
          s.next .ping).get s.next).isSome = true
      rw [Config.get_deliver_of_get (get_set_self _ _ _)]; rfl
    · show (0, s.next) :: s.links = [(0, s.next)]
      rw [hl]
    · show s.timers ++ [(0, (.timeout : Msg))] = [(0, .timeout), (0, .timeout)]
      rw [ht]; rfl
  · exact absurd hph (by omega)

/-- **A fair run exists from the hung system.** It starts in `hung`, and is
weakly fair for `signal`, for `run 0`, for every timer index and for `run
1` (the hung worker: killed in the first cycle and never resurrected, so
`run 1` is disabled from then on). Together with `hung_worker_reachable`
and `reachEnv_good`, the hypotheses of `hung_worker_replaced` are jointly
satisfiable at `t = 0`. -/
theorem hung_fair_run : ∃ ρ : SysRun beh sig, ρ.st 0 = hung ∧ Good (ρ.st 0) ∧
    ρ.WeakFair .signal ∧ ρ.WeakFair (.run 0) ∧ (∀ i, ρ.WeakFair (.timer i)) ∧ ρ.WeakFair (.run 1) := by
  have hstep : ∀ t s, Cyc (t % 5) (1 + t / 5) s →
      ∃ s', SysStepL beh sig (cycChoice (t % 5)) s s' ∧ Cyc ((t + 1) % 5) (1 + (t + 1) / 5) s' := by
    intro t s h
    obtain ⟨s', hl, hc⟩ := cyc_step (t % 5) (Nat.mod_lt _ (by decide)) _ s h
    refine ⟨s', hl, ?_⟩
    have hmod : (t + 1) % 5 = (t % 5 + 1) % 5 := by omega
    rw [hmod]
    by_cases h4 : t % 5 = 4
    · rw [if_pos h4] at hc
      have : 1 + (t + 1) / 5 = 1 + t / 5 + 1 := by omega
      rw [this]; exact hc
    · rw [if_neg h4] at hc
      have : 1 + (t + 1) / 5 = 1 + t / 5 := by omega
      rw [this]; exact hc
  obtain ⟨ρ, hst0, hch, hinv⟩ := SysRun.exists_of_inv beh sig (I := fun t s => Cyc (t % 5) (1 + t / 5) s)
    (fun t => cycChoice (t % 5)) (s0 := hung) cyc_start hstep
  refine ⟨ρ, hst0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst0]; exact reachEnv_good hung_worker_reachable.1
  · right; intro t
    refine ⟨5 * t + 2, by omega, ?_⟩
    rw [hch]
    have : (5 * t + 2) % 5 = 2 := by omega
    rw [this]; rfl
  · right; intro t
    refine ⟨5 * t + 1, by omega, ?_⟩
    rw [hch]
    have : (5 * t + 1) % 5 = 1 := by omega
    rw [this]; rfl
  · intro i
    cases i with
    | zero =>
      right; intro t
      refine ⟨5 * t, by omega, ?_⟩
      rw [hch]
      have : (5 * t) % 5 = 0 := by omega
      rw [this]; rfl
    | succ i =>
      left; intro t
      refine ⟨5 * t + 1, by omega, ?_⟩
      have h := hinv (5 * t + 1)
      have hm : (5 * t + 1) % 5 = 1 := by omega
      simp only [hm] at h
      obtain ⟨_, _, _, _, _, _, _, _, ht⟩ := h
      show ¬ (i + 1 < (ρ.st (5 * t + 1)).timers.length)
      rw [ht]; simp
  · left; intro t
    refine ⟨5 * t + 3, by omega, ?_⟩
    have h3 : Cyc 3 1 (ρ.st 3) := hinv 3
    obtain ⟨_, hn, _, _, _, hk, _⟩ := h3
    have hnone : (ρ.st (5 * t + 3)).cfg.stateOf 1 = none :=
      (ρ.reach_from (show 3 ≤ 5 * t + 3 by omega)).stateOf_none (by rw [hn]; decide)
        (by simp [Config.stateOf, hk])
    rintro ⟨st, m, rest, hget⟩
    simp [Config.stateOf, hget] at hnone

end Examples.Watchdog

end Leanactors
