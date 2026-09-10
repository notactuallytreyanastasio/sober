import Leanactors.SysProps
import Leanactors.Examples.Supervisor
/-!
# Leanactors.Examples.SupervisorProof

`Inv` is preserved by every `SysStep`. Two shapes cover all cases:

* `Inv.frame`: steps that only *add* (deliveries, spawns by anyone, signal
  delivery to the trapping supervisor, no-op runs). Everything the invariant
  looks at is monotone, except that a consumed signal may turn into a
  mailbox message. `Inv.grows` is its instance for `Sys.Grows`.
* `Inv.terminate_ne`: an actor other than the supervisor dies. If it was
  the current child, its link produces the pending signal the invariant
  needs. `Inv.terminate_frame` is its instance for `Sys.Frame`.

With `Leanactors.SysProps` the case analysis is by pid, not by message: an
actor other than the supervisor either survives its step (`Frame` plus
`Grows`) or dies (`terminate_frame`), whatever it popped. Only the
supervisor's own steps look at the message: a spawn or a no-op.

The supervisor at pid 0 itself never dies: it never emits `exit`, and it
traps, so signals reach it as messages.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Supervisor

open Leanactors Config Sys

/-! ### The two shapes -/

theorem Inv.frame {a b : Sys St Msg} (hi : Inv a)
    (hnext : a.next ≤ b.next)
    (hsup : b.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, (a.cfg.get c).isSome → (b.cfg.get c).isSome)
    (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ b.links)
    (hsigs : ∀ c r, (0, c, r) ∈ a.signals → (0, c, r) ∈ b.signals ∨ 0 < b.cfg.mcount 0 (.EXIT c r))
    (hcount : ∀ c k r, a.cfg.stateOf 0 = some (.sup (some c) k) →
      a.cfg.mcount 0 (.EXIT c r) ≤ b.cfg.mcount 0 (.EXIT c r)) : Inv b := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_⟩
  · obtain ⟨child, k, h⟩ := hi.sup_alive
    exact ⟨child, k, by rw [hsup]; exact h⟩
  · intro c k hc
    rw [hsup] at hc
    rcases hi.child_ok c k hc with ⟨hal, hl⟩ | ⟨r, hs⟩ | ⟨r, hm⟩
    · exact Or.inl ⟨halive c hal, hlinks c hl⟩
    · rcases hsigs c r hs with h | h
      · exact Or.inr (Or.inl ⟨r, h⟩)
      · exact Or.inr (Or.inr ⟨r, h⟩)
    · exact Or.inr (Or.inr ⟨r, Nat.lt_of_lt_of_le hm (hcount c k r hc)⟩)

/-- `Inv` only looks at `next`, states, liveness, links, signals and counts,
all of which are monotone along `Grows`. -/
theorem Inv.grows {a b : Sys St Msg} (hi : Inv a) (h : Grows a b) : Inv b :=
  Inv.frame hi h.next (h.stateOf 0 hi.next_pos) h.alive (fun c => h.links (0, c))
    (fun _ _ hs => Or.inl (h.signals _ hs)) (fun _ _ _ _ => h.mcount 0 _ hi.next_pos)

/-- Overwriting an actor other than the supervisor (the popped mailbox,
the new state) changes nothing the invariant sees. -/
theorem Inv.set_ne {a : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (x : Actor St Msg) :
    Inv { a with cfg := a.cfg.set p x } :=
  let f := frame_set a p x
  Inv.frame hi f.next (f.stateOf 0 (Ne.symm hp) hi.next_pos)
    (fun c h => by rw [isSome_set]; split <;> simp [h]) (fun _ h => h)
    (fun _ _ hs => Or.inl hs) (fun _ _ _ _ => f.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-- `Inv` ignores `timers` and `downs`. -/
theorem Inv.set_timers {a : Sys St Msg} (hi : Inv a) (t : List (Pid × Msg)) :
    Inv { a with timers := t } := ⟨hi.next_pos, hi.sup_alive, hi.child_ok⟩

theorem Inv.set_downs {a : Sys St Msg} (hi : Inv a) (d : List (Pid × Pid × Reason)) :
    Inv { a with downs := d } := ⟨hi.next_pos, hi.sup_alive, hi.child_ok⟩

/-- Dropping the head signal when it is not addressed to the supervisor. -/
theorem Inv.pop_signal {a : Sys St Msg} (hi : Inv a) {q src : Pid} {r : Reason}
    {rest : List (Pid × Pid × Reason)} (hsg : a.signals = (q, src, r) :: rest) (hq : q ≠ 0) :
    Inv { a with signals := rest } :=
  ⟨hi.next_pos, hi.sup_alive, fun c k hc => by
    rcases hi.child_ok c k hc with h | ⟨r', hs⟩ | h
    · exact Or.inl h
    · rw [hsg] at hs
      rcases List.mem_cons.mp hs with hs | hs
      · cases hs; exact absurd rfl hq
      · exact Or.inr (Or.inl ⟨r', hs⟩)
    · exact Or.inr (Or.inr h)⟩

/-- An actor `p ≠ 0` terminates from an intermediate system `s` that has
`a`'s supervisor links, a supervisor state and mailbox no smaller than
`a`'s, and `a`'s supervisor-bound signals. -/
theorem Inv.terminate_core {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ s.links)
    (hsup : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.EXIT c r') ≤ s.cfg.mcount 0 (.EXIT c r')) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_⟩
  · obtain ⟨child, k, h⟩ := hi.sup_alive
    exact ⟨child, k, by rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hsup, h]⟩
  · intro c k hc
    rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hsup] at hc
    rcases hi.child_ok c k hc with ⟨hal, hl⟩ | ⟨r', hs⟩ | ⟨r', hm⟩
    · by_cases hcp : c = p
      · subst hcp
        exact Or.inr (Or.inl ⟨r, terminate_signal_of_link _ _ _ (hlinks _ hl)⟩)
      · exact Or.inl ⟨by rw [terminate_isSome_ne _ _ _ hcp]; exact halive c hcp hal,
          terminate_mem_links _ _ _ (hlinks _ hl) (Ne.symm hp) hcp⟩
    · exact Or.inr (Or.inl ⟨r', terminate_mem_signals _ _ _ (hsigs c r' hs)⟩)
    · exact Or.inr (Or.inr ⟨r', by
        rw [terminate_mcount_ne _ _ _ (Ne.symm hp)]; exact Nat.lt_of_lt_of_le hm (hcount c r')⟩)

theorem Inv.terminate_ne {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = a.links)
    (hsup : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.EXIT c r') ≤ s.cfg.mcount 0 (.EXIT c r')) :
    Inv (s.terminate p r) :=
  hi.terminate_core hp r hnext (fun _ h => hlinks ▸ h) hsup halive hsigs hcount

/-- The same from a `Frame p a s` that keeps the supervisor's links. -/
theorem Inv.terminate_frame {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hf : Frame p a s) (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ s.links) :
    Inv (s.terminate p r) :=
  hi.terminate_core hp r hf.next hlinks (hf.stateOf 0 (Ne.symm hp) hi.next_pos) hf.alive
    (fun _ _ => hf.signals _) (fun _ _ => hf.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-! ### The supervisor's own steps -/

/-- The supervisor never emits `exit`. -/
theorem sup_no_exit (me fresh : Pid) (c : Option Pid) (k : Nat) (m : Msg) (r : Reason) :
    Effect.exit r ∉ (beh me fresh (.sup c k) m).2 := by
  cases c <;> cases m <;> simp [beh] <;> split <;> simp

/-- The supervisor traps. -/
theorem sup_traps {a : Sys St Msg} (hi : Inv a) {act : Actor St Msg} (hget : a.cfg.get 0 = some act) :
    sig.traps act.state = true := by
  obtain ⟨child, k, hsup⟩ := hi.sup_alive
  simp [stateOf, hget] at hsup
  rw [hsup]; rfl

/-- The spawn shape: `start` on a childless supervisor, or a restart. -/
theorem Inv.sup_spawn {a : Sys St Msg} (hi : Inv a) (k : Nat) (rest : List Msg) :
    Inv { a with cfg := (a.cfg.set 0 ⟨.sup (some a.next) k, rest⟩).set a.next ⟨.worker 0, []⟩,
                 next := a.next + 1, links := (0, a.next) :: a.links } := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hi.next_pos
  refine ⟨Nat.succ_pos _, ⟨some a.next, k, by simp [stateOf_set, Ne.symm hn0]⟩, ?_⟩
  intro c kk hc
  simp [stateOf_set, Ne.symm hn0] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact Or.inl ⟨by simp [isSome_set], by simp⟩

/-- The no-op shape: the supervisor consumes a message that is not its
current child's `EXIT` and keeps its state. -/
theorem Inv.sup_noop {a : Sys St Msg} (hi : Inv a) {child : Option Pid} {k : Nat} {m : Msg}
    {rest : List Msg} (hget : a.cfg.get 0 = some ⟨.sup child k, m :: rest⟩)
    (hm : ∀ c r, child = some c → m ≠ .EXIT c r) :
    Inv { a with cfg := a.cfg.set 0 ⟨.sup child k, rest⟩ } := by
  refine ⟨hi.next_pos, ⟨child, k, by simp [stateOf_set]⟩, ?_⟩
  intro c k' hc
  simp [stateOf_set] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rcases hi.child_ok c k (by simp [stateOf, hget]) with ⟨hal, hl⟩ | ⟨r, hs⟩ | ⟨r, hm'⟩
  · exact Or.inl ⟨by rw [isSome_set]; split <;> simp [hal], hl⟩
  · exact Or.inr (Or.inl ⟨r, hs⟩)
  · refine Or.inr (Or.inr ⟨r, ?_⟩)
    rw [mcount_of_get hget, if_neg (hm c r rfl)] at hm'
    rw [mcount_set, if_pos rfl]
    simpa using hm'

/-! ### Preservation, one lemma per kind of step -/

/-- Any actor other than the supervisor, popping any message: it survives
(`set` then `Grows`) or dies (`terminate_frame`). -/
theorem Inv.run_ne {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a)
    (hp : p ≠ 0) : Inv b := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  have hg := applyEffects_grows p { a with cfg := a.cfg.set p ⟨(beh p a.next st m).1, rest⟩ }
    (beh p a.next st m).2
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact (hi.set_ne hp _).grows hg
  · exact (hi.set_ne hp _).terminate_frame hp reason (hg.frame p) (fun c => hg.links (0, c))

theorem Inv.run {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a) : Inv b := by
  by_cases hp : p = 0
  · subst hp
    obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
    obtain ⟨child, k, hsup⟩ := hi.sup_alive
    simp [stateOf, hget] at hsup
    subst hsup
    simp only at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · cases child with
      | none =>
        cases m with
        | start =>
          simp only [beh, applyEffects, List.foldl, applyEffect]
          exact hi.sup_spawn _ _
        | _ =>
          simp only [beh]
          exact (hi.sup_noop hget (fun _ _ hc _ => nomatch hc)).grows (applyEffects_grows _ _ _)
      | some c' =>
        cases m with
        | EXIT who r =>
          by_cases hw : who = c'
          · subst hw
            simp only [beh, if_true, applyEffects, List.foldl, applyEffect]
            exact hi.sup_spawn _ _
          · simp only [beh, hw, if_false]
            exact (hi.sup_noop hget (fun _ _ hc h => by cases hc; cases h; exact hw rfl)).grows
              (applyEffects_grows _ _ _)
        | _ =>
          simp only [beh]
          exact (hi.sup_noop hget (fun _ _ _ h => nomatch h)).grows (applyEffects_grows _ _ _)
    · exact absurd (applyEffects_snd_some _ _ _ hr) (sup_no_exit _ _ _ _ _ _)
  · exact hi.run_ne h hp

/-- A signal to the supervisor becomes an `EXIT` message (it traps); a
signal to anyone else is a `Grows` or a termination. -/
theorem Inv.signal {a b : Sys St Msg} (h : signalE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  by_cases hq : q = 0
  · subst hq
    rcases hc with ⟨hd, _⟩ | ⟨act, hget, _, rfl⟩ | ⟨act, hget, htr, _, _⟩ | ⟨act, hget, htr, _, _⟩
    · obtain ⟨_, _, hsup⟩ := hi.sup_alive
      simp [stateOf, hd] at hsup
    · refine Inv.frame hi (Nat.le_refl _) (stateOf_deliver _ _ _ _)
        (fun c h => by rw [isSome_deliver]; exact h) (fun _ h => h) ?_
        (fun _ _ _ _ => by rw [mcount_deliver]; omega)
      intro c r' hs
      rw [hsg] at hs
      rcases List.mem_cons.mp hs with hs | hs
      · cases hs
        right; rw [mcount_deliver]; simp [sig, hget]
      · exact Or.inl hs
    all_goals rw [sup_traps hi hget] at htr; cases htr
  · have hpop := hi.pop_signal hsg hq
    rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
    · exact hpop
    · exact hpop.grows (grows_deliver _ _ _)
    · exact hpop
    · exact hpop.terminate_frame hq _ (Frame.refl _ _) (fun _ h => h)

/-- This program declares no DOWN codec, but the proof does not need to know. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, rest, _, hg⟩ := downE_grows h
  exact (hi.set_downs rest).grows hg

theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b :=
  (hi.set_timers _).grows (timerE_grows h)

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  cases h with
  | run p _ hrun => exact hi.run hrun
  | signal _ hsig => exact hi.signal hsig
  | down _ hdown => exact hi.down hdown
  | timer i _ htimer => exact hi.timer htimer

/-! ### From the initial system -/

theorem init_inv : Inv init := by
  refine ⟨by decide, ⟨none, 0, by simp [init, stateOf, Config.get]⟩, ?_⟩
  intro c k h
  simp [init, stateOf, Config.get] at h

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv (fun h hi => Inv.step h hi) init_inv

/-- **The supervisor never dies.** -/
theorem supervisor_alive {s : Sys St Msg} (hr : SysReach beh sig init s) :
    ∃ child k, s.cfg.stateOf 0 = some (.sup child k) :=
  (reach_inv hr).sup_alive

/-- **A missing child always has its restart in flight**: either the exit
signal is pending or the `EXIT` message is already in the supervisor's
mailbox. -/
theorem restart_in_flight {s : Sys St Msg} (hr : SysReach beh sig init s)
    {c : Pid} {k : Nat} (hc : s.cfg.stateOf 0 = some (.sup (some c) k))
    (hdead : (s.cfg.get c).isSome = false) :
    (∃ r, (0, c, r) ∈ s.signals) ∨ ∃ r, 0 < s.cfg.mcount 0 (.EXIT c r) := by
  rcases (reach_inv hr).child_ok c k hc with ⟨hal, _⟩ | h | h
  · rw [hdead] at hal; cases hal
  · exact Or.inl h
  · exact Or.inr h

end Leanactors.Examples.Supervisor
