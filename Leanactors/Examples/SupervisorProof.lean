import Leanactors.Examples.Supervisor
/-!
# Leanactors.Examples.SupervisorProof

`Inv` is preserved by every `SysStep`. Two shapes cover all cases:

* `Inv.frame`: steps that only *add* (deliveries, spawns by anyone, signal
  delivery to the trapping supervisor, no-op runs). Everything the invariant
  looks at is monotone, except that a consumed signal may turn into a
  mailbox message.
* `Inv.terminate_ne`: an actor other than the supervisor dies. If it was
  the current child, its link produces the pending signal the invariant
  needs.

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
    (hsigs : ∀ c r, (0, c, r) ∈ a.signals → (0, c, r) ∈ b.signals ∨ 0 < b.cfg.mcount 0 (.exited c r))
    (hcount : ∀ c k r, a.cfg.stateOf 0 = some (.sup (some c) k) →
      a.cfg.mcount 0 (.exited c r) ≤ b.cfg.mcount 0 (.exited c r)) : Inv b := by
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

/-- An actor `p ≠ 0` terminates from an intermediate system `s` that has
`a`'s links, a supervisor state and mailbox no smaller than `a`'s, and
`a`'s supervisor-bound signals. -/
theorem Inv.terminate_ne {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = a.links)
    (hsup : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.exited c r') ≤ s.cfg.mcount 0 (.exited c r')) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_⟩
  · obtain ⟨child, k, h⟩ := hi.sup_alive
    refine ⟨child, k, ?_⟩
    simp [terminate, stateOf_remove, Ne.symm hp, hsup, h]
  · intro c k hc
    simp only [terminate, stateOf_remove, Ne.symm hp, if_false, hsup] at hc
    rcases hi.child_ok c k hc with ⟨hal, hl⟩ | ⟨r', hs⟩ | ⟨r', hm⟩
    · by_cases hcp : c = p
      · subst hcp
        right; left
        refine ⟨r, ?_⟩
        simp only [terminate]
        apply List.mem_append_right
        rw [List.mem_map]
        exact ⟨0, mem_linkedTo_of_mem (hlinks ▸ hl), rfl⟩
      · left
        refine ⟨?_, ?_⟩
        · simp only [terminate, isSome_remove, hcp, if_false]
          exact halive c hcp hal
        · simp only [terminate]
          exact mem_unlink (hlinks ▸ hl) (Ne.symm hp) hcp
    · right; left
      exact ⟨r', by simp only [terminate]; exact List.mem_append_left _ (hsigs c r' hs)⟩
    · right; right
      refine ⟨r', ?_⟩
      simp only [terminate, mcount_remove, Ne.symm hp, if_false]
      exact Nat.lt_of_lt_of_le hm (hcount c r')

theorem worker_ne_zero {s : Sys St Msg} (hi : Inv s) {p : Pid} {n : Nat} {mb : List Msg}
    (h : s.cfg.get p = some ⟨.worker n, mb⟩) : p ≠ 0 := by
  intro e
  subst e
  obtain ⟨child, k, hs⟩ := hi.sup_alive
  simp [stateOf, h] at hs

/-! ### Preservation -/

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  obtain ⟨child, k, hsup⟩ := hi.sup_alive
  have hnext := hi.next_pos
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hnext
  cases h with
  | run p _ hrun =>
    unfold runE at hrun
    cases hget : a.cfg.get p with
    | none => simp [hget] at hrun
    | some act =>
      obtain ⟨st, mb⟩ := act
      cases mb with
      | nil => simp [hget] at hrun
      | cons m rest =>
        simp only [hget] at hrun
        have hpop := mcount_of_get hget
        cases st with
        | worker n =>
          have hp : p ≠ 0 := worker_ne_zero hi hget
          -- shared facts for every worker step: the supervisor's view of `set p`
          have hst : ∀ st', (a.cfg.set p ⟨st', rest⟩).stateOf 0 = a.cfg.stateOf 0 := fun st' => by
            simp [stateOf_set, Ne.symm hp]
          have hcnt : ∀ st' x, a.cfg.mcount 0 x ≤ (a.cfg.set p ⟨st', rest⟩).mcount 0 x := fun st' x => by
            simp [mcount_set, Ne.symm hp]
          have hal : ∀ st' c, (a.cfg.get c).isSome → ((a.cfg.set p ⟨st', rest⟩).get c).isSome := fun st' c h => by
            rw [isSome_set]; split <;> simp_all
          cases m with
          | crash =>
            simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.terminate_ne hi hp _ (Nat.le_refl _) rfl (hst _) (fun c _ => hal _ c)
              (fun _ _ h => h) (fun _ _ => hcnt _ _)
          | stop =>
            simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.terminate_ne hi hp _ (Nat.le_refl _) rfl (hst _) (fun c _ => hal _ c)
              (fun _ _ h => h) (fun _ _ => hcnt _ _)
          | job =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun c _ r _ => hcnt _ _)
          | start =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun c _ r _ => hcnt _ _)
          | exited who r =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun c _ r _ => hcnt _ _)
        | sup child' k' =>
          -- if this is the real supervisor, its state is `child`, `k`
          have hp0 : p = 0 → child' = child ∧ k' = k := by
            intro e; subst e
            simp [stateOf, hget] at hsup
            exact ⟨hsup.1, hsup.2⟩
          -- the spawn shape, for `start` on a childless sup and for a restart
          have spawn_case : ∀ k'' (rest' : List Msg),
              Inv { cfg := (a.cfg.set p ⟨.sup (some a.next) k'', rest'⟩).set a.next ⟨.worker 0, []⟩,
                    next := a.next + 1, links := (p, a.next) :: a.links, signals := a.signals } := by
            intro k'' rest'
            by_cases hp : p = 0
            · subst hp
              refine ⟨Nat.succ_pos _, ⟨some a.next, k'', by simp [stateOf_set, Ne.symm hn0]⟩, ?_⟩
              intro c kk hc
              simp [stateOf_set, Ne.symm hn0] at hc
              obtain ⟨rfl, rfl⟩ := hc
              exact Or.inl ⟨by simp [isSome_set], by simp⟩
            · apply Inv.frame hi (by simp) (by simp [stateOf_set, Ne.symm hp, Ne.symm hn0])
              · intro c h; rw [isSome_set]; split
                · rfl
                · rw [isSome_set]; split <;> simp_all
              · intro c h; exact List.mem_cons_of_mem _ h
              · intro c r h; exact Or.inl h
              · intro c kk r _; simp [mcount_set, Ne.symm hp, Ne.symm hn0]
          -- the no-op shape: state unchanged, message consumed
          have noop_case : ∀ (hm : ∀ c r, child' = some c → m ≠ .exited c r),
              Inv { a with cfg := a.cfg.set p ⟨.sup child' k', rest⟩ } := by
            intro hm
            by_cases hp : p = 0
            · subst hp
              obtain ⟨rfl, rfl⟩ := hp0 rfl
              apply Inv.frame hi
              · exact Nat.le_refl _
              · simp [stateOf_set, hsup]
              · intro c h; rw [isSome_set]; split <;> simp_all
              · intro c h; exact h
              · intro c r h; exact Or.inl h
              · intro c kk r hc
                rw [hsup] at hc
                simp at hc
                obtain ⟨rfl, rfl⟩ := hc
                rw [mcount_set]
                simp only [if_true]
                rw [hpop]
                simp [hm c r rfl]
            · apply Inv.frame hi
              · exact Nat.le_refl _
              · simp [stateOf_set, Ne.symm hp]
              · intro c h; rw [isSome_set]; split <;> simp_all
              · intro c h; exact h
              · intro c r h; exact Or.inl h
              · intro c kk r _; simp [mcount_set, Ne.symm hp]
          cases child' with
          | none =>
            cases m with
            | start =>
              simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
              obtain rfl := Option.some.inj hrun
              exact spawn_case _ _
            | job =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; cases h)
            | crash =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; cases h)
            | stop =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; cases h)
            | exited who r =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; cases h)
          | some c' =>
            cases m with
            | exited who r =>
              by_cases hw : who = c'
              · subst hw
                simp only [beh, if_true, applyEffects, List.foldl, applyEffect] at hrun
                obtain rfl := Option.some.inj hrun
                exact spawn_case _ _
              · simp only [beh, hw, if_false, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                exact noop_case (by intro c r' hc; cases hc; simp [hw])
            | start =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; simp)
            | job =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; simp)
            | crash =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; simp)
            | stop =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (by intro c r h; simp)
  | signal _ hsig =>
    unfold signalE at hsig
    cases hsg : a.signals with
    | nil => simp [hsg] at hsig
    | cons head rest =>
      obtain ⟨q, src, r⟩ := head
      simp only [hsg] at hsig
      -- a supervisor-bound signal in `a` is either this head or in `rest`
      have hrest : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') = (q, src, r) ∨ (0, c, r') ∈ rest := by
        intro c r' h; rw [hsg] at h; exact List.mem_cons.mp h
      cases hq : a.cfg.get q with
      | none =>
        simp only [hq] at hsig
        obtain rfl := Option.some.inj hsig
        have hq0 : q ≠ 0 := by
          intro e; subst e; simp [stateOf, hq] at hsup
        apply Inv.frame hi
        · exact Nat.le_refl _
        · rfl
        · intro _ h; exact h
        · intro _ h; exact h
        · intro c r' h
          rcases hrest c r' h with h | h
          · cases h; exact absurd rfl hq0
          · exact Or.inl h
        · intro _ _ _ _; exact Nat.le_refl _
      | some act =>
        simp only [hq] at hsig
        by_cases htr : sig.traps act.state = true
        · rw [if_pos htr] at hsig
          obtain rfl := Option.some.inj hsig
          apply Inv.frame hi
          · exact Nat.le_refl _
          · exact stateOf_deliver _ _ _ _
          · intro c h; rw [isSome_deliver]; exact h
          · intro c h; exact h
          · intro c r' h
            rcases hrest c r' h with h | h
            · cases h
              right
              rw [mcount_deliver]
              simp [sig, hq]
            · exact Or.inl h
          · intro c kk r' _
            rw [mcount_deliver]
            omega
        · -- a non-trapping target is not the supervisor
          have hq0 : q ≠ 0 := by
            intro e; subst e
            simp [stateOf, hq] at hsup
            have : act.state = .sup child k := hsup
            simp [sig, this] at htr
          rw [if_neg htr] at hsig
          cases r with
          | normal =>
            obtain rfl := Option.some.inj hsig
            apply Inv.frame hi
            · exact Nat.le_refl _
            · rfl
            · intro _ h; exact h
            · intro _ h; exact h
            · intro c r' h
              rcases hrest c r' h with h | h
              · cases h; exact absurd rfl hq0
              · exact Or.inl h
            · intro _ _ _ _; exact Nat.le_refl _
          | error =>
            obtain rfl := Option.some.inj hsig
            apply Inv.terminate_ne hi hq0
            · exact Nat.le_refl _
            · rfl
            · rfl
            · intro _ _ h; exact h
            · intro c r' h
              rcases hrest c r' h with h | h
              · cases h; exact absurd rfl hq0
              · exact h
            · intro _ _; exact Nat.le_refl _

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
    (∃ r, (0, c, r) ∈ s.signals) ∨ ∃ r, 0 < s.cfg.mcount 0 (.exited c r) := by
  rcases (reach_inv hr).child_ok c k hc with ⟨hal, _⟩ | h | h
  · rw [hdead] at hal; cases hal
  · exact Or.inl h
  · exact Or.inr h

end Leanactors.Examples.Supervisor
