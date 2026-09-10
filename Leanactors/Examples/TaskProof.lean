import Leanactors.Examples.Task
/-!
# Leanactors.Examples.TaskProof

`Inv` is preserved by every `SysStep`. Same two shapes as the supervisor
(`Inv.frame` for steps that only add, `Inv.terminate_ne` for a dying
worker) plus one more: the caller clearing its pending job, which makes
`pending_ok` vacuous.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Task

open Leanactors Config Sys

/-! ### The three shapes -/

theorem Inv.frame {a b : Sys St Msg} (hi : Inv a)
    (hnext : a.next ≤ b.next)
    (hlinks : b.links = []) (hsigs : b.signals = [])
    (hcal : b.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, (a.cfg.get c).isSome → (b.cfg.get c).isSome)
    (hmon : ∀ w, (0, w) ∈ a.monitors → (0, w) ∈ b.monitors)
    (hdowns : ∀ w rs, (0, w, rs) ∈ a.downs → (0, w, rs) ∈ b.downs ∨ 0 < b.cfg.mcount 0 (.DOWN w rs))
    (hreply : ∀ w r v, a.cfg.stateOf 0 = some (.caller (some w) r) →
      a.cfg.mcount 0 (.reply v) ≤ b.cfg.mcount 0 (.reply v))
    (hdcnt : ∀ w r rs, a.cfg.stateOf 0 = some (.caller (some w) r) →
      a.cfg.mcount 0 (.DOWN w rs) ≤ b.cfg.mcount 0 (.DOWN w rs)) : Inv b := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, hlinks, hsigs, ?_, ?_⟩
  · obtain ⟨w, r, h⟩ := hi.caller_alive
    exact ⟨w, r, by rw [hcal]; exact h⟩
  · intro w r hc
    rw [hcal] at hc
    rcases hi.pending_ok w r hc with ⟨hal, hm⟩ | ⟨rs, hd⟩ | ⟨v, hv⟩ | ⟨rs, hd⟩
    · exact Or.inl ⟨halive w hal, hmon w hm⟩
    · rcases hdowns w rs hd with h | h
      · exact Or.inr (Or.inl ⟨rs, h⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨rs, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨v, Nat.lt_of_lt_of_le hv (hreply w r v hc)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rs, Nat.lt_of_lt_of_le hd (hdcnt w r rs hc)⟩))

/-- The caller at 0 moved to a state with no pending job. -/
theorem Inv.cleared {a b : Sys St Msg} (hi : Inv a)
    (hnext : a.next ≤ b.next)
    (hlinks : b.links = []) (hsigs : b.signals = [])
    (r : Nat) (hcal : b.cfg.stateOf 0 = some (.caller none r)) : Inv b :=
  ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, hlinks, hsigs, ⟨none, r, hcal⟩,
   fun w r' h => by rw [hcal] at h; cases h⟩

/-- A worker `p ≠ 0` terminates from an intermediate system `s`. -/
theorem Inv.terminate_ne {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = []) (hsigs : s.signals = [])
    (hmon : s.monitors = a.monitors)
    (hcal : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hdowns : ∀ w rs, (0, w, rs) ∈ a.downs → (0, w, rs) ∈ s.downs)
    (hreply : ∀ v, a.cfg.mcount 0 (.reply v) ≤ s.cfg.mcount 0 (.reply v))
    (hdcnt : ∀ w rs, a.cfg.mcount 0 (.DOWN w rs) ≤ s.cfg.mcount 0 (.DOWN w rs)) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_, ?_, ?_⟩
  · simp [terminate, hlinks, unlink]
  · simp [terminate, hsigs, hlinks, linkedTo]
  · obtain ⟨w, r', h⟩ := hi.caller_alive
    exact ⟨w, r', by simp [terminate, stateOf_remove, Ne.symm hp, hcal, h]⟩
  · intro w r' hc
    simp only [terminate, stateOf_remove, Ne.symm hp, if_false, hcal] at hc
    rcases hi.pending_ok w r' hc with ⟨hal, hm⟩ | ⟨rs, hd⟩ | ⟨v, hv⟩ | ⟨rs, hd⟩
    · by_cases hwp : w = p
      · subst hwp
        right; left
        refine ⟨r, ?_⟩
        simp only [terminate]
        apply List.mem_append_right
        rw [List.mem_map]
        exact ⟨0, mem_watchers_of_mem (hmon ▸ hm), rfl⟩
      · left
        refine ⟨?_, ?_⟩
        · simp only [terminate, isSome_remove, hwp, if_false]
          exact halive w hwp hal
        · simp only [terminate]
          exact mem_unmonitor (hmon ▸ hm) (Ne.symm hp) hwp
    · right; left
      exact ⟨rs, by simp only [terminate]; exact List.mem_append_left _ (hdowns w rs hd)⟩
    · right; right; left
      refine ⟨v, ?_⟩
      simp only [terminate, mcount_remove, Ne.symm hp, if_false]
      exact Nat.lt_of_lt_of_le hv (hreply v)
    · right; right; right
      refine ⟨rs, ?_⟩
      simp only [terminate, mcount_remove, Ne.symm hp, if_false]
      exact Nat.lt_of_lt_of_le hd (hdcnt w rs)

theorem worker_ne_zero {s : Sys St Msg} (hi : Inv s) {p parent : Pid} {n : Nat} {mb : List Msg}
    (h : s.cfg.get p = some ⟨.worker parent n, mb⟩) : p ≠ 0 := by
  intro e
  subst e
  obtain ⟨w, r, hs⟩ := hi.caller_alive
  simp [stateOf, h] at hs

/-! ### Preservation -/

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  obtain ⟨w0, r0, hcal⟩ := hi.caller_alive
  have hnext := hi.next_pos
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hnext
  have hl := hi.links_nil
  have hsg := hi.signals_nil
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
        | worker parent n =>
          have hp : p ≠ 0 := worker_ne_zero hi hget
          have hst : ∀ st', (a.cfg.set p ⟨st', rest⟩).stateOf 0 = a.cfg.stateOf 0 := fun st' => by
            simp [stateOf_set, Ne.symm hp]
          have hcnt : ∀ st' x, a.cfg.mcount 0 x ≤ (a.cfg.set p ⟨st', rest⟩).mcount 0 x := fun st' x => by
            simp [mcount_set, Ne.symm hp]
          have hal : ∀ st' c, (a.cfg.get c).isSome → ((a.cfg.set p ⟨st', rest⟩).get c).isSome := fun st' c h => by
            rw [isSome_set]; split <;> simp_all
          cases m with
          | compute =>
            simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
            obtain rfl := Option.some.inj hrun
            apply Inv.terminate_ne hi hp
            · exact Nat.le_refl _
            · exact hl
            · exact hsg
            · rfl
            · rw [stateOf_deliver]; exact hst _
            · intro c _ h; rw [isSome_deliver]; exact hal _ c h
            · intro _ _ h; exact h
            · intro v; rw [mcount_deliver]; have := hcnt (.worker parent n) (.reply v); omega
            · intro w rs; rw [mcount_deliver]; have := hcnt (.worker parent n) (.DOWN w rs); omega
          | crash =>
            simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
            obtain rfl := Option.some.inj hrun
            apply Inv.terminate_ne hi hp
            · exact Nat.le_refl _
            · exact hl
            · exact hsg
            · rfl
            · exact hst _
            · intro c _ h; exact hal _ c h
            · intro _ _ h; exact h
            · intro v; exact hcnt _ _
            · intro w rs; exact hcnt _ _
          | go =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) hl hsg (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun _ _ v _ => hcnt _ _) (fun _ _ _ _ => hcnt _ _)
          | reply v =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) hl hsg (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun _ _ v _ => hcnt _ _) (fun _ _ _ _ => hcnt _ _)
          | DOWN who rs =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact Inv.frame hi (Nat.le_refl _) hl hsg (hst _) (hal _) (fun _ h => h) (fun _ _ h => Or.inl h)
              (fun _ _ v _ => hcnt _ _) (fun _ _ _ _ => hcnt _ _)
        | caller w' r' =>
          have hp0 : p = 0 → w' = w0 ∧ r' = r0 := by
            intro e; subst e
            simp [stateOf, hget] at hcal
            exact ⟨hcal.1, hcal.2⟩
          -- a caller-shaped actor at `p ≠ 0` never affects the invariant
          have other_case : ∀ st', p ≠ 0 → Inv { a with cfg := a.cfg.set p ⟨st', rest⟩ } := by
            intro st' hp
            apply Inv.frame hi
            · exact Nat.le_refl _
            · exact hl
            · exact hsg
            · simp [stateOf_set, Ne.symm hp]
            · intro c h; rw [isSome_set]; split <;> simp_all
            · intro _ h; exact h
            · intro _ _ h; exact Or.inl h
            · intro _ _ v _; simp [mcount_set, Ne.symm hp]
            · intro _ _ _ _; simp [mcount_set, Ne.symm hp]
          -- the caller at 0 clears its pending job
          have clear_case : ∀ r'', p = 0 → Inv { a with cfg := a.cfg.set p ⟨.caller none r'', rest⟩ } := by
            intro r'' hp; subst hp
            exact Inv.cleared hi (Nat.le_refl _) hl hsg r'' (by simp [stateOf_set])
          cases w' with
          | none =>
            cases m with
            | go =>
              simp only [beh, applyEffects, List.foldl, applyEffect, Config.get_set_self,
                Option.isSome_some, if_true] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · subst hp
                refine ⟨Nat.succ_pos _, hl, hsg, ⟨some a.next, r', by simp [stateOf_set, Ne.symm hn0]⟩, ?_⟩
                intro w r hc
                simp [stateOf_set, Ne.symm hn0] at hc
                obtain ⟨rfl, rfl⟩ := hc
                exact Or.inl ⟨by simp [isSome_set], by simp⟩
              · apply Inv.frame hi
                · simp
                · exact hl
                · exact hsg
                · simp [stateOf_set, Ne.symm hp, Ne.symm hn0]
                · intro c h; rw [isSome_set]; split
                  · rfl
                  · rw [isSome_set]; split <;> simp_all
                · intro w h; exact List.mem_cons_of_mem _ h
                · intro _ _ h; exact Or.inl h
                · intro _ _ v _; simp [mcount_set, Ne.symm hp, Ne.symm hn0]
                · intro _ _ _ _; simp [mcount_set, Ne.symm hp, Ne.symm hn0]
            | reply v =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · exact clear_case _ hp
              · exact other_case _ hp
            | compute =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · exact clear_case _ hp
              · exact other_case _ hp
            | crash =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · exact clear_case _ hp
              · exact other_case _ hp
            | DOWN who rs =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · exact clear_case _ hp
              · exact other_case _ hp
          | some w'' =>
            -- no-op at the real caller: the popped message is neither a reply nor DOWN w''
            have noop_case : ∀ (hm : ∀ v, m ≠ .reply v) (hd : ∀ rs, m ≠ .DOWN w'' rs),
                Inv { a with cfg := a.cfg.set p ⟨.caller (some w'') r', rest⟩ } := by
              intro hm hd
              by_cases hp : p = 0
              · subst hp
                obtain ⟨rfl, rfl⟩ := hp0 rfl
                apply Inv.frame hi
                · exact Nat.le_refl _
                · exact hl
                · exact hsg
                · simp [stateOf_set, hcal]
                · intro c h; rw [isSome_set]; split <;> simp_all
                · intro _ h; exact h
                · intro _ _ h; exact Or.inl h
                · intro w r v hc
                  rw [hcal] at hc; simp at hc; obtain ⟨rfl, rfl⟩ := hc
                  rw [mcount_set]; simp only [if_true]; rw [hpop]; simp [hm v]
                · intro w r rs hc
                  rw [hcal] at hc; simp at hc; obtain ⟨rfl, rfl⟩ := hc
                  rw [mcount_set]; simp only [if_true]; rw [hpop]; simp [hd rs]
              · exact other_case _ hp
            cases m with
            | reply v =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              by_cases hp : p = 0
              · exact clear_case _ hp
              · exact other_case _ hp
            | DOWN who rs =>
              by_cases hw : who = w''
              · subst hw
                simp only [beh, if_true, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                by_cases hp : p = 0
                · exact clear_case _ hp
                · exact other_case _ hp
              · simp only [beh, hw, if_false, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                exact noop_case (fun v h => by cases h) (fun rs' h => by cases h; exact hw rfl)
            | go =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (fun v h => by cases h) (fun rs h => by cases h)
            | compute =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (fun v h => by cases h) (fun rs h => by cases h)
            | crash =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact noop_case (fun v h => by cases h) (fun rs h => by cases h)
  | signal _ hsig =>
    -- no links, hence no signals
    unfold signalE at hsig
    rw [hsg] at hsig
    cases hsig
  | timer i _ htimer =>
    unfold timerE at htimer
    cases ht : a.timers[i]? with
    | none => simp [ht] at htimer
    | some tm =>
      obtain ⟨to, m⟩ := tm
      simp only [ht] at htimer
      obtain rfl := Option.some.inj htimer
      apply Inv.frame hi
      · exact Nat.le_refl _
      · exact hl
      · exact hsg
      · exact stateOf_deliver _ _ _ _
      · intro c h; rw [isSome_deliver]; exact h
      · intro _ h; exact h
      · intro _ _ h; exact Or.inl h
      · intro _ _ _ _; rw [mcount_deliver]; omega
      · intro _ _ _ _; rw [mcount_deliver]; omega
  | down _ hdown =>
    unfold downE at hdown
    cases hd : a.downs with
    | nil => simp [hd] at hdown
    | cons head rest =>
      obtain ⟨wt, t, rs⟩ := head
      simp only [hd] at hdown
      have hcodec : sig.downMsg = some fun p r => .DOWN p r := rfl
      simp only [hcodec] at hdown
      have hrest : ∀ w rs', (0, w, rs') ∈ a.downs → (0, w, rs') = (wt, t, rs) ∨ (0, w, rs') ∈ rest := by
        intro w rs' h; rw [hd] at h; exact List.mem_cons.mp h
      cases hw : a.cfg.get wt with
      | none =>
        simp only [hw] at hdown
        obtain rfl := Option.some.inj hdown
        have hw0 : wt ≠ 0 := by intro e; subst e; simp [stateOf, hw] at hcal
        apply Inv.frame hi
        · exact Nat.le_refl _
        · exact hl
        · exact hsg
        · rfl
        · intro _ h; exact h
        · intro _ h; exact h
        · intro w rs' h
          rcases hrest w rs' h with h | h
          · cases h; exact absurd rfl hw0
          · exact Or.inl h
        · intro _ _ _ _; exact Nat.le_refl _
        · intro _ _ _ _; exact Nat.le_refl _
      | some act =>
        simp only [hw] at hdown
        obtain rfl := Option.some.inj hdown
        apply Inv.frame hi
        · exact Nat.le_refl _
        · exact hl
        · exact hsg
        · exact stateOf_deliver _ _ _ _
        · intro c h; rw [isSome_deliver]; exact h
        · intro _ h; exact h
        · intro w rs' h
          rcases hrest w rs' h with h | h
          · cases h
            right
            rw [mcount_deliver]
            simp [hw]
          · exact Or.inl h
        · intro _ _ v _; rw [mcount_deliver]; omega
        · intro _ _ _ _; rw [mcount_deliver]; omega

/-! ### From the initial system -/

theorem init_inv : Inv init := by
  refine ⟨by decide, rfl, rfl, ⟨none, 0, by simp [init, stateOf, Config.get]⟩, ?_⟩
  intro w r h
  simp [init, stateOf, Config.get] at h

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv (fun h hi => Inv.step h hi) init_inv

/-- **A pending job is never lost.** If the caller is waiting on `w` and
`w` is dead, then `w`'s DOWN is queued, or the reply or the DOWN message is
already in the caller's mailbox. -/
theorem job_never_lost {s : Sys St Msg} (hr : SysReach beh sig init s)
    {w : Pid} {r : Nat} (hc : s.cfg.stateOf 0 = some (.caller (some w) r))
    (hdead : (s.cfg.get w).isSome = false) :
    (∃ rs, (0, w, rs) ∈ s.downs) ∨ (∃ v, 0 < s.cfg.mcount 0 (.reply v)) ∨
    (∃ rs, 0 < s.cfg.mcount 0 (.DOWN w rs)) := by
  rcases (reach_inv hr).pending_ok w r hc with ⟨hal, _⟩ | h | h | h
  · rw [hdead] at hal; cases hal
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Leanactors.Examples.Task
