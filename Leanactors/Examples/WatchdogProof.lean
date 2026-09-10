import Leanactors.Examples.Watchdog
/-!
# Leanactors.Examples.WatchdogProof

`Inv` is preserved by every `SysStep`. The frame lemma here lets the
watchdog's boolean flag change as long as its child does not, which covers
the `:timeout` step; everything else is the supervisor recipe.
-/

set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Watchdog

open Leanactors Config Sys

/-! ### The two shapes -/

theorem Inv.frame {a b : Sys St Msg} (hi : Inv a)
    (hnext : a.next ≤ b.next)
    (hdog : ∀ w bb, a.cfg.stateOf 0 = some (.watchdog w bb) → ∃ bb', b.cfg.stateOf 0 = some (.watchdog w bb'))
    (halive : ∀ c, (a.cfg.get c).isSome → (b.cfg.get c).isSome)
    (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ b.links)
    (hsigs : ∀ c r, (0, c, r) ∈ a.signals → (0, c, r) ∈ b.signals ∨ 0 < b.cfg.mcount 0 (.EXIT c r))
    (hcount : ∀ c bb r, a.cfg.stateOf 0 = some (.watchdog (some c) bb) →
      a.cfg.mcount 0 (.EXIT c r) ≤ b.cfg.mcount 0 (.EXIT c r)) : Inv b := by
  obtain ⟨w0, b0, h0⟩ := hi.dog_alive
  obtain ⟨b1, h1⟩ := hdog w0 b0 h0
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ⟨w0, b1, h1⟩, ?_⟩
  intro c bb hc
  rw [h1] at hc
  simp at hc
  obtain ⟨rfl, rfl⟩ := hc
  rcases hi.child_ok c b0 h0 with ⟨hal, hl⟩ | ⟨r, hs⟩ | ⟨r, hm⟩
  · exact Or.inl ⟨halive c hal, hlinks c hl⟩
  · rcases hsigs c r hs with h | h
    · exact Or.inr (Or.inl ⟨r, h⟩)
    · exact Or.inr (Or.inr ⟨r, h⟩)
  · exact Or.inr (Or.inr ⟨r, Nat.lt_of_lt_of_le hm (hcount c b0 r h0)⟩)

theorem Inv.terminate_ne {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = a.links)
    (hdog : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.EXIT c r') ≤ s.cfg.mcount 0 (.EXIT c r')) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_⟩
  · obtain ⟨w, bb, h⟩ := hi.dog_alive
    exact ⟨w, bb, by simp [terminate, stateOf_remove, Ne.symm hp, hdog, h]⟩
  · intro c bb hc
    simp only [terminate, stateOf_remove, Ne.symm hp, if_false, hdog] at hc
    rcases hi.child_ok c bb hc with ⟨hal, hl⟩ | ⟨r', hs⟩ | ⟨r', hm⟩
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

theorem worker_ne_zero {s : Sys St Msg} (hi : Inv s) {p : Pid} {h : Bool} {n : Nat} {mb : List Msg}
    (hg : s.cfg.get p = some ⟨.worker h n, mb⟩) : p ≠ 0 := by
  intro e
  subst e
  obtain ⟨w, bb, hs⟩ := hi.dog_alive
  simp [stateOf, hg] at hs

/-! ### Preservation -/

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  obtain ⟨w0, b0, hdog⟩ := hi.dog_alive
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
        | worker hung n =>
          have hp : p ≠ 0 := worker_ne_zero hi hget
          -- any step of a worker other than dying is a frame
          have wframe : ∀ (cfg' : Config St Msg), cfg'.stateOf 0 = a.cfg.stateOf 0 →
              (∀ c, (a.cfg.get c).isSome → (cfg'.get c).isSome) →
              (∀ x, a.cfg.mcount 0 x ≤ cfg'.mcount 0 x) →
              Inv { a with cfg := cfg' } := by
            intro cfg' hs hal hc
            apply Inv.frame hi
            · exact Nat.le_refl _
            · intro w bb h; exact ⟨bb, by rw [hs]; exact h⟩
            · exact hal
            · intro _ h; exact h
            · intro _ _ h; exact Or.inl h
            · intro c _ r _; exact hc _
          have hst : ∀ st', (a.cfg.set p ⟨st', rest⟩).stateOf 0 = a.cfg.stateOf 0 := fun st' => by
            simp [stateOf_set, Ne.symm hp]
          have hcnt : ∀ st' x, a.cfg.mcount 0 x ≤ (a.cfg.set p ⟨st', rest⟩).mcount 0 x := fun st' x => by
            simp [mcount_set, Ne.symm hp]
          have hal : ∀ st' c, (a.cfg.get c).isSome → ((a.cfg.set p ⟨st', rest⟩).get c).isSome := fun st' c h => by
            rw [isSome_set]; split <;> simp_all
          cases m with
          | ping =>
            cases hung with
            | false =>
              simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
              obtain rfl := Option.some.inj hrun
              apply wframe
              · rw [stateOf_deliver]; exact hst _
              · intro c h; rw [isSome_deliver]; exact hal _ c h
              · intro x; rw [mcount_deliver]; have := hcnt (.worker false (n + 1)) x; omega
            | true =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact wframe _ (hst _) (hal _) (hcnt _)
          | hang =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact wframe _ (hst _) (hal _) (hcnt _)
          | start =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact wframe _ (hst _) (hal _) (hcnt _)
          | pong =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact wframe _ (hst _) (hal _) (hcnt _)
          | timeout =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact wframe _ (hst _) (hal _) (hcnt _)
          | EXIT who r =>
            simp only [beh, applyEffects, List.foldl] at hrun
            obtain rfl := Option.some.inj hrun
            exact wframe _ (hst _) (hal _) (hcnt _)
        | watchdog w' b' =>
          have hp0 : p = 0 → w' = w0 ∧ b' = b0 := by
            intro e; subst e
            simp [stateOf, hget] at hdog
            exact ⟨hdog.1, hdog.2⟩
          -- spawn shape: new child at `a.next`, pinged, timer armed
          have spawn_case : ∀ (rest' : List Msg),
              Inv { cfg := ((a.cfg.set p ⟨.watchdog (some a.next) true, rest'⟩).set a.next ⟨.worker false 0, []⟩).deliver a.next .ping,
                    next := a.next + 1, links := (p, a.next) :: a.links, signals := a.signals,
                    monitors := a.monitors, downs := a.downs, timers := a.timers ++ [(p, .timeout)] } := by
            intro rest'
            by_cases hp : p = 0
            · subst hp
              refine ⟨Nat.succ_pos _, ⟨some a.next, true, by simp [stateOf_deliver, stateOf_set, Ne.symm hn0]⟩, ?_⟩
              intro c bb hc
              simp [stateOf_deliver, stateOf_set, Ne.symm hn0] at hc
              obtain ⟨rfl, rfl⟩ := hc
              exact Or.inl ⟨by simp [isSome_deliver, isSome_set], by simp⟩
            · apply Inv.frame hi
              · simp
              · intro w bb h; exact ⟨bb, by simp [stateOf_deliver, stateOf_set, Ne.symm hp, Ne.symm hn0]; exact h⟩
              · intro c h; rw [isSome_deliver, isSome_set]; split
                · rfl
                · rw [isSome_set]; split <;> simp_all
              · intro c h; exact List.mem_cons_of_mem _ h
              · intro c r h; exact Or.inl h
              · intro c bb r _; rw [mcount_deliver]; simp [mcount_set, Ne.symm hp, Ne.symm hn0]
          -- flag-only change at the real watchdog, or any change elsewhere, with a
          -- popped message that is not an EXIT for the current child
          have flag_case : ∀ b'' (cfg' : Config St Msg),
              cfg' = a.cfg.set p ⟨.watchdog w' b'', rest⟩ ∨
                (∃ q m', cfg' = (a.cfg.set p ⟨.watchdog w' b'', rest⟩).deliver q m') →
              (∀ c r, w' = some c → m ≠ .EXIT c r) →
              ∀ (timers' : List (Pid × Msg)) (sigs' : List (Pid × Pid × Reason)),
                (∀ x, x ∈ a.signals → x ∈ sigs') →
                Inv { a with cfg := cfg', timers := timers', signals := sigs' } := by
            intro b'' cfg' hcfg hm timers' sigs' hs
            have hst : cfg'.stateOf 0 = (a.cfg.set p ⟨.watchdog w' b'', rest⟩).stateOf 0 := by
              rcases hcfg with rfl | ⟨q, m', rfl⟩
              · rfl
              · exact stateOf_deliver _ _ _ _
            have hal : ∀ c, ((a.cfg.set p ⟨.watchdog w' b'', rest⟩).get c).isSome → (cfg'.get c).isSome := by
              intro c h
              rcases hcfg with rfl | ⟨q, m', rfl⟩
              · exact h
              · rw [isSome_deliver]; exact h
            have hcn : ∀ x, (a.cfg.set p ⟨.watchdog w' b'', rest⟩).mcount 0 x ≤ cfg'.mcount 0 x := by
              intro x
              rcases hcfg with rfl | ⟨q, m', rfl⟩
              · exact Nat.le_refl _
              · rw [mcount_deliver]; omega
            apply Inv.frame hi
            · exact Nat.le_refl _
            · intro w bb h
              rw [hst]
              by_cases hp : p = 0
              · subst hp
                obtain ⟨rfl, rfl⟩ := hp0 rfl
                rw [hdog] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨b'', by simp [stateOf_set]⟩
              · exact ⟨bb, by simp [stateOf_set, Ne.symm hp]; exact h⟩
            · intro c h; apply hal; rw [isSome_set]; split <;> simp_all
            · intro _ h; exact h
            · intro c r h; exact Or.inl (hs _ h)
            · intro c bb r hc
              refine Nat.le_trans ?_ (hcn _)
              by_cases hp : p = 0
              · subst hp
                obtain ⟨rfl, rfl⟩ := hp0 rfl
                rw [hdog] at hc; simp at hc; obtain ⟨rfl, rfl⟩ := hc
                rw [mcount_set]; simp only [if_true]; rw [hpop]; simp [hm c r rfl]
              · simp [mcount_set, Ne.symm hp]
          cases w' with
          | none =>
            cases m with
            | start =>
              simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
              obtain rfl := Option.some.inj hrun
              exact spawn_case _
            | pong =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h) _ _ (fun _ h => h)
            | timeout =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h) _ _ (fun _ h => h)
            | ping =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h) _ _ (fun _ h => h)
            | hang =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h) _ _ (fun _ h => h)
            | EXIT who r =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h) _ _ (fun _ h => h)
          | some w'' =>
            cases m with
            | pong =>
              cases b' with
              | true =>
                simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
                obtain rfl := Option.some.inj hrun
                exact flag_case true _ (Or.inr ⟨_, _, rfl⟩) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
              | false =>
                simp only [beh, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                exact flag_case false _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
            | timeout =>
              cases b' with
              | true =>
                simp only [beh, applyEffects, List.foldl, applyEffect] at hrun
                obtain rfl := Option.some.inj hrun
                exact flag_case false _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _
                  (fun _ h => List.mem_append_left _ h)
              | false =>
                simp only [beh, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                exact flag_case false _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
            | EXIT who r =>
              by_cases hw : who = w''
              · subst hw
                simp only [beh, if_true, applyEffects, List.foldl, applyEffect] at hrun
                obtain rfl := Option.some.inj hrun
                exact spawn_case _
              · simp only [beh, hw, if_false, applyEffects, List.foldl] at hrun
                obtain rfl := Option.some.inj hrun
                exact flag_case b' _ (Or.inl rfl) (fun c r' hc h => by cases hc; cases h; exact hw rfl) _ _ (fun _ h => h)
            | start =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
            | ping =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
            | hang =>
              simp only [beh, applyEffects, List.foldl] at hrun
              obtain rfl := Option.some.inj hrun
              exact flag_case b' _ (Or.inl rfl) (fun c r h => by cases h; intro e; cases e) _ _ (fun _ h => h)
  | signal _ hsig =>
    unfold signalE at hsig
    cases hsg : a.signals with
    | nil => simp [hsg] at hsig
    | cons head rest =>
      obtain ⟨q, src, r⟩ := head
      simp only [hsg] at hsig
      have hrest : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') = (q, src, r) ∨ (0, c, r') ∈ rest := by
        intro c r' h; rw [hsg] at h; exact List.mem_cons.mp h
      cases hq : a.cfg.get q with
      | none =>
        simp only [hq] at hsig
        obtain rfl := Option.some.inj hsig
        have hq0 : q ≠ 0 := by intro e; subst e; simp [stateOf, hq] at hdog
        apply Inv.frame hi
        · exact Nat.le_refl _
        · intro w bb h; exact ⟨bb, h⟩
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
          · intro w bb h; exact ⟨bb, by rw [stateOf_deliver]; exact h⟩
          · intro c h; rw [isSome_deliver]; exact h
          · intro c h; exact h
          · intro c r' h
            rcases hrest c r' h with h | h
            · cases h
              right
              rw [mcount_deliver]
              simp [sig, hq]
            · exact Or.inl h
          · intro c bb r' _
            rw [mcount_deliver]
            omega
        · have hq0 : q ≠ 0 := by
            intro e; subst e
            simp [stateOf, hq] at hdog
            have : act.state = .watchdog w0 b0 := hdog
            simp [sig, this] at htr
          rw [if_neg htr] at hsig
          cases r with
          | normal =>
            obtain rfl := Option.some.inj hsig
            apply Inv.frame hi
            · exact Nat.le_refl _
            · intro w bb h; exact ⟨bb, h⟩
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
      · intro w bb h; exact ⟨bb, by rw [stateOf_deliver]; exact h⟩
      · intro c h; rw [isSome_deliver]; exact h
      · intro _ h; exact h
      · intro _ _ h; exact Or.inl h
      · intro _ _ _ _; rw [mcount_deliver]; omega
  | down _ hdown =>
    unfold downE at hdown
    cases hd : a.downs with
    | nil => simp [hd] at hdown
    | cons head rest =>
      obtain ⟨w, t, r⟩ := head
      simp only [hd] at hdown
      have hcodec : sig.downMsg = none := rfl
      simp only [hcodec] at hdown
      obtain rfl := Option.some.inj hdown
      apply Inv.frame hi
      · exact Nat.le_refl _
      · intro w bb h; exact ⟨bb, h⟩
      · intro _ h; exact h
      · intro _ h; exact h
      · intro _ _ h; exact Or.inl h
      · intro _ _ _ _; exact Nat.le_refl _

/-! ### From the initial system -/

theorem init_inv : Inv init := by
  refine ⟨by decide, ⟨none, false, by simp [init, stateOf, Config.get]⟩, ?_⟩
  intro c bb h
  simp [init, stateOf, Config.get] at h

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  hr.inv (fun h hi => Inv.step h hi) init_inv

/-- **The watchdog never dies.** -/
theorem watchdog_alive {s : Sys St Msg} (hr : SysReach beh sig init s) :
    ∃ w bb, s.cfg.stateOf 0 = some (.watchdog w bb) :=
  (reach_inv hr).dog_alive

/-- **A dead worker always has its restart in flight**, whether it hung and
was killed or crashed on its own. -/
theorem restart_in_flight {s : Sys St Msg} (hr : SysReach beh sig init s)
    {w : Pid} {bb : Bool} (hc : s.cfg.stateOf 0 = some (.watchdog (some w) bb))
    (hdead : (s.cfg.get w).isSome = false) :
    (∃ r, (0, w, r) ∈ s.signals) ∨ ∃ r, 0 < s.cfg.mcount 0 (.EXIT w r) := by
  rcases (reach_inv hr).child_ok w bb hc with ⟨hal, _⟩ | h | h
  · rw [hdead] at hal; cases hal
  · exact Or.inl h
  · exact Or.inr h

end Leanactors.Examples.Watchdog
