import Leanactors.Examples.Lock
/-!
# Leanactors.Examples.LockProof

`Inv` is inductive: every `Step` preserves it. Combined with `Inv.mutex`
and `Reach.inv` this gives mutual exclusion under every scheduler.

The proof is a case split on (state, message) of the stepping actor. Each
case reduces, via `Step.chars`, to linear arithmetic over the six
per-pid counters, discharged by `omega`.
-/

-- The proofs below pass lemma sets that are needed in some branches and not others.
set_option linter.unusedSimpArgs false

namespace Leanactors.Examples.Lock

open Leanactors Config

/-! ### Small facts about the counters -/

theorem phaseOf_cli {c : Config St Msg} {x : Pid} {ph : Phase}
    (h : phaseOf c x = some ph) : c.stateOf x = some (.cli ph) := by
  cases hs : c.stateOf x with
  | none => simp [phaseOf, hs] at h
  | some s =>
    cases s with
    | srv _ _ => simp [phaseOf, hs] at h
    | cli ph' =>
      simp only [phaseOf, hs, Option.some.injEq] at h
      subst h
      rfl

theorem w_eq_one {c : Config St Msg} {x : Pid} (h : w c x = 1) :
    c.stateOf x = some (.cli .waiting) := by
  unfold w at h
  split at h
  · exact phaseOf_cli ‹_›
  · omega

theorem hd_eq_one {c : Config St Msg} {x : Pid} (h : hd c x = 1) :
    c.stateOf x = some (.cli .holding) := by
  unfold hd at h
  split at h
  · exact phaseOf_cli ‹_›
  · omega

theorem w_le (c : Config St Msg) (x : Pid) : w c x ≤ 1 := by
  unfold w; split <;> omega

theorem hd_le (c : Config St Msg) (x : Pid) : hd c x ≤ 1 := by
  unfold hd; split <;> omega

theorem ne_server_of_cli {c : Config St Msg} (hi : Inv c) {x : Pid} {ph : Phase}
    (h : c.stateOf x = some (.cli ph)) : x ≠ server := by
  intro e
  subst e
  obtain ⟨h0, q0, hs⟩ := hi.srv
  rw [hs] at h
  cases h

/-- Phase counters from a known client state. -/
theorem w_hd_of_state {c : Config St Msg} {x : Pid} {ph : Phase}
    (h : c.stateOf x = some (.cli ph)) :
    w c x = (if ph = .waiting then 1 else 0) ∧ hd c x = (if ph = .holding then 1 else 0) := by
  simp [w, hd, phaseOf, h]

theorem w_hd_of_srv {c : Config St Msg} {x : Pid} {h0 : Option Pid} {q0 : List Pid}
    (h : c.stateOf x = some (.srv h0 q0)) : w c x = 0 ∧ hd c x = 0 := by
  simp [w, hd, phaseOf, h]

/-- A server step always yields a server state. -/
theorem beh_srv (p : Pid) (h1 : Option Pid) (q1 : List Pid) (m : Msg) :
    ∃ h' q', (beh p (.srv h1 q1) m).1 = .srv h' q' := by
  cases m with
  | acquire x =>
    cases h1 with
    | none => exact ⟨_, _, rfl⟩
    | some h => exact ⟨_, _, rfl⟩
  | release x =>
    cases h1 with
    | none => exact ⟨_, _, rfl⟩
    | some h =>
      simp only [beh]
      split
      · cases q1 with
        | nil => exact ⟨_, _, rfl⟩
        | cons n r => exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
  | grant => cases h1 <;> exact ⟨_, _, rfl⟩
  | tick => cases h1 <;> exact ⟨_, _, rfl⟩

/-! ### Frame: a step that changes nothing the invariant looks at -/

theorem Inv.frame {c c' : Config St Msg} (hi : Inv c)
    (hsrv : c'.stateOf server = c.stateOf server)
    (honly : ∀ y h q, c'.stateOf y = some (.srv h q) → y = server)
    (hph : ∀ y, phaseOf c' y = phaseOf c y)
    (hg : ∀ y, g c' y = g c y) (ha : ∀ y, a c' y = a c y) (hr : ∀ y, r c' y = r c y) :
    Inv c' := by
  have hw : ∀ y, w c' y = w c y := fun y => by simp [w, hph]
  have hhd : ∀ y, hd c' y = hd c y := fun y => by simp [hd, hph]
  refine ⟨?_, honly, ?_, ?_⟩
  · obtain ⟨h, q, hs⟩ := hi.srv
    exact ⟨h, q, by rw [hsrv]; exact hs⟩
  · intro h q hs y hne
    rw [hsrv] at hs
    rw [hg, hhd, hr, ha, hw]
    exact hi.nonholder h q hs y hne
  · intro h q hs
    rw [hsrv] at hs
    rw [hg, hhd, hr, ha, hw]
    exact hi.holder h q hs

/-! ### The main preservation theorem -/

set_option hygiene false in
/-- A client step whose message is ignored, or a tick that only moves the
client between phases without sends: everything the invariant sees is
unchanged. Expects the client-case context of `Inv.step`. -/
macro "client_frame" : tactic => `(tactic| (
  apply Inv.frame hi hsrv' honly'
  · intro z
    by_cases hz : z = me
    · subst hz; simp [phaseOf, hstate, beh, hsp]
    · exact hph_ne z hz
  · intro z
    have := hg' z
    simp [beh] at this
    by_cases hz : z = me
    · subst hz; simp at hg_pop; rw [this, hg_pop]; simp
    · rw [this]; simp [hz]
  · intro z; have := ha' z; simp [beh] at this; exact this
  · intro z; have := hr' z; simp [beh] at this; exact this))

set_option hygiene false in
/-- A client in the wrong phase pops a `grant`: contradicts the invariant. -/
macro "client_grant_absurd" : tactic => `(tactic| (
  exfalso
  simp at hg_pop
  by_cases hh : h0 = some me
  · subst hh
    have old := hi.holder me q0 hsrv
    simp [hw_me, hhd_me] at old
    omega
  · have old := hi.nonholder h0 q0 hsrv me hh
    omega))

set_option maxHeartbeats 1000000 in
theorem Inv.step {c c' : Config St Msg} (h : Step beh c c') (hi : Inv c) : Inv c' := by
  obtain ⟨me, s, m, rest, hget, hstate, hcount⟩ := h.chars
  obtain ⟨h0, q0, hsrv⟩ := hi.srv
  have hsrv_some : (c.get server).isSome = true := isSome_of_stateOf hsrv
  have hsp : c.stateOf me = some s := by simp [stateOf, hget]
  have hpop := mcount_of_get hget
  have hst_ne : ∀ y, y ≠ me → c'.stateOf y = c.stateOf y := fun y hy => by rw [hstate]; simp [hy]
  have hph_ne : ∀ y, y ≠ me → phaseOf c' y = phaseOf c y := fun y hy => by
    simp [phaseOf, hst_ne y hy]
  cases s with
  | cli ph =>
    -- ===================== a client steps =====================
    have hps : me ≠ server := ne_server_of_cli hi hsp
    have hsrv' : c'.stateOf server = c.stateOf server := hst_ne server (Ne.symm hps)
    have hg_pop : g c me = rest.count .grant + (if m = .grant then 1 else 0) := hpop .grant
    have ha' : ∀ y, a c' y = a c y + (beh me (.cli ph) m).2.count (server, .acquire y) := fun y => by
      simp only [a, hcount, Ne.symm hps, if_false, hsrv_some, if_true]
    have hr' : ∀ y, r c' y = r c y + (beh me (.cli ph) m).2.count (server, .release y) := fun y => by
      simp only [r, hcount, Ne.symm hps, if_false, hsrv_some, if_true]
    have hg' : ∀ y, g c' y = (if y = me then rest.count .grant else g c y)
        + if (c.get y).isSome then (beh me (.cli ph) m).2.count (y, .grant) else 0 := fun y => by
      simp only [g, hcount]
    have honly' : ∀ y h q, c'.stateOf y = some (.srv h q) → y = server := by
      intro y h q hy
      by_cases hy' : y = me
      · subst hy'
        rw [hstate] at hy
        simp only [if_true] at hy
        cases ph <;> cases m <;> simp [beh] at hy
      · rw [hst_ne y hy'] at hy
        exact hi.only_srv y h q hy
    obtain ⟨hw_me, hhd_me⟩ := w_hd_of_state hsp
    have hph' : ∀ y, y ≠ me → w c' y = w c y ∧ hd c' y = hd c y := fun y hy => by
      simp [w, hd, hph_ne y hy]
    cases ph with
    | idle =>
      cases m with
      | tick =>
        -- idle --tick--> waiting, sends (acquire me) to server
        simp only [beh] at hstate ha' hr' hg'
        have hw_me' : w c' me = 1 ∧ hd c' me = 0 := by simp [w, hd, phaseOf, hstate]
        simp at hg_pop
        refine ⟨⟨h0, q0, by rw [hsrv']; exact hsrv⟩, honly', ?_, ?_⟩
        · intro h q hs y hne
          rw [hsrv'] at hs
          have old := hi.nonholder h q hs y hne
          have ha := ha' y; have hr := hr' y; have hg := hg' y
          by_cases hy : y = me
          · subst hy
            simp [List.count_cons] at ha hr hg
            simp [hw_me, hhd_me] at old
            have := hw_me'.1; have := hw_me'.2
            omega
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' y hy
            rw [hw, hhd, hg, hr, ha]
            exact old
        · intro h q hs
          rw [hsrv'] at hs
          have old := hi.holder h q hs
          have ha := ha' h; have hr := hr' h; have hg := hg' h
          by_cases hy : h = me
          · subst hy
            simp [List.count_cons] at ha hr hg
            simp [hw_me, hhd_me] at old
            have := hw_me'.1; have := hw_me'.2
            omega
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' h hy
            rw [hw, hhd, hg, hr, ha]
            exact old
      | grant => client_grant_absurd
      | acquire y => client_frame
      | release y => client_frame
    | waiting =>
      cases m with
      | grant =>
        -- waiting --grant--> holding
        simp only [beh] at hstate ha' hr' hg'
        have hw_me' : w c' me = 0 ∧ hd c' me = 1 := by simp [w, hd, phaseOf, hstate]
        simp at hg_pop
        refine ⟨⟨h0, q0, by rw [hsrv']; exact hsrv⟩, honly', ?_, ?_⟩
        · intro h q hs y hne
          rw [hsrv'] at hs
          have old := hi.nonholder h q hs y hne
          have ha := ha' y; have hr := hr' y; have hg := hg' y
          by_cases hy : y = me
          · subst hy
            -- a non-holder with a grant in its mailbox: contradiction
            exfalso; omega
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' y hy
            rw [hw, hhd, hg, hr, ha]
            exact old
        · intro h q hs
          rw [hsrv'] at hs
          have old := hi.holder h q hs
          have ha := ha' h; have hr := hr' h; have hg := hg' h
          by_cases hy : h = me
          · subst hy
            simp [List.count_cons] at ha hr hg
            simp [hw_me, hhd_me] at old
            have := hw_me'.1; have := hw_me'.2
            omega
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' h hy
            rw [hw, hhd, hg, hr, ha]
            exact old
      | tick => client_frame
      | acquire y => client_frame
      | release y => client_frame
    | holding =>
      cases m with
      | tick =>
        -- holding --tick--> idle, sends (release me) to server
        simp only [beh] at hstate ha' hr' hg'
        have hw_me' : w c' me = 0 ∧ hd c' me = 0 := by simp [w, hd, phaseOf, hstate]
        simp at hg_pop
        refine ⟨⟨h0, q0, by rw [hsrv']; exact hsrv⟩, honly', ?_, ?_⟩
        · intro h q hs y hne
          rw [hsrv'] at hs
          have old := hi.nonholder h q hs y hne
          have ha := ha' y; have hr := hr' y; have hg := hg' y
          by_cases hy : y = me
          · subst hy
            -- holding but not the holder: contradiction
            exfalso
            simp [hw_me, hhd_me] at old
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' y hy
            rw [hw, hhd, hg, hr, ha]
            exact old
        · intro h q hs
          rw [hsrv'] at hs
          have old := hi.holder h q hs
          have ha := ha' h; have hr := hr' h; have hg := hg' h
          by_cases hy : h = me
          · subst hy
            simp [List.count_cons] at ha hr hg
            simp [hw_me, hhd_me] at old
            have := hw_me'.1; have := hw_me'.2
            omega
          · simp [List.count_cons, hy, Ne.symm hy] at ha hr hg
            obtain ⟨hw, hhd⟩ := hph' h hy
            rw [hw, hhd, hg, hr, ha]
            exact old
      | grant => client_grant_absurd
      | acquire y => client_frame
      | release y => client_frame
  | srv h1 q1 =>
    -- ===================== the server steps =====================
    have hp : me = server := hi.only_srv me h1 q1 hsp
    subst hp
    clear hsrv h0 q0
    have hsrv_some' : (c.get server).isSome = true := isSome_of_stateOf hsp
    -- popped-message accounting at the server
    have ha_pop : ∀ y, a c y = rest.count (.acquire y) + (if m = .acquire y then 1 else 0) :=
      fun y => hpop _
    have hr_pop : ∀ y, r c y = rest.count (.release y) + (if m = .release y then 1 else 0) :=
      fun y => hpop _
    have hg_pop : g c server = rest.count .grant + (if m = .grant then 1 else 0) := hpop _
    -- new counters
    have ha' : ∀ y, a c' y = rest.count (.acquire y) + (beh server (.srv h1 q1) m).2.count (server, .acquire y) :=
      fun y => by simp only [a, hcount, if_true, hsrv_some']
    have hr' : ∀ y, r c' y = rest.count (.release y) + (beh server (.srv h1 q1) m).2.count (server, .release y) :=
      fun y => by simp only [r, hcount, if_true, hsrv_some']
    have hg' : ∀ y, g c' y = (if y = server then rest.count .grant else g c y)
        + if (c.get y).isSome then (beh server (.srv h1 q1) m).2.count (y, .grant) else 0 := fun y => by
      simp only [g, hcount]
    -- phases never change on a server step
    have hph' : ∀ y, phaseOf c' y = phaseOf c y := by
      intro y
      by_cases hy : y = server
      · subst hy
        obtain ⟨h', q', e⟩ := beh_srv server h1 q1 m
        simp only [phaseOf, hstate, if_true, hsp, e]
      · exact hph_ne y hy
    have hw : ∀ y, w c' y = w c y := fun y => by simp [w, hph']
    have hhd : ∀ y, hd c' y = hd c y := fun y => by simp [hd, hph']
    have honly' : ∀ y h q, c'.stateOf y = some (.srv h q) → y = server := by
      intro y h q hy
      by_cases hy' : y = server
      · exact hy'
      · rw [hst_ne y hy'] at hy
        exact hi.only_srv y h q hy
    obtain ⟨hw_p, hhd_p⟩ := w_hd_of_srv hsp
    cases m with
    | tick =>
      apply Inv.frame hi (by rw [hstate, hsp]; simp [beh]) honly' hph'
      · intro z; have := hg' z; simp [beh] at this
        by_cases hz : z = server
        · subst hz; simp at hg_pop; rw [this, hg_pop]; simp
        · rw [this]; simp [hz]
      · intro z; have := ha' z; simp [beh] at this; rw [this, ha_pop]; simp
      · intro z; have := hr' z; simp [beh] at this; rw [this, hr_pop]; simp
    | grant =>
      -- a grant to the server: contradiction, the server never holds a grant
      exfalso
      simp at hg_pop
      by_cases hh : h1 = some server
      · subst hh
        have old := hi.holder server q1 hsp
        by_cases hg1 : g c server = 1
        · have := (old.2.1 hg1).1; omega
        · omega
      · have old := hi.nonholder h1 q1 hsp server hh
        omega
    | acquire x =>
      cases h1 with
      | none =>
        -- free lock: grant to x
        simp only [beh] at hstate ha' hr' hg'
        have hsrv' : c'.stateOf server = some (.srv (some x) q1) := by rw [hstate]; simp
        have old_x := hi.nonholder none q1 hsp x (by simp)
        have hax := ha_pop x
        simp at hax
        -- x is waiting, hence a live client distinct from the server
        have hwx : w c x = 1 := by have := w_le c x; omega
        have hx_state := w_eq_one hwx
        have hx_some : (c.get x).isSome = true := isSome_of_stateOf hx_state
        have hxp : x ≠ server := ne_server_of_cli hi hx_state
        refine ⟨⟨some x, q1, hsrv'⟩, honly', ?_, ?_⟩
        · intro h q hs y hne
          rw [hsrv'] at hs
          simp at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hyx : y ≠ x := fun e => hne (by rw [e])
          have old := hi.nonholder none q1 hsp y (by simp)
          have ha := ha' y; have hr := hr' y; have hg := hg' y
          have hay := ha_pop y; have hry := hr_pop y
          simp [List.count_cons, List.count_nil, hyx, Ne.symm hyx] at ha hr hg hay hry
          rw [hw, hhd]
          by_cases hy : y = server
          · subst hy
            simp at hg hg_pop
            omega
          · simp [hy] at hg
            omega
        · intro h q hs
          rw [hsrv'] at hs
          simp at hs
          obtain ⟨rfl, rfl⟩ := hs
          have ha := ha' x; have hr := hr' x; have hg := hg' x
          have hrx := hr_pop x
          simp [List.count_cons, List.count_nil, hxp, hx_some] at ha hr hg hrx
          rw [hw, hhd]
          omega
      | some hh =>
        -- lock held: enqueue x
        simp only [beh] at hstate ha' hr' hg'
        have hsrv' : c'.stateOf server = some (.srv (some hh) (q1 ++ [x])) := by rw [hstate]; simp
        refine ⟨⟨some hh, q1 ++ [x], hsrv'⟩, honly', ?_, ?_⟩
        · intro h q hs y hne
          rw [hsrv'] at hs
          simp at hs
          obtain ⟨rfl, rfl⟩ := hs
          have old := hi.nonholder (some hh) q1 hsp y hne
          have ha := ha' y; have hr := hr' y; have hg := hg' y
          have hay := ha_pop y; have hry := hr_pop y
          simp [List.count_cons, List.count_append] at ha hr hg hay hry
          rw [hw, hhd]
          by_cases hy : y = server
          · subst hy
            simp at hg hg_pop
            by_cases hyx : x = server <;> simp [hyx] at hay ⊢ <;> omega
          · simp [hy] at hg
            by_cases hyx : x = y <;> simp [hyx] at hay ⊢ <;> omega
        · intro h q hs
          rw [hsrv'] at hs
          simp at hs
          obtain ⟨rfl, rfl⟩ := hs
          have old := hi.holder hh q1 hsp
          have ha := ha' hh; have hr := hr' hh; have hg := hg' hh
          have hay := ha_pop hh; have hry := hr_pop hh
          simp [List.count_cons, List.count_append] at ha hr hg hay hry
          rw [hw, hhd]
          by_cases hy : hh = server
          · subst hy
            simp at hg hg_pop
            by_cases hyx : x = server <;> simp [hyx] at hay ⊢ <;> omega
          · simp [hy] at hg
            by_cases hyx : x = hh <;> simp [hyx] at hay ⊢ <;> omega
    | release x =>
      cases h1 with
      | none =>
        exfalso
        have old := hi.nonholder none q1 hsp x (by simp)
        have hrx := hr_pop x
        simp at hrx
        omega
      | some hh =>
        by_cases hx : x = hh
        · subst hx
          cases q1 with
          | nil =>
            -- release with empty queue: lock becomes free
            simp only [beh, if_true, eq_self_iff_true] at hstate ha' hr' hg'
            have hsrv' : c'.stateOf server = some (.srv none []) := by rw [hstate]; simp
            have old_x := hi.holder x [] hsp
            have hrx := hr_pop x
            simp at hrx
            refine ⟨⟨none, [], hsrv'⟩, honly', ?_, ?_⟩
            · intro h q hs y _
              rw [hsrv'] at hs
              simp at hs
              obtain ⟨rfl, rfl⟩ := hs
              have ha := ha' y; have hr := hr' y; have hg := hg' y
              have hay := ha_pop y; have hry := hr_pop y
              simp [List.count_cons, List.count_nil] at ha hr hg hay hry
              rw [hw, hhd]
              simp only [List.count_nil]
              by_cases hyx : y = x
              · subst hyx
                simp at old_x
                by_cases hy : y = server
                · subst hy; simp at hg hg_pop; omega
                · simp [hy] at hg; omega
              · have old := hi.nonholder (some x) [] hsp y (by simp [Ne.symm hyx])
                simp at old
                simp [Ne.symm hyx] at hry
                by_cases hy : y = server
                · subst hy; simp at hg hg_pop; omega
                · simp [hy] at hg; omega
            · intro h q hs
              rw [hsrv'] at hs
              simp at hs
          | cons n rest' =>
            -- release with waiting queue: grant to n
            simp only [beh, if_true, eq_self_iff_true] at hstate ha' hr' hg'
            have hsrv' : c'.stateOf server = some (.srv (some n) rest') := by rw [hstate]; simp
            have old_x := hi.holder x (n :: rest') hsp
            have hrx := hr_pop x
            simp at hrx
            -- n is waiting: it is a live client distinct from the server
            have hwn : w c n = 1 := by
              by_cases hnx : n = x
              · subst hnx
                simp [List.count_cons, List.count_nil] at old_x
                have := w_le c n
                omega
              · have old := hi.nonholder (some x) (n :: rest') hsp n (by simp [Ne.symm hnx])
                simp [List.count_cons, List.count_nil] at old
                have := w_le c n
                omega
            have hn_state := w_eq_one hwn
            have hn_some : (c.get n).isSome = true := isSome_of_stateOf hn_state
            have hnp : n ≠ server := ne_server_of_cli hi hn_state
            refine ⟨⟨some n, rest', hsrv'⟩, honly', ?_, ?_⟩
            · intro h q hs y hne
              rw [hsrv'] at hs
              simp at hs
              obtain ⟨rfl, rfl⟩ := hs
              have hyn : y ≠ n := fun e => hne (by rw [e])
              have ha := ha' y; have hr := hr' y; have hg := hg' y
              have hay := ha_pop y; have hry := hr_pop y
              simp [List.count_cons, List.count_nil, hyn, Ne.symm hyn] at ha hr hg hay hry
              rw [hw, hhd]
              by_cases hyx : y = x
              · subst hyx
                simp [List.count_cons, List.count_nil, hyn, Ne.symm hyn] at old_x
                by_cases hy : y = server
                · subst hy; simp at hg hg_pop; omega
                · simp [hy] at hg; omega
              · have old := hi.nonholder (some x) (n :: rest') hsp y (by simp [Ne.symm hyx])
                simp [List.count_cons, List.count_nil, hyn, Ne.symm hyn] at old
                simp [Ne.symm hyx] at hry
                by_cases hy : y = server
                · subst hy; simp at hg hg_pop; omega
                · simp [hy] at hg; omega
            · intro h q hs
              rw [hsrv'] at hs
              simp at hs
              obtain ⟨rfl, rfl⟩ := hs
              have ha := ha' n; have hr := hr' n; have hg := hg' n
              have han := ha_pop n; have hrn := hr_pop n
              simp [List.count_cons, List.count_nil, hnp, hn_some] at ha hr hg han hrn
              rw [hw, hhd]
              by_cases hnx : n = x
              · subst hnx
                simp [List.count_cons, List.count_nil] at old_x
                omega
              · have old := hi.nonholder (some x) (n :: rest') hsp n (by simp [Ne.symm hnx])
                simp [List.count_cons, List.count_nil] at old
                simp [Ne.symm hnx] at hrn
                omega
        · -- release from a non-holder: contradiction
          exfalso
          have old := hi.nonholder (some hh) q1 hsp x (by simp [Ne.symm hx])
          have hrx := hr_pop x
          simp at hrx
          omega


/-! ### Environment ticks preserve the invariant -/

theorem Inv.env {c c' : Config St Msg} (h : EnvStep c c') (hi : Inv c) : Inv c' := by
  cases h with
  | tick p =>
    have hst : ∀ y, (c.deliver p .tick).stateOf y = c.stateOf y := fun y => stateOf_deliver c p y _
    have hcnt : ∀ y m, m ≠ Msg.tick → (c.deliver p .tick).mcount y m = c.mcount y m := by
      intro y m hm
      rw [mcount_deliver]
      simp [Ne.symm hm]
    apply Inv.frame hi (hst server)
    · intro y h q hy; rw [hst] at hy; exact hi.only_srv y h q hy
    · intro y; simp [phaseOf, hst]
    · intro y; exact hcnt y .grant (by simp)
    · intro y; exact hcnt server (.acquire y) (by simp)
    · intro y; exact hcnt server (.release y) (by simp)

/-! ### The initial configuration satisfies the invariant -/

theorem initCfg_stateOf (n p : Pid) :
    (initCfg n).stateOf p =
      if p = server then some (.srv none []) else if p ≤ n then some (.cli .idle) else none := by
  unfold stateOf Config.get initCfg
  by_cases h0 : p = server
  · simp [h0]
  · by_cases hn : p ≤ n <;> simp [h0, hn]

theorem initCfg_mcount (n p : Pid) (m : Msg) : (initCfg n).mcount p m = 0 := by
  unfold mcount Config.get initCfg
  by_cases h0 : p = server
  · simp [h0]
  · by_cases hn : p ≤ n <;> simp [h0, hn]

theorem initCfg_inv (n : Nat) : Inv (initCfg n) := by
  have hs : (initCfg n).stateOf server = some (.srv none []) := by simp [initCfg_stateOf]
  have hw : ∀ p, w (initCfg n) p = 0 := by
    intro p; unfold w phaseOf; rw [initCfg_stateOf]
    by_cases h0 : p = server
    · simp [h0]
    · by_cases hn : p ≤ n <;> simp [h0, hn]
  have hhd : ∀ p, hd (initCfg n) p = 0 := by
    intro p; unfold hd phaseOf; rw [initCfg_stateOf]
    by_cases h0 : p = server
    · simp [h0]
    · by_cases hn : p ≤ n <;> simp [h0, hn]
  refine ⟨⟨none, [], hs⟩, ?_, ?_, ?_⟩
  · intro p h q hpq
    rw [initCfg_stateOf] at hpq
    by_cases h0 : p = server
    · exact h0
    · by_cases hn : p ≤ n <;> simp [h0, hn] at hpq
  · intro h q hsq p _
    rw [hs] at hsq
    simp at hsq
    obtain ⟨rfl, rfl⟩ := hsq
    simp [g, a, r, initCfg_mcount, hhd, hw]
  · intro h q hsq
    rw [hs] at hsq
    simp at hsq

/-! ### End-to-end: mutual exclusion under every scheduler and environment -/

theorem ReachEnv.inv {c c' : Config St Msg} (h : ReachEnv c c') (hi : Inv c) : Inv c' := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (Inv.step hs hi)
  | env he _ ih => exact ih (Inv.env he hi)

/-- **Main theorem.** Starting from a server and `n` idle clients, under
any interleaving of actor steps and environment ticks, no two clients are
ever `holding` at the same time. -/
theorem mutex_forever (n : Nat) {c : Config St Msg} (hr : ReachEnv (initCfg n) c) :
    ∀ p q, c.stateOf p = some (.cli .holding) → c.stateOf q = some (.cli .holding) → p = q := by
  intro p q hp hq
  have hi := hr.inv (initCfg_inv n)
  have hp' := (w_hd_of_state hp).2
  have hq' := (w_hd_of_state hq).2
  simp at hp' hq'
  exact hi.mutex p q hp' hq'

end Leanactors.Examples.Lock
