import Leanactors.SysProps
import Leanactors.Examples.Task
/-!
# Leanactors.Examples.TaskProof

`Inv` is preserved by every `SysStep`. Same two shapes as the supervisor
(`Inv.frame` for steps that only add, `Inv.terminate_ne` for a dying
worker) plus one more: the caller clearing its pending job, which makes
`pending_ok` vacuous.

With `Leanactors.SysProps` the case analysis is by pid: any actor other
than the caller survives its step (`set` then `Grows`) or dies
(`terminate_frame`), whatever it popped. The one thing `Grows` cannot say
is that `links` and `signals` stay empty, and that comes from
`beh_isolated`: no clause ever links or signals.
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

/-- `Inv.frame` along `Grows`; only `links = []` and `signals = []` are not
monotone and must be supplied. -/
theorem Inv.grows {a b : Sys St Msg} (hi : Inv a) (h : Grows a b) (hl : b.links = [])
    (hs : b.signals = []) : Inv b :=
  Inv.frame hi h.next hl hs (h.stateOf 0 hi.next_pos) h.alive (fun w => h.monitors (0, w))
    (fun _ _ hd => Or.inl (h.downs _ hd)) (fun _ _ _ _ => h.mcount 0 _ hi.next_pos)
    (fun _ _ _ _ => h.mcount 0 _ hi.next_pos)

/-- Overwriting an actor other than the caller. -/
theorem Inv.set_ne {a : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (x : Actor St Msg) :
    Inv { a with cfg := a.cfg.set p x } :=
  let f := frame_set a p x
  Inv.frame hi f.next hi.links_nil hi.signals_nil (f.stateOf 0 (Ne.symm hp) hi.next_pos)
    (fun c h => by rw [isSome_set]; split <;> simp [h]) (fun _ h => h) (fun _ _ hd => Or.inl hd)
    (fun _ _ _ _ => f.mcount 0 _ (Ne.symm hp) hi.next_pos)
    (fun _ _ _ _ => f.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-- `Inv` ignores `timers`. -/
theorem Inv.set_timers {a : Sys St Msg} (hi : Inv a) (t : List (Pid × Msg)) :
    Inv { a with timers := t } :=
  ⟨hi.next_pos, hi.links_nil, hi.signals_nil, hi.caller_alive, hi.pending_ok⟩

/-- Dropping the head DOWN when it is not addressed to the caller. -/
theorem Inv.pop_down {a : Sys St Msg} (hi : Inv a) {w t : Pid} {rs : Reason}
    {rest : List (Pid × Pid × Reason)} (hd : a.downs = (w, t, rs) :: rest) (hw : w ≠ 0) :
    Inv { a with downs := rest } :=
  ⟨hi.next_pos, hi.links_nil, hi.signals_nil, hi.caller_alive, fun w' r hc => by
    rcases hi.pending_ok w' r hc with h | ⟨rs', hd'⟩ | h | h
    · exact Or.inl h
    · rw [hd] at hd'
      rcases List.mem_cons.mp hd' with hd' | hd'
      · cases hd'; exact absurd rfl hw
      · exact Or.inr (Or.inl ⟨rs', hd'⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))⟩

/-- The caller at 0 moved to a state with no pending job. -/
theorem Inv.cleared {a b : Sys St Msg} (hi : Inv a)
    (hnext : a.next ≤ b.next)
    (hlinks : b.links = []) (hsigs : b.signals = [])
    (r : Nat) (hcal : b.cfg.stateOf 0 = some (.caller none r)) : Inv b :=
  ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, hlinks, hsigs, ⟨none, r, hcal⟩,
   fun w r' h => by rw [hcal] at h; cases h⟩

/-- A worker `p ≠ 0` terminates from an intermediate system `s` that keeps
the caller's monitors, state, mailbox and pending DOWNs. -/
theorem Inv.terminate_core {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = []) (hsigs : s.signals = [])
    (hmon : ∀ w, (0, w) ∈ a.monitors → (0, w) ∈ s.monitors)
    (hcal : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hdowns : ∀ w rs, (0, w, rs) ∈ a.downs → (0, w, rs) ∈ s.downs)
    (hreply : ∀ v, a.cfg.mcount 0 (.reply v) ≤ s.cfg.mcount 0 (.reply v))
    (hdcnt : ∀ w rs, a.cfg.mcount 0 (.DOWN w rs) ≤ s.cfg.mcount 0 (.DOWN w rs)) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, terminate_links_of_links_nil _ _ _ hlinks,
    by rw [terminate_signals_of_links_nil _ _ _ hlinks, hsigs], ?_, ?_⟩
  · obtain ⟨w, r', h⟩ := hi.caller_alive
    exact ⟨w, r', by rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hcal, h]⟩
  · intro w r' hc
    rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hcal] at hc
    rcases hi.pending_ok w r' hc with ⟨hal, hm⟩ | ⟨rs, hd⟩ | ⟨v, hv⟩ | ⟨rs, hd⟩
    · by_cases hwp : w = p
      · subst hwp
        exact Or.inr (Or.inl ⟨r, terminate_down_of_monitor _ _ _ (hmon _ hm)⟩)
      · exact Or.inl ⟨by rw [terminate_isSome_ne _ _ _ hwp]; exact halive w hwp hal,
          terminate_mem_monitors _ _ _ (hmon _ hm) (Ne.symm hp) hwp⟩
    · exact Or.inr (Or.inl ⟨rs, terminate_mem_downs _ _ _ (hdowns w rs hd)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨v, by
        rw [terminate_mcount_ne _ _ _ (Ne.symm hp)]; exact Nat.lt_of_lt_of_le hv (hreply v)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rs, by
        rw [terminate_mcount_ne _ _ _ (Ne.symm hp)]; exact Nat.lt_of_lt_of_le hd (hdcnt w rs)⟩))

theorem Inv.terminate_ne {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : s.links = []) (hsigs : s.signals = [])
    (hmon : s.monitors = a.monitors)
    (hcal : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hdowns : ∀ w rs, (0, w, rs) ∈ a.downs → (0, w, rs) ∈ s.downs)
    (hreply : ∀ v, a.cfg.mcount 0 (.reply v) ≤ s.cfg.mcount 0 (.reply v))
    (hdcnt : ∀ w rs, a.cfg.mcount 0 (.DOWN w rs) ≤ s.cfg.mcount 0 (.DOWN w rs)) :
    Inv (s.terminate p r) :=
  hi.terminate_core hp r hnext hlinks hsigs (fun _ h => hmon ▸ h) hcal halive hdowns hreply hdcnt

/-- The same from a `Frame p a s` that keeps the caller's monitors. -/
theorem Inv.terminate_frame {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hf : Frame p a s) (hlinks : s.links = []) (hsigs : s.signals = [])
    (hmon : ∀ w, (0, w) ∈ a.monitors → (0, w) ∈ s.monitors) : Inv (s.terminate p r) :=
  hi.terminate_core hp r hf.next hlinks hsigs hmon (hf.stateOf 0 (Ne.symm hp) hi.next_pos)
    hf.alive (fun _ _ => hf.downs _) (fun _ => hf.mcount 0 _ (Ne.symm hp) hi.next_pos)
    (fun _ _ => hf.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-! ### What the behaviour never does -/

/-- No clause links or signals, so `links` and `signals` stay empty. -/
theorem beh_isolated (me fresh : Pid) (st : St) (m : Msg) :
    ∀ e ∈ (beh me fresh st m).2, e.isolated = true := by
  cases st with
  | caller w r => cases w <;> cases m <;> simp [beh, Effect.isolated] <;> split <;> simp
  | worker p n => cases m <;> simp [beh, Effect.isolated]

/-- The caller never emits `exit`. -/
theorem caller_no_exit (me fresh : Pid) (w : Option Pid) (r : Nat) (m : Msg) (rs : Reason) :
    Effect.exit rs ∉ (beh me fresh (.caller w r) m).2 := by
  cases w <;> cases m <;> simp [beh] <;> split <;> simp

/-! ### The caller's own steps -/

/-- The spawn shape: `go` on an idle caller spawns and monitors a worker. -/
theorem Inv.caller_spawn {a : Sys St Msg} (hi : Inv a) (r : Nat) (rest : List Msg) :
    Inv { a with cfg := (a.cfg.set 0 ⟨.caller (some a.next) r, rest⟩).set a.next ⟨.worker 0 0, []⟩,
                 next := a.next + 1, monitors := (0, a.next) :: a.monitors } := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hi.next_pos
  refine ⟨Nat.succ_pos _, hi.links_nil, hi.signals_nil,
    ⟨some a.next, r, by simp [stateOf_set, Ne.symm hn0]⟩, ?_⟩
  intro w r' hc
  simp [stateOf_set, Ne.symm hn0] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact Or.inl ⟨by simp [isSome_set], by simp⟩

/-- The cleared shape at the caller: whatever it popped, it now has no
pending job. -/
theorem Inv.caller_clear {a : Sys St Msg} (hi : Inv a) (r : Nat) (rest : List Msg) :
    Inv { a with cfg := a.cfg.set 0 ⟨.caller none r, rest⟩ } :=
  hi.cleared (Nat.le_refl _) hi.links_nil hi.signals_nil r (by simp [stateOf_set])

/-- The no-op shape: the caller, waiting on `w`, consumes a message that is
neither a reply nor `w`'s DOWN. -/
theorem Inv.caller_noop {a : Sys St Msg} (hi : Inv a) {w : Pid} {r : Nat} {m : Msg}
    {rest : List Msg} (hget : a.cfg.get 0 = some ⟨.caller (some w) r, m :: rest⟩)
    (hm : ∀ v, m ≠ .reply v) (hd : ∀ rs, m ≠ .DOWN w rs) :
    Inv { a with cfg := a.cfg.set 0 ⟨.caller (some w) r, rest⟩ } := by
  refine ⟨hi.next_pos, hi.links_nil, hi.signals_nil, ⟨some w, r, by simp [stateOf_set]⟩, ?_⟩
  intro w' r' hc
  simp [stateOf_set] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rcases hi.pending_ok w r (by simp [stateOf, hget]) with ⟨hal, hmon⟩ | ⟨rs, hd'⟩ | ⟨v, hv⟩ | ⟨rs, hv⟩
  · exact Or.inl ⟨by rw [isSome_set]; split <;> simp [hal], hmon⟩
  · exact Or.inr (Or.inl ⟨rs, hd'⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨v, ?_⟩))
    rw [mcount_of_get hget, if_neg (hm v)] at hv
    rw [mcount_set, if_pos rfl]
    simpa using hv
  · refine Or.inr (Or.inr (Or.inr ⟨rs, ?_⟩))
    rw [mcount_of_get hget, if_neg (hd rs)] at hv
    rw [mcount_set, if_pos rfl]
    simpa using hv

/-! ### Preservation, one lemma per kind of step -/

/-- Any actor other than the caller, popping any message: it survives
(`set` then `Grows`) or dies (`terminate_frame`); `links` and `signals`
stay empty because no effect ever links. -/
theorem Inv.run_ne {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a)
    (hp : p ≠ 0) : Inv b := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  have hg := applyEffects_grows p { a with cfg := a.cfg.set p ⟨(beh p a.next st m).1, rest⟩ }
    (beh p a.next st m).2
  obtain ⟨hl, hs⟩ := applyEffects_links_signals_of_isolated p
    { a with cfg := a.cfg.set p ⟨(beh p a.next st m).1, rest⟩ } (beh_isolated p a.next st m)
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact (hi.set_ne hp _).grows hg (hl.trans hi.links_nil) (hs.trans hi.signals_nil)
  · exact (hi.set_ne hp _).terminate_frame hp reason (hg.frame p) (hl.trans hi.links_nil)
      (hs.trans hi.signals_nil) (fun w => hg.monitors (0, w))

theorem Inv.run {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a) : Inv b := by
  by_cases hp : p = 0
  · subst hp
    obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
    obtain ⟨w, r, hcal⟩ := hi.caller_alive
    simp [stateOf, hget] at hcal
    subst hcal
    simp only at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · cases w with
      | none =>
        cases m with
        | go =>
          simp only [beh, applyEffects, List.foldl, applyEffect, get_set_self, Option.isSome_some,
            if_true]
          exact hi.caller_spawn _ _
        | _ =>
          simp only [beh, applyEffects, List.foldl]
          exact hi.caller_clear _ _
      | some w =>
        cases m with
        | reply v =>
          simp only [beh, applyEffects, List.foldl]
          exact hi.caller_clear _ _
        | DOWN who rs =>
          by_cases hw : who = w
          · subst hw
            simp only [beh, if_true, applyEffects, List.foldl]
            exact hi.caller_clear _ _
          · simp only [beh, hw, if_false, applyEffects, List.foldl]
            exact hi.caller_noop hget (fun _ h => nomatch h) (fun _ h => by cases h; exact hw rfl)
        | _ =>
          simp only [beh, applyEffects, List.foldl]
          exact hi.caller_noop hget (fun _ h => nomatch h) (fun _ h => nomatch h)
    · exact absurd (applyEffects_snd_some _ _ _ hr) (caller_no_exit _ _ _ _ _ _)
  · exact hi.run_ne h hp

/-- No links, hence no signals. -/
theorem Inv.signal {a b : Sys St Msg} (h : signalE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, _, hsg, _⟩ := signalE_cases h
  rw [hi.signals_nil] at hsg
  cases hsg

/-- A DOWN for the caller lands in its mailbox; anyone else's is a `Grows`. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨w, t, rs, rest, hd, rfl⟩ := downE_of_codec rfl h
  by_cases hw : w = 0
  · subst hw
    obtain ⟨_, _, hcal⟩ := hi.caller_alive
    refine Inv.frame hi (Nat.le_refl _) hi.links_nil hi.signals_nil (stateOf_deliver _ _ _ _)
      (fun c h => by rw [isSome_deliver]; exact h) (fun _ h => h) ?_
      (fun _ _ _ _ => by rw [mcount_deliver]; omega) (fun _ _ _ _ => by rw [mcount_deliver]; omega)
    intro w' rs' h
    rw [hd] at h
    rcases List.mem_cons.mp h with h | h
    · cases h
      right; rw [mcount_deliver]; simp [isSome_of_stateOf hcal]
    · exact Or.inl h
  · exact (hi.pop_down hd hw).grows (grows_deliver _ _ _) hi.links_nil hi.signals_nil

theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b :=
  (hi.set_timers _).grows (timerE_grows h) ((timerE_links h).trans hi.links_nil)
    ((timerE_signals h).trans hi.signals_nil)

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) : Inv b := by
  cases h with
  | run p _ hrun => exact hi.run hrun
  | signal _ hsig => exact hi.signal hsig
  | down _ hdown => exact hi.down hdown
  | timer i _ htimer => exact hi.timer htimer

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
