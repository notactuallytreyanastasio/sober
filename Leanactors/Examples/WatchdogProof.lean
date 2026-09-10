import Leanactors.SysProps
import Leanactors.Examples.Watchdog
/-!
# Leanactors.Examples.WatchdogProof

`Inv` is preserved by every `SysStep`. The frame lemma here lets the
watchdog's boolean flag change as long as its child does not, which covers
the `:timeout` step; everything else is the supervisor recipe.

With `Leanactors.SysProps` the case analysis is by pid: any actor other
than the watchdog survives its step (`set` then `Grows`) or dies
(`terminate_frame`), whatever it popped. The watchdog's own steps are the
spawn shape (`start`, restart on the child's `EXIT`) or a no-op on the
child with a free flag (`pong`, `timeout`, and everything ignored), whose
effects (`send`, `sendAfter`, `signal`) only add.

The watchdog traps, but a `kill` signal would terminate it anyway. It
never receives one: the only `signal` in `beh` is the watchdog's own
`Process.exit(w, :kill)` to its worker `w`, and `w` is never pid 0
(`ChildNe`: every worker was spawned at a fresh pid, which is positive).
`Sys.NoKillTo 0` and `ChildNe` are carried beside `Inv` through
`reach_inv`; `Inv` itself and every theorem about it keep their shape.
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

/-- `Inv.frame` along `Grows`. -/
theorem Inv.grows {a b : Sys St Msg} (hi : Inv a) (h : Grows a b) : Inv b :=
  Inv.frame hi h.next (fun w bb hw => ⟨bb, by rw [h.stateOf 0 hi.next_pos]; exact hw⟩) h.alive
    (fun c => h.links (0, c)) (fun _ _ hs => Or.inl (h.signals _ hs))
    (fun _ _ _ _ => h.mcount 0 _ hi.next_pos)

/-- Overwriting an actor other than the watchdog. -/
theorem Inv.set_ne {a : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (x : Actor St Msg) :
    Inv { a with cfg := a.cfg.set p x } :=
  let f := frame_set a p x
  Inv.frame hi f.next (fun w bb hw => ⟨bb, by rw [f.stateOf 0 (Ne.symm hp) hi.next_pos]; exact hw⟩)
    (fun c h => by rw [isSome_set]; split <;> simp [h]) (fun _ h => h)
    (fun _ _ hs => Or.inl hs) (fun _ _ _ _ => f.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-- `Inv` ignores `timers` and `downs`. -/
theorem Inv.set_timers {a : Sys St Msg} (hi : Inv a) (t : List (Pid × Msg)) :
    Inv { a with timers := t } := ⟨hi.next_pos, hi.dog_alive, hi.child_ok⟩

theorem Inv.set_downs {a : Sys St Msg} (hi : Inv a) (d : List (Pid × Pid × Reason)) :
    Inv { a with downs := d } := ⟨hi.next_pos, hi.dog_alive, hi.child_ok⟩

/-- Dropping the head signal when it is not addressed to the watchdog. -/
theorem Inv.pop_signal {a : Sys St Msg} (hi : Inv a) {q src : Pid} {r : Reason}
    {rest : List (Pid × Pid × Reason)} (hsg : a.signals = (q, src, r) :: rest) (hq : q ≠ 0) :
    Inv { a with signals := rest } :=
  ⟨hi.next_pos, hi.dog_alive, fun c bb hc => by
    rcases hi.child_ok c bb hc with h | ⟨r', hs⟩ | h
    · exact Or.inl h
    · rw [hsg] at hs
      rcases List.mem_cons.mp hs with hs | hs
      · cases hs; exact absurd rfl hq
      · exact Or.inr (Or.inl ⟨r', hs⟩)
    · exact Or.inr (Or.inr h)⟩

/-- An actor `p ≠ 0` terminates from an intermediate system `s` that has
`a`'s watchdog links, a watchdog state and mailbox no smaller than `a`'s,
and `a`'s watchdog-bound signals. -/
theorem Inv.terminate_core {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hnext : a.next ≤ s.next)
    (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ s.links)
    (hdog : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.EXIT c r') ≤ s.cfg.mcount 0 (.EXIT c r')) :
    Inv (s.terminate p r) := by
  refine ⟨Nat.lt_of_lt_of_le hi.next_pos hnext, ?_, ?_⟩
  · obtain ⟨w, bb, h⟩ := hi.dog_alive
    exact ⟨w, bb, by rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hdog, h]⟩
  · intro c bb hc
    rw [terminate_stateOf_ne _ _ _ (Ne.symm hp), hdog] at hc
    rcases hi.child_ok c bb hc with ⟨hal, hl⟩ | ⟨r', hs⟩ | ⟨r', hm⟩
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
    (hdog : s.cfg.stateOf 0 = a.cfg.stateOf 0)
    (halive : ∀ c, c ≠ p → (a.cfg.get c).isSome → (s.cfg.get c).isSome)
    (hsigs : ∀ c r', (0, c, r') ∈ a.signals → (0, c, r') ∈ s.signals)
    (hcount : ∀ c r', a.cfg.mcount 0 (.EXIT c r') ≤ s.cfg.mcount 0 (.EXIT c r')) :
    Inv (s.terminate p r) :=
  hi.terminate_core hp r hnext (fun _ h => hlinks ▸ h) hdog halive hsigs hcount

/-- The same from a `Frame p a s` that keeps the watchdog's links. -/
theorem Inv.terminate_frame {a s : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0) (r : Reason)
    (hf : Frame p a s) (hlinks : ∀ c, (0, c) ∈ a.links → (0, c) ∈ s.links) :
    Inv (s.terminate p r) :=
  hi.terminate_core hp r hf.next hlinks (hf.stateOf 0 (Ne.symm hp) hi.next_pos) hf.alive
    (fun _ _ => hf.signals _) (fun _ _ => hf.mcount 0 _ (Ne.symm hp) hi.next_pos)

/-! ### The watchdog's own steps -/

/-- The watchdog never emits `exit`. -/
theorem dog_no_exit (me fresh : Pid) (w : Option Pid) (bb : Bool) (m : Msg) (r : Reason) :
    Effect.exit r ∉ (beh me fresh (.watchdog w bb) m).2 := by
  cases w <;> cases bb <;> cases m <;> simp [beh] <;> split <;> simp

/-- The watchdog traps. -/
theorem dog_traps {a : Sys St Msg} (hi : Inv a) {act : Actor St Msg} (hget : a.cfg.get 0 = some act) :
    sig.traps act.state = true := by
  obtain ⟨w, bb, hdog⟩ := hi.dog_alive
  simp [stateOf, hget] at hdog
  rw [hdog]; rfl

/-- The spawn shape: a new child at `a.next`, pinged, with the timer armed. -/
theorem Inv.dog_spawn {a : Sys St Msg} (hi : Inv a) (rest : List Msg) :
    Inv { a with
          cfg := ((a.cfg.set 0 ⟨.watchdog (some a.next) true, rest⟩).set a.next
            ⟨.worker false 0, []⟩).deliver a.next .ping,
          next := a.next + 1, links := (0, a.next) :: a.links,
          timers := a.timers ++ [(0, .timeout)] } := by
  have hn0 : a.next ≠ 0 := Nat.ne_of_gt hi.next_pos
  refine ⟨Nat.succ_pos _, ⟨some a.next, true, by simp [stateOf_deliver, stateOf_set, Ne.symm hn0]⟩, ?_⟩
  intro c bb hc
  simp [stateOf_deliver, stateOf_set, Ne.symm hn0] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact Or.inl ⟨by simp [isSome_deliver, isSome_set], by simp⟩

/-- The no-op shape: the watchdog consumes a message that is not its
current child's `EXIT`, keeps its child and may flip its flag. -/
theorem Inv.dog_noop {a : Sys St Msg} (hi : Inv a) {w : Option Pid} {bb : Bool} {m : Msg}
    {rest : List Msg} (hget : a.cfg.get 0 = some ⟨.watchdog w bb, m :: rest⟩) (bb' : Bool)
    (hm : ∀ c r, w = some c → m ≠ .EXIT c r) :
    Inv { a with cfg := a.cfg.set 0 ⟨.watchdog w bb', rest⟩ } := by
  refine ⟨hi.next_pos, ⟨w, bb', by simp [stateOf_set]⟩, ?_⟩
  intro c b' hc
  simp [stateOf_set] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rcases hi.child_ok c bb (by simp [stateOf, hget]) with ⟨hal, hl⟩ | ⟨r, hs⟩ | ⟨r, hm'⟩
  · exact Or.inl ⟨by rw [isSome_set]; split <;> simp [hal], hl⟩
  · exact Or.inr (Or.inl ⟨r, hs⟩)
  · refine Or.inr (Or.inr ⟨r, ?_⟩)
    rw [mcount_of_get hget, if_neg (hm c r rfl)] at hm'
    rw [mcount_set, if_pos rfl]
    simpa using hm'

/-! ### Preservation, one lemma per kind of step -/

/-- Any actor other than the watchdog, popping any message: it survives
(`set` then `Grows`) or dies (`terminate_frame`). -/
theorem Inv.run_ne {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a)
    (hp : p ≠ 0) : Inv b := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  have hg := applyEffects_grows p { a with cfg := a.cfg.set p ⟨(beh p a.next st m).1, rest⟩ }
    (beh p a.next st m).2
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact (hi.set_ne hp _).grows hg
  · exact (hi.set_ne hp _).terminate_frame hp _ (hg.frame p) (fun c => hg.links (0, c))

theorem Inv.run {a b : Sys St Msg} {p : Pid} (h : runE beh a p = some b) (hi : Inv a) : Inv b := by
  by_cases hp : p = 0
  · subst hp
    obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
    obtain ⟨w, bb, hdog⟩ := hi.dog_alive
    simp [stateOf, hget] at hdog
    subst hdog
    simp only at hs'
    rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
    · cases w with
      | none =>
        cases m with
        | start =>
          simp only [beh, applyEffects, List.foldl, applyEffect]
          exact hi.dog_spawn _
        | _ =>
          simp only [beh]
          exact (hi.dog_noop hget _ (fun _ _ hc _ => nomatch hc)).grows (applyEffects_grows _ _ _)
      | some w' =>
        cases m with
        | EXIT who r =>
          by_cases hw : who = w'
          · subst hw
            simp only [beh, if_true, applyEffects, List.foldl, applyEffect]
            exact hi.dog_spawn _
          · simp only [beh, hw, if_false]
            exact (hi.dog_noop hget _ (fun _ _ hc h => by cases hc; cases h; exact hw rfl)).grows
              (applyEffects_grows _ _ _)
        | _ =>
          cases bb <;> simp only [beh] <;>
            exact (hi.dog_noop hget _ (fun _ _ _ h => nomatch h)).grows (applyEffects_grows _ _ _)
    · exact absurd (applyEffects_snd_some _ _ _ hr) (dog_no_exit _ _ _ _ _ _)
  · exact hi.run_ne h hp

/-- A signal to the watchdog becomes an `EXIT` message (it traps, and it is
never a `kill`); a signal to anyone else is a `Grows` or a termination. -/
theorem Inv.signal {a b : Sys St Msg} (h : signalE sig a = some b) (hi : Inv a)
    (hk : a.NoKillTo 0) : Inv b := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  by_cases hq : q = 0
  · subst hq
    rcases hc with ⟨hd, _⟩ | ⟨act, hget, _, _, rfl⟩ | ⟨act, hget, htr, _, _⟩ | ⟨act, hget, htr, _, _⟩
      | ⟨_, _, rfl, _⟩
    · obtain ⟨_, _, hdog⟩ := hi.dog_alive
      simp [stateOf, hd] at hdog
    · refine Inv.frame hi (Nat.le_refl _)
        (fun w bb hw => ⟨bb, by rw [stateOf_deliver]; exact hw⟩)
        (fun c h => by rw [isSome_deliver]; exact h) (fun _ h => h) ?_
        (fun _ _ _ _ => by rw [mcount_deliver]; omega)
      intro c r' hs
      rw [hsg] at hs
      rcases List.mem_cons.mp hs with hs | hs
      · cases hs
        right; rw [mcount_deliver]; simp [sig, hget]
      · exact Or.inl hs
    · rw [dog_traps hi hget] at htr; cases htr
    · rw [dog_traps hi hget] at htr; cases htr
    · exact absurd (by rw [hsg]; exact List.mem_cons_self) (hk src)
  · have hpop := hi.pop_signal hsg hq
    rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact hpop
    · exact hpop.grows (grows_deliver _ _ _)
    · exact hpop
    · exact hpop.terminate_frame hq _ (Frame.refl _ _) (fun _ h => h)
    · exact hpop.terminate_frame hq _ (Frame.refl _ _) (fun _ h => h)

/-- This program declares no DOWN codec, but the proof does not need to know. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, rest, _, hg⟩ := downE_grows h
  exact (hi.set_downs rest).grows hg

theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b :=
  (hi.set_timers _).grows (timerE_grows h)

theorem Inv.step {a b : Sys St Msg} (h : SysStep beh sig a b) (hi : Inv a) (hk : a.NoKillTo 0) :
    Inv b := by
  cases h with
  | run p _ hrun => exact hi.run hrun
  | signal _ hsig => exact hi.signal hsig hk
  | down _ hdown => exact hi.down hdown
  | timer i _ htimer => exact hi.timer htimer

/-! ### The watchdog is never killed -/

/-- No watchdog, at any pid, names pid 0 as its worker. -/
def ChildNe (s : Sys St Msg) : Prop :=
  ∀ p w bb, s.cfg.stateOf p = some (.watchdog (some w) bb) → w ≠ 0

/-- A watchdog state after a step names the fresh pid or the worker it
already had. -/
theorem dog_state_cases (me fresh : Pid) (st : St) (m : Msg) (w : Pid) (bb : Bool)
    (h : (beh me fresh st m).1 = .watchdog (some w) bb) :
    w = fresh ∨ ∃ bb', st = .watchdog (some w) bb' := by
  cases st with
  | watchdog w' b' =>
    cases w' <;> cases b' <;> cases m <;> simp [beh] at h <;> (try split at h) <;> simp_all
  | worker h' n => cases h' <;> cases m <;> simp [beh] at h

/-- Everything ever spawned is a worker. -/
theorem beh_spawns_workers (me fresh : Pid) (st : St) (m : Msg) :
    ∀ e ∈ (beh me fresh st m).2, ∀ x, e.init? = some x → ∃ h n, x = .worker h n := by
  cases st with
  | watchdog w' b' =>
    cases w' <;> cases b' <;> cases m <;> simp [beh, Effect.init?] <;> split <;> simp [Effect.init?]
  | worker h' n => cases h' <;> cases m <;> simp [beh, Effect.init?]

/-- The only signal in `beh` is the watchdog's kill to its own worker. -/
theorem dog_signal (me fresh : Pid) (st : St) (m : Msg) {q : Pid} {r : Reason}
    (h : Effect.signal q r ∈ (beh me fresh st m).2) : ∃ bb, st = .watchdog (some q) bb := by
  cases st with
  | watchdog w' b' =>
    cases w' <;> cases b' <;> cases m <;> simp [beh] at h <;> (try split at h) <;> simp_all
  | worker h' n => cases h' <;> cases m <;> simp [beh] at h

theorem childNe_step {a b : Sys St Msg} (h : SysStep beh sig a b) (hc : ChildNe a) (hn : 0 < a.next) :
    ChildNe b := by
  intro p w bb hp
  rcases h.stateOf_spawn_cases p with h1 | h1 | ⟨q, st, m, rest, hget, rfl, h1⟩
    | ⟨q, st, m, rest, hget, e, he, h1⟩
  · exact hc p w bb (h1 ▸ hp)
  · rw [h1] at hp; cases hp
  · rw [h1] at hp
    rcases dog_state_cases _ _ _ _ _ _ (Option.some.inj hp) with rfl | ⟨bb', hst⟩
    · exact Nat.ne_of_gt hn
    · exact hc p w bb' (by simp [stateOf, hget, hst])
  · rw [← h1] at hp
    obtain ⟨_, _, hx⟩ := beh_spawns_workers _ _ _ _ e he _ hp
    cases hx

theorem noKillTo_step {a b : Sys St Msg} (h : SysStep beh sig a b) (hk : a.NoKillTo 0)
    (hc : ChildNe a) : b.NoKillTo 0 :=
  h.noKillTo hk (fun q st m _ hget hmem => by
    obtain ⟨bb, rfl⟩ := dog_signal _ _ _ _ hmem
    exact hc q 0 bb (by simp [stateOf, hget]) rfl)

/-! ### From the initial system -/

theorem init_inv : Inv init := by
  refine ⟨by decide, ⟨none, false, by simp [init, stateOf, Config.get]⟩, ?_⟩
  intro c bb h
  simp [init, stateOf, Config.get] at h

theorem init_noKillTo : init.NoKillTo 0 := NoKillTo.of_signals_nil rfl

theorem init_childNe : ChildNe init := by
  intro p w bb h
  simp [init, stateOf, Config.get] at h

theorem reach_inv {s : Sys St Msg} (hr : SysReach beh sig init s) : Inv s :=
  (hr.inv (I := fun s => Inv s ∧ s.NoKillTo 0 ∧ ChildNe s)
    (fun h ⟨hi, hk, hc⟩ => ⟨Inv.step h hi hk, noKillTo_step h hk hc, childNe_step h hc hi.next_pos⟩)
    ⟨init_inv, init_noKillTo, init_childNe⟩).1

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
