import Leanactors.Sys
/-!
# Leanactors.SysProps

Metatheory of the `Sys` layer: what one step can and cannot change. The
example proofs (`SupervisorProof`, `TaskProof`, `WatchdogProof`) each
re-derive these facts by unfolding `runE`, `applyEffects` and `terminate`
by hand; this file states them once.

## Frames

* `Sys.Grows a b`: `b` is `a` with things only added. `next` does not
  decrease, every pid below `a.next` keeps its state, live actors stay
  live, mailbox counts below `a.next` do not decrease, and `links`,
  `monitors`, `signals`, `downs`, `timers` are supersets. Reflexive and
  transitive.
* `Sys.Frame p a b`: the same with `p` exempt: `p`'s own state, liveness,
  count and links/monitors involving `p` may change. Reflexive,
  transitive, and `Grows.frame` embeds.

## Effects (`Sys.applyEffect`, `Sys.applyEffects`)

* `applyEffect_grows`, `applyEffects_grows`: every effect list only adds
  (`applyEffects_next`, `applyEffects_stateOf`, `applyEffects_alive`,
  `applyEffects_mcount`, `applyEffects_mem_links`, …, are the projections).
* `applyEffects_snd_none`: no `exit` in the list means no pending exit;
  `applyEffects_snd_some`: a pending exit came from an `exit` effect.
* `Effect.isolated` (everything but `link`, `spawnLink`, `signal`) and
  `applyEffects_links_signals_of_isolated`: such effects leave `links` and
  `signals` exactly as they were (a behaviour that never links keeps an
  invariant's `links = []` and `signals = []`).

## Termination (`Sys.terminate`)

* `terminate_stateOf`, `terminate_isSome`, `terminate_mcount`,
  `terminate_next`, `terminate_timers`: everything except `p` untouched.
* `terminate_mem_links`, `terminate_mem_monitors`: pairs not involving `p`
  survive; `terminate_mem_signals`, `terminate_mem_downs`: old entries
  survive.
* `terminate_signal_of_link`, `terminate_signal_of_link'`: a linked actor
  (either orientation) gets a signal; `terminate_down_of_monitor`: a watcher
  gets a DOWN; `terminate_mem_signals_iff`, `terminate_mem_downs_iff`: the
  exact new contents; `terminate_signals_of_links_nil`,
  `terminate_links_of_links_nil`, `terminate_downs_of_monitors_nil`: nothing
  is queued without links or monitors. `terminate_frame`:
  `Frame p s (s.terminate p r)`.
* `mem_linkedTo_iff`, `mem_watchers_iff`, `mem_unlink_iff`,
  `mem_unmonitor_iff`: the neighbourhood functions, exactly.

## Steps

* `runE_cases`: `runE beh s p = some s'` unpacks into the popped message and
  either a plain result or a self-terminated one.
* `runE_frame`: `Frame p s s'` (`runE_next`, `runE_stateOf_of_ne`,
  `runE_alive_of_ne`, `runE_mcount_of_ne` are its projections: any pid other
  than `p` below `s.next` keeps its state, no disjunction needed, because
  `runE` terminates only `p`); `runE_stateOf_self`: `p` ends in the state
  the behaviour returned or is dead; `runE_stateOf_self_of_no_exit`,
  `runE_of_no_exit`: without an `exit` effect `p` survives and keeps its
  links, monitors and timers.
* `signalE_cases`, `signalE_frame`, `signalE_next`, `signalE_stateOf`:
  delivering a signal to `q` is a `Frame q` from the system minus that
  signal, and `q` either keeps its state or dies of an `error` or `kill`
  signal (`kill` ignores `traps`).
* `downE_cases`, `downE_grows`, `downE_next`, `downE_stateOf`,
  `downE_links`, `downE_signals`; `downE_of_codec`: with a DOWN codec the
  step is always one `deliver` (a dead watcher drops it inside `deliver`);
  `timerE_cases`, `timerE_grows`, `timerE_next`, `timerE_stateOf`,
  `timerE_links`, `timerE_signals`.
* `SysStep.next_mono`, `SysReach.next_mono`; `SysStep.stateOf_cases`: a pid
  below `next` is unchanged, dead, or the actor that ran;
  `SysStep.stateOf_none`, `SysReach.stateOf_none`: no resurrection.
* `Sys.Fresh`: pids at or above `next` are dead. `Sys.fresh_ofList`
  establishes it, `SysStep.fresh` / `SysReach.fresh` preserve it, and
  `Fresh.lt_next`, `Frame.stateOf_of_fresh`, `Frame.mcount_of_fresh`,
  `Grows.stateOf_of_fresh`, `Grows.mcount_of_fresh` trade the `q < next`
  side conditions for liveness.

## Where signals and actors come from

* `applyEffects_mem_signals_cases`: a signal after a step's effects is an old
  one, a `noproc` error from `link`, or a `signal` effect of the step.
* `Effect.init?` and `applyEffects_stateOf_cases`,
  `runE_stateOf_spawn_cases`, `SysStep.stateOf_spawn_cases`: every actor
  after a step is unchanged, dead, the actor that ran, or freshly spawned
  in the initial state of one of that step's effects (no `q < next` bound,
  unlike `SysStep.stateOf_cases`).
* `Sys.NoKillTo p`: no pending `kill` is addressed to `p`. Since a `kill`
  terminates even a trapping actor, a proof that `p` never dies needs it;
  `NoKillTo.runE` (given that no popped message makes anyone `signal p
  .kill`), `NoKillTo.signalE`, `NoKillTo.downE`, `NoKillTo.timerE` and
  `SysStep.noKillTo` preserve it. `runE` reports a self-exit as
  `reason.propagated`, never `kill` (`Reason.propagated_ne_kill`), and a
  killed actor's links see `error`, so only a `signal` effect can create
  a `kill` signal.

`Leanactors.Examples.SysPropsDemo` re-proves the timer, DOWN and no-exit
worker cases of the supervisor's `Inv.step` with these lemmas.

Note for proof authors: `omega` does not see through the `Pid` abbreviation,
so arithmetic on pids here uses `Nat.lt_of_lt_of_le` and friends.
-/

namespace Leanactors

variable {σ μ : Type}

open Config

/-! ## Neighbourhoods -/

theorem mem_linkedTo_of_mem' {links : List (Pid × Pid)} {p q : Pid} (h : (p, q) ∈ links) :
    q ∈ linkedTo links p := by
  unfold linkedTo
  rw [List.mem_filterMap]
  exact ⟨(p, q), h, by simp⟩

theorem mem_linkedTo_iff {links : List (Pid × Pid)} {p q : Pid} :
    q ∈ linkedTo links p ↔ (p, q) ∈ links ∨ (q, p) ∈ links := by
  constructor
  · intro h
    unfold linkedTo at h
    rw [List.mem_filterMap] at h
    obtain ⟨⟨a, b⟩, hab, he⟩ := h
    by_cases ha : a = p
    · subst ha
      simp at he
      subst he
      exact Or.inl hab
    · by_cases hb : b = p
      · subst hb
        simp [ha] at he
        subst he
        exact Or.inr hab
      · simp [ha, hb] at he
  · rintro (h | h)
    · exact mem_linkedTo_of_mem' h
    · exact mem_linkedTo_of_mem h

theorem mem_watchers_iff {monitors : List (Pid × Pid)} {p w : Pid} :
    w ∈ watchers monitors p ↔ (w, p) ∈ monitors := by
  constructor
  · intro h
    unfold watchers at h
    rw [List.mem_filterMap] at h
    obtain ⟨⟨a, b⟩, hab, he⟩ := h
    by_cases hb : b = p
    · subst hb
      simp at he
      subst he
      exact hab
    · simp [hb] at he
  · exact mem_watchers_of_mem

theorem mem_unlink_iff {links : List (Pid × Pid)} {a b p : Pid} :
    (a, b) ∈ unlink links p ↔ (a, b) ∈ links ∧ a ≠ p ∧ b ≠ p := by
  unfold unlink
  rw [List.mem_filter]
  simp

theorem mem_unmonitor_iff {monitors : List (Pid × Pid)} {a b p : Pid} :
    (a, b) ∈ unmonitor monitors p ↔ (a, b) ∈ monitors ∧ a ≠ p ∧ b ≠ p := by
  unfold unmonitor
  rw [List.mem_filter]
  simp

/-- A delivery to a dead pid is dropped (`Config.deliver` matches on the actor). -/
theorem deliver_of_get_none (c : Config σ μ) {q : Pid} (hq : c.get q = none) (m : μ) :
    c.deliver q m = c := by
  unfold deliver
  have hq' : c.actors q = none := hq
  rw [hq']

namespace Sys

/-! ## Frames -/

/-- `b` is `a` with things only added. -/
structure Grows (a b : Sys σ μ) : Prop where
  next : a.next ≤ b.next
  stateOf : ∀ q, q < a.next → b.cfg.stateOf q = a.cfg.stateOf q
  alive : ∀ q, (a.cfg.get q).isSome → (b.cfg.get q).isSome
  mcount : ∀ [DecidableEq μ] (q : Pid) (m : μ), q < a.next → a.cfg.mcount q m ≤ b.cfg.mcount q m
  links : ∀ x ∈ a.links, x ∈ b.links
  monitors : ∀ x ∈ a.monitors, x ∈ b.monitors
  signals : ∀ x ∈ a.signals, x ∈ b.signals
  downs : ∀ x ∈ a.downs, x ∈ b.downs
  timers : ∀ x ∈ a.timers, x ∈ b.timers

/-- `b` is `a` with things only added, except that `p` may have changed
state, died, or lost its links and monitors. Timers are only added: a
death keeps them (`terminate_timers`). -/
structure Frame (p : Pid) (a b : Sys σ μ) : Prop where
  next : a.next ≤ b.next
  stateOf : ∀ q, q ≠ p → q < a.next → b.cfg.stateOf q = a.cfg.stateOf q
  alive : ∀ q, q ≠ p → (a.cfg.get q).isSome → (b.cfg.get q).isSome
  mcount : ∀ [DecidableEq μ] (q : Pid) (m : μ), q ≠ p → q < a.next →
    a.cfg.mcount q m ≤ b.cfg.mcount q m
  links : ∀ x ∈ a.links, x.1 ≠ p → x.2 ≠ p → x ∈ b.links
  monitors : ∀ x ∈ a.monitors, x.1 ≠ p → x.2 ≠ p → x ∈ b.monitors
  signals : ∀ x ∈ a.signals, x ∈ b.signals
  downs : ∀ x ∈ a.downs, x ∈ b.downs
  timers : ∀ x ∈ a.timers, x ∈ b.timers

theorem Grows.refl (a : Sys σ μ) : Grows a a :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
   fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Grows.trans {a b c : Sys σ μ} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨Nat.le_trans h1.next h2.next,
   fun q hq => (h2.stateOf q (Nat.lt_of_lt_of_le hq h1.next)).trans (h1.stateOf q hq),
   fun q h => h2.alive q (h1.alive q h),
   fun q m hq => Nat.le_trans (h1.mcount q m hq) (h2.mcount q m (Nat.lt_of_lt_of_le hq h1.next)),
   fun x h => h2.links x (h1.links x h),
   fun x h => h2.monitors x (h1.monitors x h),
   fun x h => h2.signals x (h1.signals x h),
   fun x h => h2.downs x (h1.downs x h),
   fun x h => h2.timers x (h1.timers x h)⟩

theorem Grows.frame {a b : Sys σ μ} (h : Grows a b) (p : Pid) : Frame p a b :=
  ⟨h.next, fun q _ hq => h.stateOf q hq, fun q _ => h.alive q, fun q m _ hq => h.mcount q m hq,
   fun x hx _ _ => h.links x hx, fun x hx _ _ => h.monitors x hx, h.signals, h.downs, h.timers⟩

theorem Frame.refl (p : Pid) (a : Sys σ μ) : Frame p a a := (Grows.refl a).frame p

theorem Frame.trans {p : Pid} {a b c : Sys σ μ} (h1 : Frame p a b) (h2 : Frame p b c) :
    Frame p a c :=
  ⟨Nat.le_trans h1.next h2.next,
   fun q hp hq => (h2.stateOf q hp (Nat.lt_of_lt_of_le hq h1.next)).trans (h1.stateOf q hp hq),
   fun q hp h => h2.alive q hp (h1.alive q hp h),
   fun q m hp hq =>
     Nat.le_trans (h1.mcount q m hp hq) (h2.mcount q m hp (Nat.lt_of_lt_of_le hq h1.next)),
   fun x h h1' h2' => h2.links x (h1.links x h h1' h2') h1' h2',
   fun x h h1' h2' => h2.monitors x (h1.monitors x h h1' h2') h1' h2',
   fun x h => h2.signals x (h1.signals x h),
   fun x h => h2.downs x (h1.downs x h),
   fun x h => h2.timers x (h1.timers x h)⟩

/-- A frame followed by growth is a frame. -/
theorem Frame.trans_grows {p : Pid} {a b c : Sys σ μ} (h1 : Frame p a b) (h2 : Grows b c) :
    Frame p a c := h1.trans (h2.frame p)

theorem Grows.trans_frame {p : Pid} {a b c : Sys σ μ} (h1 : Grows a b) (h2 : Frame p b c) :
    Frame p a c := (h1.frame p).trans h2

/-! ### Frames from the `Config` operations -/

/-- Only the `cfg` changed, by a delivery. -/
theorem grows_deliver (s : Sys σ μ) (q : Pid) (m : μ) :
    Grows s { s with cfg := s.cfg.deliver q m } :=
  ⟨Nat.le_refl _, fun _ _ => stateOf_deliver _ _ _ _, fun _ h => by rw [isSome_deliver]; exact h,
   fun _ _ _ => by rw [mcount_deliver]; omega,
   fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Overwriting `p`'s actor record. -/
theorem frame_set (s : Sys σ μ) (p : Pid) (a : Actor σ μ) :
    Frame p s { s with cfg := s.cfg.set p a } :=
  ⟨Nat.le_refl _, fun _ hp _ => by simp [stateOf_set, hp],
   fun _ hp h => by rw [isSome_set]; simp [hp, h],
   fun _ _ hp _ => by simp [mcount_set, hp],
   fun _ h _ _ => h, fun _ h _ _ => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Creating an actor at the fresh pid and bumping the counter. -/
theorem grows_spawn (s : Sys σ μ) (init : σ) :
    Grows s { s with cfg := s.cfg.set s.next ⟨init, []⟩, next := s.next + 1 } :=
  ⟨Nat.le_succ _, fun _ hq => by simp [stateOf_set, Nat.ne_of_lt hq],
   fun _ h => by rw [isSome_set]; split <;> simp [h],
   fun _ _ hq => by simp [mcount_set, Nat.ne_of_lt hq],
   fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-! ## Effects -/

theorem applyEffect_grows (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) :
    Grows s (applyEffect p (s, d) e).1 := by
  cases e with
  | send to m => exact grows_deliver s to m
  | spawn init => exact grows_spawn s init
  | spawnLink init =>
    refine (grows_spawn s init).trans ?_
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
      fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | link q =>
    simp only [applyEffect]
    split
    · exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
        fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
    · exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
        fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
  | monitor q =>
    simp only [applyEffect]
    split
    · exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
        fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h⟩
    · exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
        fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
  | spawnMonitor init =>
    refine (grows_spawn s init).trans ?_
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
      fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | sendAfter to m =>
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
      fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩
  | signal q r =>
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h, fun _ _ _ => Nat.le_refl _,
      fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
  | exit r => exact Grows.refl s

theorem foldl_applyEffect_grows (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) : Grows s (effs.foldl (applyEffect p) (s, d)).1 := by
  induction effs generalizing s d with
  | nil => exact Grows.refl s
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h := applyEffect_grows p s d e
    revert h
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h
    exact h.trans (ih s1 d1)

theorem applyEffects_grows (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) :
    Grows s (applyEffects p s effs).1 :=
  foldl_applyEffect_grows p effs s none

/-! ### Projections, for direct use -/

theorem applyEffects_next (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) :
    s.next ≤ (applyEffects p s effs).1.next := (applyEffects_grows p s effs).next

theorem applyEffects_stateOf (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) {q : Pid}
    (hq : q < s.next) : (applyEffects p s effs).1.cfg.stateOf q = s.cfg.stateOf q :=
  (applyEffects_grows p s effs).stateOf q hq

theorem applyEffects_alive (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) {q : Pid}
    (h : (s.cfg.get q).isSome) : ((applyEffects p s effs).1.cfg.get q).isSome :=
  (applyEffects_grows p s effs).alive q h

theorem applyEffects_mcount [DecidableEq μ] (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {q : Pid} (m : μ) (hq : q < s.next) :
    s.cfg.mcount q m ≤ (applyEffects p s effs).1.cfg.mcount q m :=
  (applyEffects_grows p s effs).mcount q m hq

theorem applyEffects_mem_links (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) {x : Pid × Pid}
    (h : x ∈ s.links) : x ∈ (applyEffects p s effs).1.links :=
  (applyEffects_grows p s effs).links x h

theorem applyEffects_mem_monitors (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {x : Pid × Pid} (h : x ∈ s.monitors) : x ∈ (applyEffects p s effs).1.monitors :=
  (applyEffects_grows p s effs).monitors x h

theorem applyEffects_mem_signals (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {x : Pid × Pid × Reason} (h : x ∈ s.signals) : x ∈ (applyEffects p s effs).1.signals :=
  (applyEffects_grows p s effs).signals x h

theorem applyEffects_mem_downs (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {x : Pid × Pid × Reason} (h : x ∈ s.downs) : x ∈ (applyEffects p s effs).1.downs :=
  (applyEffects_grows p s effs).downs x h

theorem applyEffects_mem_timers (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {x : Pid × μ} (h : x ∈ s.timers) : x ∈ (applyEffects p s effs).1.timers :=
  (applyEffects_grows p s effs).timers x h

/-! ### The pending self-exit -/

theorem applyEffect_snd_of_not_exit (p : Pid) (s : Sys σ μ) (d : Option Reason) {e : Effect σ μ}
    (he : ∀ r, e ≠ .exit r) : (applyEffect p (s, d) e).2 = d := by
  cases e with
  | exit r => exact absurd rfl (he r)
  | link q => simp only [applyEffect]; split <;> rfl
  | monitor q => simp only [applyEffect]; split <;> rfl
  | _ => rfl

theorem foldl_applyEffect_snd_none (p : Pid) {effs : List (Effect σ μ)}
    (h : ∀ r, Effect.exit r ∉ effs) (s : Sys σ μ) (d : Option Reason) :
    (effs.foldl (applyEffect p) (s, d)).2 = d := by
  induction effs generalizing s d with
  | nil => rfl
  | cons e rest ih =>
    rw [List.foldl_cons]
    have he : ∀ r, e ≠ .exit r := fun r hr => h r (hr ▸ List.mem_cons_self)
    have hd := applyEffect_snd_of_not_exit p s d he
    revert hd
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro hd
    subst hd
    exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) s1 d1

/-- A behaviour that never emits `exit` never terminates itself. -/
theorem applyEffects_snd_none (p : Pid) (s : Sys σ μ) {effs : List (Effect σ μ)}
    (h : ∀ r, Effect.exit r ∉ effs) : (applyEffects p s effs).2 = none :=
  foldl_applyEffect_snd_none p h s none

theorem applyEffect_snd_some (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) {r : Reason}
    (h : (applyEffect p (s, d) e).2 = some r) : d = some r ∨ e = .exit r := by
  cases e with
  | exit r' => exact Or.inr (by simp only [applyEffect] at h; rw [Option.some.inj h])
  | link q => simp only [applyEffect] at h; split at h <;> exact Or.inl h
  | monitor q => simp only [applyEffect] at h; split at h <;> exact Or.inl h
  | _ => exact Or.inl h

theorem foldl_applyEffect_snd_some (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) {r : Reason} (h : (effs.foldl (applyEffect p) (s, d)).2 = some r) :
    d = some r ∨ Effect.exit r ∈ effs := by
  induction effs generalizing s d with
  | nil => exact Or.inl h
  | cons e rest ih =>
    rw [List.foldl_cons] at h
    have hstep := @applyEffect_snd_some σ μ p s d e
    revert h hstep
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h hstep
    rcases ih s1 d1 h with h1 | h1
    · rcases hstep h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2 ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A pending self-exit came from an `exit` effect. -/
theorem applyEffects_snd_some (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) {r : Reason}
    (h : (applyEffects p s effs).2 = some r) : Effect.exit r ∈ effs := by
  rcases foldl_applyEffect_snd_some p effs s none h with h1 | h1
  · cases h1
  · exact h1

/-! ### Effects that never touch `links` or `signals` -/

end Sys

/-- Everything but `link`, `spawnLink` and `signal` (a `link` to a dead pid
queues a `noproc` signal, so it is excluded too). -/
def Effect.isolated : Effect σ μ → Bool
  | .link _ | .spawnLink _ | .signal _ _ => false
  | _ => true

namespace Sys

theorem applyEffect_links_signals_of_isolated (p : Pid) (s : Sys σ μ) (d : Option Reason)
    {e : Effect σ μ} (he : e.isolated = true) :
    (applyEffect p (s, d) e).1.links = s.links ∧ (applyEffect p (s, d) e).1.signals = s.signals := by
  cases e with
  | link q => cases he
  | spawnLink init => cases he
  | signal q r => cases he
  | monitor q => simp only [applyEffect]; split <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem foldl_applyEffect_links_signals_of_isolated (p : Pid) {effs : List (Effect σ μ)}
    (h : ∀ e ∈ effs, e.isolated = true) (s : Sys σ μ) (d : Option Reason) :
    (effs.foldl (applyEffect p) (s, d)).1.links = s.links ∧
    (effs.foldl (applyEffect p) (s, d)).1.signals = s.signals := by
  induction effs generalizing s d with
  | nil => exact ⟨rfl, rfl⟩
  | cons e rest ih =>
    rw [List.foldl_cons]
    have he := applyEffect_links_signals_of_isolated p s d (h e List.mem_cons_self)
    revert he
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro he
    obtain ⟨h1, h2⟩ := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) s1 d1
    exact ⟨h1.trans he.1, h2.trans he.2⟩

/-- A behaviour that never links or signals leaves `links` and `signals` alone. -/
theorem applyEffects_links_signals_of_isolated (p : Pid) (s : Sys σ μ) {effs : List (Effect σ μ)}
    (h : ∀ e ∈ effs, e.isolated = true) :
    (applyEffects p s effs).1.links = s.links ∧ (applyEffects p s effs).1.signals = s.signals :=
  foldl_applyEffect_links_signals_of_isolated p h s none

/-! ### Where signals come from -/

/-- A signal after one effect of `p` is an old one, a `noproc` error to `p`
from a `link` to a dead pid, or the `signal` effect itself. -/
theorem applyEffect_mem_signals_cases (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ)
    {x : Pid × Pid × Reason} (hx : x ∈ (applyEffect p (s, d) e).1.signals) :
    x ∈ s.signals ∨ (∃ q, x = (p, q, .error)) ∨ ∃ q r, x = (q, p, r) ∧ e = .signal q r := by
  cases e with
  | link q =>
    simp only [applyEffect] at hx
    split at hx
    · exact Or.inl hx
    · rcases List.mem_append.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨q, by simpa using h⟩)
  | monitor q => simp only [applyEffect] at hx; split at hx <;> exact Or.inl hx
  | signal q r =>
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨q, r, by simpa using h, rfl⟩)
  | _ => exact Or.inl hx

theorem foldl_applyEffect_mem_signals_cases (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) {x : Pid × Pid × Reason}
    (hx : x ∈ (effs.foldl (applyEffect p) (s, d)).1.signals) :
    x ∈ s.signals ∨ (∃ q, x = (p, q, .error)) ∨ ∃ q r, x = (q, p, r) ∧ Effect.signal q r ∈ effs := by
  induction effs generalizing s d with
  | nil => exact Or.inl hx
  | cons e rest ih =>
    rw [List.foldl_cons] at hx
    have hstep := @applyEffect_mem_signals_cases σ μ p s d e
    revert hx hstep
    generalize applyEffect p (s, d) e = y
    obtain ⟨s1, d1⟩ := y
    intro hx hstep
    rcases ih s1 d1 hx with h1 | h1 | ⟨q, r, hxe, he⟩
    · rcases hstep h1 with h2 | h2 | ⟨q, r, hxe, he⟩
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨q, r, hxe, he ▸ List.mem_cons_self⟩)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨q, r, hxe, List.mem_cons_of_mem _ he⟩)

/-- A signal after a step's effects is an old one, a `noproc` error, or one
of the step's `signal` effects. In particular a `kill` signal can only come
from `signal q .kill`. -/
theorem applyEffects_mem_signals_cases (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ))
    {x : Pid × Pid × Reason} (hx : x ∈ (applyEffects p s effs).1.signals) :
    x ∈ s.signals ∨ (∃ q, x = (p, q, .error)) ∨ ∃ q r, x = (q, p, r) ∧ Effect.signal q r ∈ effs :=
  foldl_applyEffect_mem_signals_cases p effs s none hx

/-! ### Where actors come from -/

end Sys

/-- The initial state a spawning effect creates. -/
def Effect.init? : Effect σ μ → Option σ
  | .spawn i | .spawnLink i | .spawnMonitor i => some i
  | _ => none

namespace Sys

theorem applyEffect_stateOf (p : Pid) (s : Sys σ μ) (d : Option Reason) (e : Effect σ μ) (q : Pid) :
    (applyEffect p (s, d) e).1.cfg.stateOf q = s.cfg.stateOf q ∨
      e.init? = (applyEffect p (s, d) e).1.cfg.stateOf q := by
  cases e with
  | send to m => exact Or.inl (stateOf_deliver _ _ _ _)
  | spawn init | spawnLink init | spawnMonitor init =>
    by_cases hq : q = s.next
    · subst hq
      exact Or.inr (by simp [applyEffect, Effect.init?, stateOf_set])
    · exact Or.inl (by simp [applyEffect, stateOf_set, hq])
  | link q' => simp only [applyEffect]; split <;> exact Or.inl rfl
  | monitor q' => simp only [applyEffect]; split <;> exact Or.inl rfl
  | _ => exact Or.inl rfl

theorem foldl_applyEffect_stateOf (p : Pid) (effs : List (Effect σ μ)) (s : Sys σ μ)
    (d : Option Reason) (q : Pid) :
    (effs.foldl (applyEffect p) (s, d)).1.cfg.stateOf q = s.cfg.stateOf q ∨
      ∃ e ∈ effs, e.init? = (effs.foldl (applyEffect p) (s, d)).1.cfg.stateOf q := by
  induction effs generalizing s d with
  | nil => exact Or.inl rfl
  | cons e rest ih =>
    rw [List.foldl_cons]
    have hstep := applyEffect_stateOf p s d e q
    revert hstep
    generalize applyEffect p (s, d) e = y
    obtain ⟨s1, d1⟩ := y
    intro hstep
    rcases ih s1 d1 with h1 | ⟨e', he', h1⟩
    · rcases hstep with h2 | h2
      · exact Or.inl (h1.trans h2)
      · exact Or.inr ⟨e, List.mem_cons_self, h2.trans h1.symm⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1⟩

/-- Every actor after a step's effects is an old one or was spawned by one
of the effects, in that effect's initial state. -/
theorem applyEffects_stateOf_cases (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) (q : Pid) :
    (applyEffects p s effs).1.cfg.stateOf q = s.cfg.stateOf q ∨
      ∃ e ∈ effs, e.init? = (applyEffects p s effs).1.cfg.stateOf q :=
  foldl_applyEffect_stateOf p effs s none q

/-! ## Termination -/

section terminate

variable (s : Sys σ μ) (p : Pid) (r : Reason)

@[simp] theorem terminate_next : (s.terminate p r).next = s.next := rfl
/-- Pending timers survive a death (`terminate` used to omit the field, so
the structure default `[]` silently disarmed every timer). -/
@[simp] theorem terminate_timers : (s.terminate p r).timers = s.timers := rfl
theorem terminate_links : (s.terminate p r).links = unlink s.links p := rfl
theorem terminate_monitors : (s.terminate p r).monitors = unmonitor s.monitors p := rfl
theorem terminate_signals :
    (s.terminate p r).signals = s.signals ++ (linkedTo s.links p).map fun q => (q, p, r) := rfl
theorem terminate_downs :
    (s.terminate p r).downs = s.downs ++ (watchers s.monitors p).map fun w => (w, p, r) := rfl

theorem terminate_stateOf (q : Pid) :
    (s.terminate p r).cfg.stateOf q = if q = p then none else s.cfg.stateOf q :=
  stateOf_remove _ _ _

theorem terminate_isSome (q : Pid) :
    ((s.terminate p r).cfg.get q).isSome = if q = p then false else (s.cfg.get q).isSome :=
  isSome_remove _ _ _

theorem terminate_mcount [DecidableEq μ] (q : Pid) (m : μ) :
    (s.terminate p r).cfg.mcount q m = if q = p then 0 else s.cfg.mcount q m :=
  mcount_remove _ _ _ _

@[simp] theorem terminate_stateOf_self : (s.terminate p r).cfg.stateOf p = none := by
  simp [terminate_stateOf]

theorem terminate_stateOf_ne {q : Pid} (h : q ≠ p) :
    (s.terminate p r).cfg.stateOf q = s.cfg.stateOf q := by
  simp [terminate_stateOf, h]

theorem terminate_isSome_ne {q : Pid} (h : q ≠ p) :
    ((s.terminate p r).cfg.get q).isSome = (s.cfg.get q).isSome := by
  simp [terminate_isSome, h]

theorem terminate_mcount_ne [DecidableEq μ] {q : Pid} (h : q ≠ p) (m : μ) :
    (s.terminate p r).cfg.mcount q m = s.cfg.mcount q m := by
  simp [terminate_mcount, h]

theorem terminate_mem_links {a b : Pid} (h : (a, b) ∈ s.links) (ha : a ≠ p) (hb : b ≠ p) :
    (a, b) ∈ (s.terminate p r).links :=
  mem_unlink h ha hb

theorem terminate_mem_monitors {a b : Pid} (h : (a, b) ∈ s.monitors) (ha : a ≠ p) (hb : b ≠ p) :
    (a, b) ∈ (s.terminate p r).monitors :=
  mem_unmonitor h ha hb

theorem terminate_mem_signals {x : Pid × Pid × Reason} (h : x ∈ s.signals) :
    x ∈ (s.terminate p r).signals :=
  List.mem_append_left _ h

theorem terminate_mem_downs {x : Pid × Pid × Reason} (h : x ∈ s.downs) :
    x ∈ (s.terminate p r).downs :=
  List.mem_append_left _ h

/-- Someone linked to the dying actor gets a signal. -/
theorem terminate_signal_of_linkedTo {q : Pid} (h : q ∈ linkedTo s.links p) :
    (q, p, r) ∈ (s.terminate p r).signals := by
  apply List.mem_append_right
  rw [List.mem_map]
  exact ⟨q, h, rfl⟩

theorem terminate_signal_of_link {q : Pid} (h : (q, p) ∈ s.links) :
    (q, p, r) ∈ (s.terminate p r).signals :=
  terminate_signal_of_linkedTo s p r (mem_linkedTo_of_mem h)

theorem terminate_signal_of_link' {q : Pid} (h : (p, q) ∈ s.links) :
    (q, p, r) ∈ (s.terminate p r).signals :=
  terminate_signal_of_linkedTo s p r (mem_linkedTo_of_mem' h)

/-- Someone watching the dying actor gets a DOWN. -/
theorem terminate_down_of_monitor {w : Pid} (h : (w, p) ∈ s.monitors) :
    (w, p, r) ∈ (s.terminate p r).downs := by
  apply List.mem_append_right
  rw [List.mem_map]
  exact ⟨w, mem_watchers_of_mem h, rfl⟩

/-- Exactly what is in the signal queue after a termination. -/
theorem terminate_mem_signals_iff (x : Pid × Pid × Reason) :
    x ∈ (s.terminate p r).signals ↔
      x ∈ s.signals ∨ ∃ q, x = (q, p, r) ∧ ((p, q) ∈ s.links ∨ (q, p) ∈ s.links) := by
  rw [terminate_signals, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, rfl, mem_linkedTo_iff.mp hq⟩
  · rintro (h | ⟨q, rfl, hq⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, mem_linkedTo_iff.mpr hq, rfl⟩

theorem terminate_mem_downs_iff (x : Pid × Pid × Reason) :
    x ∈ (s.terminate p r).downs ↔ x ∈ s.downs ∨ ∃ w, x = (w, p, r) ∧ (w, p) ∈ s.monitors := by
  rw [terminate_downs, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨w, hw, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, rfl, mem_watchers_iff.mp hw⟩
  · rintro (h | ⟨w, rfl, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, mem_watchers_iff.mpr hw, rfl⟩

/-- With no links the signal queue is untouched; with no monitors so is the DOWN queue. -/
theorem terminate_signals_of_links_nil (h : s.links = []) :
    (s.terminate p r).signals = s.signals := by
  simp [terminate_signals, h, linkedTo]

theorem terminate_links_of_links_nil (h : s.links = []) : (s.terminate p r).links = [] := by
  simp [terminate_links, h, unlink]

theorem terminate_downs_of_monitors_nil (h : s.monitors = []) :
    (s.terminate p r).downs = s.downs := by
  simp [terminate_downs, h, watchers]

theorem terminate_frame : Frame p s (s.terminate p r) :=
  ⟨Nat.le_refl _, fun _ hq _ => terminate_stateOf_ne s p r hq,
   fun _ hq h => by rw [terminate_isSome_ne s p r hq]; exact h,
   fun _ m hq _ => by rw [terminate_mcount_ne s p r hq m]; exact Nat.le_refl _,
   fun x hx h1 h2 => terminate_mem_links s p r hx h1 h2,
   fun x hx h1 h2 => terminate_mem_monitors s p r hx h1 h2,
   fun _ h => terminate_mem_signals s p r h, fun _ h => terminate_mem_downs s p r h,
   fun _ h => h⟩

end terminate

/-! ## `runE` -/

/-- Unpacking a successful `runE`: the popped message, the effects, and the
two ways the step can end (a self-exit with `reason` is reported to links
and monitors as `reason.propagated`). -/
theorem runE_cases {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid} (h : runE beh s p = some s') :
    ∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧
      let out := beh p s.next st m
      let r := applyEffects p { s with cfg := s.cfg.set p ⟨out.1, rest⟩ } out.2
      (r.2 = none ∧ s' = r.1) ∨
      (∃ reason, r.2 = some reason ∧ s' = r.1.terminate p reason.propagated) := by
  unfold runE at h
  split at h
  · rename_i st m rest hget
    refine ⟨st, m, rest, hget, ?_⟩
    obtain rfl := Option.some.inj h
    simp only
    cases hr : (applyEffects p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
        (beh p s.next st m).2).2 with
    | none => exact Or.inl ⟨rfl, by simp⟩
    | some reason => exact Or.inr ⟨reason, rfl, by simp⟩
  · cases h

/-- The running actor is the only thing a `runE` step may damage. -/
theorem runE_frame {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid} (h : runE beh s p = some s') :
    Frame p s s' := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  have h1 := frame_set s p ⟨(beh p s.next st m).1, rest⟩
  have h2 := applyEffects_grows p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
    (beh p s.next st m).2
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact h1.trans_grows h2
  · exact (h1.trans_grows h2).trans (terminate_frame _ p _)

theorem runE_next {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid} (h : runE beh s p = some s') :
    s.next ≤ s'.next := (runE_frame h).next

/-- Every pid other than the running one, below the fresh counter, keeps its
state: `runE` terminates only its own actor. -/
theorem runE_stateOf_of_ne {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') {q : Pid} (hq : q ≠ p) (hlt : q < s.next) :
    s'.cfg.stateOf q = s.cfg.stateOf q := (runE_frame h).stateOf q hq hlt

theorem runE_alive_of_ne {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') {q : Pid} (hq : q ≠ p) (ha : (s.cfg.get q).isSome) :
    (s'.cfg.get q).isSome := (runE_frame h).alive q hq ha

theorem runE_mcount_of_ne [DecidableEq μ] {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') {q : Pid} (m : μ) (hq : q ≠ p) (hlt : q < s.next) :
    s.cfg.mcount q m ≤ s'.cfg.mcount q m := (runE_frame h).mcount q m hq hlt

/-- The running actor ends in the state its behaviour returned, or dead
(`p < s.next` rules out a spawn landing on `p`'s own slot). -/
theorem runE_stateOf_self {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') (hp : p < s.next) :
    (∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧
      s'.cfg.stateOf p = some (beh p s.next st m).1) ∨ s'.cfg.stateOf p = none := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · left
    refine ⟨st, m, rest, hget, ?_⟩
    have hg := applyEffects_grows p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
      (beh p s.next st m).2
    rw [hg.stateOf p hp]
    simp [stateOf_set]
  · right
    exact terminate_stateOf_self _ p _

/-- The running actor does not die if its behaviour emits no `exit`. -/
theorem runE_stateOf_self_of_no_exit {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') {st : σ} {m : μ} {rest : List μ}
    (hget : s.cfg.get p = some ⟨st, m :: rest⟩) (hp : p < s.next)
    (hexit : ∀ r, Effect.exit r ∉ (beh p s.next st m).2) :
    s'.cfg.stateOf p = some (beh p s.next st m).1 := by
  obtain ⟨st', m', rest', hget', hs'⟩ := runE_cases h
  rw [hget] at hget'
  obtain ⟨rfl, rfl, rfl⟩ := (by simpa using hget' : st = st' ∧ m = m' ∧ rest = rest')
  simp only at hs'
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · have hg := applyEffects_grows p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
      (beh p s.next st m).2
    rw [hg.stateOf p hp]
    simp [stateOf_set]
  · exact absurd (applyEffects_snd_some _ _ _ hr) (hexit reason)

/-- If the popped message produces no `exit`, nothing of the running actor
is lost either: it stays alive and keeps its links, monitors and timers. -/
theorem runE_of_no_exit {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s')
    (hexit : ∀ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ →
      ∀ r, Effect.exit r ∉ (beh p s.next st m).2) :
    (∀ q, (s.cfg.get q).isSome → (s'.cfg.get q).isSome) ∧
    (∀ x ∈ s.links, x ∈ s'.links) ∧ (∀ x ∈ s.monitors, x ∈ s'.monitors) ∧
    (∀ x ∈ s.timers, x ∈ s'.timers) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp only at hs'
  have hg := applyEffects_grows p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
    (beh p s.next st m).2
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, hr, _⟩
  · refine ⟨fun q hq => hg.alive q ?_, hg.links, hg.monitors, hg.timers⟩
    rw [isSome_set]
    split <;> simp [hq]
  · exact absurd (applyEffects_snd_some _ _ _ hr) (hexit st m rest hget reason)

/-- **Every actor after a `runE` step**, with no bound on the pid: unchanged,
dead, the actor that ran in the state its behaviour returned, or freshly
spawned by one of the step's effects in that effect's initial state. -/
theorem runE_stateOf_spawn_cases {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') (q : Pid) :
    s'.cfg.stateOf q = s.cfg.stateOf q ∨ s'.cfg.stateOf q = none ∨
      (∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧ q = p ∧
        s'.cfg.stateOf q = some (beh p s.next st m).1) ∨
      (∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧
        ∃ e ∈ (beh p s.next st m).2, e.init? = s'.cfg.stateOf q) := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp only at hs'
  have hc := applyEffects_stateOf_cases p { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ }
    (beh p s.next st m).2 q
  simp only [stateOf_set] at hc
  -- the state at `q` in the system the step ends in, before a possible self-termination
  have key : ∀ s'' : Sys σ μ, s''.cfg.stateOf q = (applyEffects p
        { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } (beh p s.next st m).2).1.cfg.stateOf q →
      s''.cfg.stateOf q = s.cfg.stateOf q ∨ s''.cfg.stateOf q = none ∨
      (∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧ q = p ∧
        s''.cfg.stateOf q = some (beh p s.next st m).1) ∨
      (∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧
        ∃ e ∈ (beh p s.next st m).2, e.init? = s''.cfg.stateOf q) := by
    intro s'' hs''
    rcases hc with hc | ⟨e, he, hc⟩
    · rw [hs'', hc]
      by_cases hq : q = p
      · subst hq
        exact Or.inr (Or.inr (Or.inl ⟨st, m, rest, hget, rfl, by simp⟩))
      · exact Or.inl (by simp [hq])
    · exact Or.inr (Or.inr (Or.inr ⟨st, m, rest, hget, e, he, hs'' ▸ hc⟩))
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact key _ rfl
  · by_cases hq : q = p
    · subst hq
      exact Or.inr (Or.inl (terminate_stateOf_self _ _ _))
    · exact key _ (terminate_stateOf_ne _ _ _ hq)

/-! ## `signalE` -/

/-- Unpacking a successful `signalE`: the head signal and the five ways it
can be handled (target gone, trapped as a message, `normal` ignored, `error`
kills a non-trapping target, `kill` kills the target whatever it traps and
its links see `error`). -/
theorem signalE_cases {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s') :
    ∃ q src r rest, s.signals = (q, src, r) :: rest ∧
      ((s.cfg.get q = none ∧ s' = { s with signals := rest }) ∨
       (∃ a, s.cfg.get q = some a ∧ sig.traps a.state = true ∧ r ≠ .kill ∧
          s' = { s with signals := rest, cfg := s.cfg.deliver q (sig.exitMsg src r) }) ∨
       (∃ a, s.cfg.get q = some a ∧ sig.traps a.state = false ∧ r = .normal ∧
          s' = { s with signals := rest }) ∨
       (∃ a, s.cfg.get q = some a ∧ sig.traps a.state = false ∧ r = .error ∧
          s' = ({ s with signals := rest } : Sys σ μ).terminate q .error) ∨
       (∃ a, s.cfg.get q = some a ∧ r = .kill ∧
          s' = ({ s with signals := rest } : Sys σ μ).terminate q .error)) := by
  unfold signalE at h
  split at h
  · cases h
  · rename_i q src r rest hsg
    refine ⟨q, src, r, rest, hsg, ?_⟩
    obtain rfl := Option.some.inj h
    cases hq : s.cfg.get q with
    | none => exact Or.inl ⟨rfl, by simp⟩
    | some a =>
      cases r with
      | kill => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl, rfl, by simp⟩)))
      | normal =>
        by_cases htr : sig.traps a.state = true
        · exact Or.inr (Or.inl ⟨a, rfl, htr, by simp, by simp [htr]⟩)
        · have htr' : sig.traps a.state = false := by simpa using htr
          exact Or.inr (Or.inr (Or.inl ⟨a, rfl, htr', rfl, by simp [htr']⟩))
      | error =>
        by_cases htr : sig.traps a.state = true
        · exact Or.inr (Or.inl ⟨a, rfl, htr, by simp, by simp [htr]⟩)
        · have htr' : sig.traps a.state = false := by simpa using htr
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl, htr', rfl, by simp [htr']⟩)))

/-- Delivering a signal to `q` is a frame around `q` from the system minus
that signal. -/
theorem signalE_frame {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s') :
    ∃ q src r rest, s.signals = (q, src, r) :: rest ∧ Frame q { s with signals := rest } s' := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  refine ⟨q, src, r, rest, hsg, ?_⟩
  rcases hc with ⟨_, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, rfl⟩
  · exact Frame.refl q _
  · exact (grows_deliver { s with signals := rest } q (sig.exitMsg src r)).frame q
  · exact Frame.refl q _
  · exact terminate_frame _ q .error
  · exact terminate_frame _ q .error

theorem signalE_next {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s') :
    s.next ≤ s'.next := by
  obtain ⟨_, _, _, _, _, hf⟩ := signalE_frame h
  exact hf.next

/-- A signal step leaves every state alone, except that its target may die,
and then only from a signal that is not `normal` (`error` to a non-trapping
target, or `kill` to anyone). -/
theorem signalE_stateOf {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s')
    (q : Pid) : s'.cfg.stateOf q = s.cfg.stateOf q ∨
      (s'.cfg.stateOf q = none ∧ ∃ src r rest, r ≠ .normal ∧ s.signals = (q, src, r) :: rest) := by
  obtain ⟨q', src, r, rest, hsg, hc⟩ := signalE_cases h
  rcases hc with ⟨_, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, rfl, rfl⟩ | ⟨a, _, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl (stateOf_deliver _ _ _ _)
  · exact Or.inl rfl
  · by_cases hq : q = q'
    · subst hq
      exact Or.inr ⟨terminate_stateOf_self _ _ _, src, .error, rest, by simp, hsg⟩
    · exact Or.inl (terminate_stateOf_ne _ _ _ hq)
  · by_cases hq : q = q'
    · subst hq
      exact Or.inr ⟨terminate_stateOf_self _ _ _, src, .kill, rest, by simp, hsg⟩
    · exact Or.inl (terminate_stateOf_ne _ _ _ hq)

/-! ## `downE` -/

theorem downE_cases {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    ∃ w t r rest, s.downs = (w, t, r) :: rest ∧
      ((∃ codec, sig.downMsg = some codec ∧ (s.cfg.get w).isSome ∧
          s' = { s with downs := rest, cfg := s.cfg.deliver w (codec t r) }) ∨
       s' = { s with downs := rest }) := by
  unfold downE at h
  split at h
  · cases h
  · rename_i w t r rest hd
    refine ⟨w, t, r, rest, hd, ?_⟩
    obtain rfl := Option.some.inj h
    cases hc : sig.downMsg with
    | none => exact Or.inr (by simp)
    | some codec =>
      cases hw : s.cfg.get w with
      | none => exact Or.inr (by simp)
      | some a => exact Or.inl ⟨codec, rfl, by simp, by simp⟩

theorem downE_grows {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    ∃ w t r rest, s.downs = (w, t, r) :: rest ∧ Grows { s with downs := rest } s' := by
  obtain ⟨w, t, r, rest, hd, hc⟩ := downE_cases h
  refine ⟨w, t, r, rest, hd, ?_⟩
  rcases hc with ⟨codec, _, _, rfl⟩ | rfl
  · exact grows_deliver { s with downs := rest } w (codec t r)
  · exact Grows.refl _

theorem downE_stateOf {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') (q : Pid) :
    s'.cfg.stateOf q = s.cfg.stateOf q := by
  obtain ⟨_, _, _, _, _, hg⟩ := downE_grows h
  by_cases hq : q < s.next
  · exact hg.stateOf q hq
  · obtain ⟨w, t, r, rest, hd, hc⟩ := downE_cases h
    rcases hc with ⟨codec, _, _, rfl⟩ | rfl
    · exact stateOf_deliver _ _ _ _
    · rfl

theorem downE_next {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    s.next ≤ s'.next := by
  obtain ⟨_, _, _, _, _, hg⟩ := downE_grows h
  exact hg.next

theorem downE_links {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    s'.links = s.links := by
  obtain ⟨_, _, _, _, _, hc⟩ := downE_cases h
  rcases hc with ⟨_, _, _, rfl⟩ | rfl <;> rfl

theorem downE_signals {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    s'.signals = s.signals := by
  obtain ⟨_, _, _, _, _, hc⟩ := downE_cases h
  rcases hc with ⟨_, _, _, rfl⟩ | rfl <;> rfl

/-- With a DOWN codec the step is always one delivery: `deliver` itself
drops the message when the watcher is dead. -/
theorem downE_of_codec {sig : Signals σ μ} {codec : Pid → Reason → μ} (hc : sig.downMsg = some codec)
    {s s' : Sys σ μ} (h : downE sig s = some s') :
    ∃ w t r rest, s.downs = (w, t, r) :: rest ∧
      s' = { s with downs := rest, cfg := s.cfg.deliver w (codec t r) } := by
  unfold downE at h
  split at h
  · cases h
  · rename_i w t r rest hd
    refine ⟨w, t, r, rest, hd, ?_⟩
    obtain rfl := Option.some.inj h
    rw [hc]
    cases hw : s.cfg.get w with
    | none => simp [deliver_of_get_none _ hw]
    | some a => simp

/-! ## `timerE` -/

theorem timerE_cases {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') :
    ∃ to m, s.timers[i]? = some (to, m) ∧
      s' = { s with cfg := s.cfg.deliver to m, timers := s.timers.eraseIdx i } := by
  unfold timerE at h
  split at h
  · cases h
  · rename_i to m ht
    exact ⟨to, m, ht, (Option.some.inj h).symm⟩

theorem timerE_grows {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') :
    Grows { s with timers := s.timers.eraseIdx i } s' := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  exact grows_deliver { s with timers := s.timers.eraseIdx i } to m

theorem timerE_stateOf {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') (q : Pid) :
    s'.cfg.stateOf q = s.cfg.stateOf q := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  exact stateOf_deliver _ _ _ _

theorem timerE_next {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') : s.next ≤ s'.next := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  exact Nat.le_refl _

theorem timerE_links {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') : s'.links = s.links := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  rfl

theorem timerE_signals {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') :
    s'.signals = s.signals := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  rfl

end Sys

/-! ## Steps and reachability -/

open Sys

theorem SysStep.next_mono {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') : s.next ≤ s'.next := by
  cases h with
  | run p _ hrun => exact runE_next hrun
  | signal _ hsig => exact signalE_next hsig
  | down _ hdown => exact downE_next hdown
  | timer i _ htimer => exact timerE_next htimer

theorem SysReach.next_mono {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysReach beh sig s s') : s.next ≤ s'.next := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hst _ ih => exact Nat.le_trans hst.next_mono ih

/-- **Frame for one step.** A pid below the fresh counter keeps its state,
dies, or is the actor that ran (and then it is in the state its behaviour
returned). -/
theorem SysStep.stateOf_cases {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') (q : Pid) (hq : q < s.next) :
    s'.cfg.stateOf q = s.cfg.stateOf q ∨ s'.cfg.stateOf q = none ∨
      ∃ st m rest, s.cfg.get q = some ⟨st, m :: rest⟩ ∧
        s'.cfg.stateOf q = some (beh q s.next st m).1 := by
  cases h with
  | run p _ hrun =>
    by_cases hqp : q = p
    · subst hqp
      rcases runE_stateOf_self hrun hq with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (runE_stateOf_of_ne hrun hqp hq)
  | signal _ hsig =>
    rcases signalE_stateOf hsig q with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | down _ hdown => exact Or.inl (downE_stateOf hdown q)
  | timer i _ htimer => exact Or.inl (timerE_stateOf htimer q)

/-- No resurrection: a dead pid below the counter stays dead. -/
theorem SysStep.stateOf_none {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') {q : Pid} (hq : q < s.next) (hd : s.cfg.stateOf q = none) :
    s'.cfg.stateOf q = none := by
  rcases h.stateOf_cases q hq with h | h | ⟨st, m, rest, hget, _⟩
  · rw [h, hd]
  · exact h
  · simp [stateOf, hget] at hd

theorem SysReach.stateOf_none {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysReach beh sig s s') {q : Pid} (hq : q < s.next) (hd : s.cfg.stateOf q = none) :
    s'.cfg.stateOf q = none := by
  induction h with
  | refl => exact hd
  | step hst _ ih => exact ih (Nat.lt_of_lt_of_le hq hst.next_mono) (hst.stateOf_none hq hd)

/-- `SysStep.stateOf_cases` without the `q < next` bound: a pid is
unchanged, dead, the actor that ran, or spawned by the step. -/
theorem SysStep.stateOf_spawn_cases {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') (q : Pid) :
    s'.cfg.stateOf q = s.cfg.stateOf q ∨ s'.cfg.stateOf q = none ∨
      (∃ p st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧ q = p ∧
        s'.cfg.stateOf q = some (beh p s.next st m).1) ∨
      (∃ p st m rest, s.cfg.get p = some ⟨st, m :: rest⟩ ∧
        ∃ e ∈ (beh p s.next st m).2, e.init? = s'.cfg.stateOf q) := by
  cases h with
  | run p _ hrun =>
    rcases runE_stateOf_spawn_cases hrun q with h | h | ⟨st, m, rest, hget, hq, h⟩ | ⟨st, m, rest, hget, e, he, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨p, st, m, rest, hget, hq, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, st, m, rest, hget, e, he, h⟩))
  | signal _ hsig =>
    rcases signalE_stateOf hsig q with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | down _ hdown => exact Or.inl (downE_stateOf hdown q)
  | timer i _ htimer => exact Or.inl (timerE_stateOf htimer q)

/-! ## Freshness: pids at or above `next` are dead -/

/-- Every pid at or above the counter is unused. Holds for any system built
by `ofList` with pids below `next`, and is preserved by every step. -/
def Sys.Fresh (s : Sys σ μ) : Prop := ∀ q, s.next ≤ q → (s.cfg.get q).isSome = false

namespace Sys

theorem Fresh.lt_next {s : Sys σ μ} (hf : s.Fresh) {q : Pid} (h : (s.cfg.get q).isSome) :
    q < s.next := by
  cases Nat.lt_or_ge q s.next with
  | inl hlt => exact hlt
  | inr hge => rw [hf q hge] at h; cases h

theorem Fresh.lt_next_of_stateOf {s : Sys σ μ} (hf : s.Fresh) {q : Pid} {x : σ}
    (h : s.cfg.stateOf q = some x) : q < s.next :=
  hf.lt_next (isSome_of_stateOf h)

theorem Fresh.lt_next_of_get {s : Sys σ μ} (hf : s.Fresh) {q : Pid} {a : Actor σ μ}
    (h : s.cfg.get q = some a) : q < s.next :=
  hf.lt_next (by rw [h]; rfl)

/-- With freshness, the side condition `q < a.next` of a frame can be
replaced by `q` being alive. -/
theorem Frame.stateOf_of_fresh {p : Pid} {a b : Sys σ μ} (h : Frame p a b) (hf : a.Fresh)
    {q : Pid} (hq : q ≠ p) (ha : (a.cfg.get q).isSome) : b.cfg.stateOf q = a.cfg.stateOf q :=
  h.stateOf q hq (hf.lt_next ha)

theorem Frame.mcount_of_fresh [DecidableEq μ] {p : Pid} {a b : Sys σ μ} (h : Frame p a b)
    (hf : a.Fresh) {q : Pid} (m : μ) (hq : q ≠ p) (ha : (a.cfg.get q).isSome) :
    a.cfg.mcount q m ≤ b.cfg.mcount q m :=
  h.mcount q m hq (hf.lt_next ha)

theorem Grows.stateOf_of_fresh {a b : Sys σ μ} (h : Grows a b) (hf : a.Fresh)
    {q : Pid} (ha : (a.cfg.get q).isSome) : b.cfg.stateOf q = a.cfg.stateOf q :=
  h.stateOf q (hf.lt_next ha)

theorem Grows.mcount_of_fresh [DecidableEq μ] {a b : Sys σ μ} (h : Grows a b) (hf : a.Fresh)
    {q : Pid} (m : μ) (ha : (a.cfg.get q).isSome) : a.cfg.mcount q m ≤ b.cfg.mcount q m :=
  h.mcount q m (hf.lt_next ha)

theorem fresh_deliver {s : Sys σ μ} (hf : s.Fresh) (q : Pid) (m : μ) :
    Fresh { s with cfg := s.cfg.deliver q m } := by
  intro q' hq
  simp only
  rw [isSome_deliver]
  exact hf q' hq

theorem fresh_set {s : Sys σ μ} (hf : s.Fresh) {p : Pid} (hp : p < s.next) (a : Actor σ μ) :
    Fresh { s with cfg := s.cfg.set p a } := by
  intro q hq
  have hq' : s.next ≤ q := hq
  have hne : q ≠ p := fun e => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hp (e ▸ hq'))
  show ((s.cfg.set p a).get q).isSome = false
  rw [isSome_set, if_neg hne]
  exact hf q hq'


theorem fresh_spawn {s : Sys σ μ} (hf : s.Fresh) (init : σ) :
    Fresh { s with cfg := s.cfg.set s.next ⟨init, []⟩, next := s.next + 1 } := by
  intro q hq
  have hq' : s.next + 1 ≤ q := hq
  have hne : q ≠ s.next := fun e => Nat.lt_irrefl s.next (e ▸ hq')
  show ((s.cfg.set s.next ⟨init, []⟩).get q).isSome = false
  rw [isSome_set, if_neg hne]
  exact hf q (Nat.le_of_succ_le hq')

theorem fresh_terminate {s : Sys σ μ} (hf : s.Fresh) (p : Pid) (r : Reason) :
    Fresh (s.terminate p r) := by
  intro q hq
  rw [terminate_isSome]
  split
  · rfl
  · exact hf q hq

theorem fresh_applyEffect {s : Sys σ μ} (hf : s.Fresh) (p : Pid) (d : Option Reason)
    (e : Effect σ μ) : Fresh (applyEffect p (s, d) e).1 := by
  cases e with
  | send to m => exact fresh_deliver hf to m
  | spawn init => exact fresh_spawn hf init
  | spawnLink init => exact fresh_spawn hf init
  | link q => simp only [applyEffect]; split <;> exact hf
  | monitor q => simp only [applyEffect]; split <;> exact hf
  | spawnMonitor init => exact fresh_spawn hf init
  | sendAfter to m => exact hf
  | signal q r => exact hf
  | exit r => exact hf

theorem fresh_foldl_applyEffect (p : Pid) (effs : List (Effect σ μ)) {s : Sys σ μ} (hf : s.Fresh)
    (d : Option Reason) : Fresh (effs.foldl (applyEffect p) (s, d)).1 := by
  induction effs generalizing s d with
  | nil => exact hf
  | cons e rest ih =>
    rw [List.foldl_cons]
    have h := fresh_applyEffect hf p d e
    revert h
    generalize applyEffect p (s, d) e = x
    obtain ⟨s1, d1⟩ := x
    intro h
    exact ih h d1

theorem fresh_applyEffects (p : Pid) {s : Sys σ μ} (hf : s.Fresh) (effs : List (Effect σ μ)) :
    Fresh (applyEffects p s effs).1 :=
  fresh_foldl_applyEffect p effs hf none

theorem fresh_runE {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid} (h : runE beh s p = some s')
    (hf : s.Fresh) : s'.Fresh := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp only at hs'
  have h1 := fresh_applyEffects p (fresh_set hf (hf.lt_next_of_get hget)
    ⟨(beh p s.next st m).1, rest⟩) (beh p s.next st m).2
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact h1
  · exact fresh_terminate h1 p _

theorem fresh_signalE {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s')
    (hf : s.Fresh) : s'.Fresh := by
  obtain ⟨q, src, r, rest, _, hc⟩ := signalE_cases h
  have hf' : Fresh { s with signals := rest } := hf
  rcases hc with ⟨_, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, rfl⟩
  · exact hf'
  · exact fresh_deliver hf' q _
  · exact hf'
  · exact fresh_terminate hf' q .error
  · exact fresh_terminate hf' q .error

theorem fresh_downE {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s')
    (hf : s.Fresh) : s'.Fresh := by
  obtain ⟨w, t, r, rest, _, hc⟩ := downE_cases h
  have hf' : Fresh { s with downs := rest } := hf
  rcases hc with ⟨codec, _, _, rfl⟩ | rfl
  · exact fresh_deliver hf' w _
  · exact hf'

theorem fresh_timerE {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s') (hf : s.Fresh) :
    s'.Fresh := by
  obtain ⟨to, m, _, rfl⟩ := timerE_cases h
  exact fresh_deliver (s := { s with timers := s.timers.eraseIdx i }) hf to m

end Sys

theorem SysStep.fresh {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') (hf : s.Fresh) : s'.Fresh := by
  cases h with
  | run p _ hrun => exact fresh_runE hrun hf
  | signal _ hsig => exact fresh_signalE hsig hf
  | down _ hdown => exact fresh_downE hdown hf
  | timer i _ htimer => exact fresh_timerE htimer hf

theorem SysReach.fresh {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysReach beh sig s s') (hf : s.Fresh) : s'.Fresh :=
  h.inv (fun hst hf => hst.fresh hf) hf

/-- `ofList` with every pid below `n` is fresh at `n`. -/
theorem Sys.fresh_ofList (xs : List (Pid × σ)) (n : Pid) (hxs : ∀ x ∈ xs, x.1 < n)
    (links : List (Pid × Pid)) (signals : List (Pid × Pid × Reason)) :
    Fresh (⟨Config.ofList xs, n, links, signals, [], [], []⟩ : Sys σ μ) := by
  intro q hq
  have hq' : n ≤ q := hq
  simp only [Config.get, Config.ofList, Option.isSome_map]
  cases hf : xs.find? (·.1 = q) with
  | none => rfl
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hxq := List.find?_some hf
    simp at hxq
    have hlt := hxs x hx
    have hle : n ≤ x.1 := by rw [hxq]; exact hq'
    exact absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl _)

/-! ## Kill signals: who can be killed -/

namespace Sys

/-- No pending `kill` signal is addressed to `p`. A `kill` terminates its
target whether or not it traps, so an invariant "p never dies" needs to
know nobody aims one at `p`; the lemmas below preserve it through every
step, given that no behaviour clause ever emits `signal p .kill`. -/
def NoKillTo (p : Pid) (s : Sys σ μ) : Prop := ∀ src, (p, src, .kill) ∉ s.signals

theorem NoKillTo.of_signals_eq {p : Pid} {a b : Sys σ μ} (h : a.NoKillTo p)
    (he : b.signals = a.signals) : b.NoKillTo p := fun src hx => h src (he ▸ hx)

theorem NoKillTo.of_signals_nil {p : Pid} {a : Sys σ μ} (h : a.signals = []) : a.NoKillTo p :=
  fun _ hx => by rw [h] at hx; cases hx

/-- Popping the head signal. -/
theorem NoKillTo.of_cons {p : Pid} {a : Sys σ μ} (h : a.NoKillTo p) {x : Pid × Pid × Reason}
    {rest : List (Pid × Pid × Reason)} (hsg : a.signals = x :: rest) :
    NoKillTo p { a with signals := rest } :=
  fun src hx => h src (by rw [hsg]; exact List.mem_cons_of_mem _ hx)

/-- A death reported with a reason other than `kill` (every death is:
`runE` reports `reason.propagated`, `signalE` reports `error`). -/
theorem NoKillTo.terminate {p : Pid} {s : Sys σ μ} (h : s.NoKillTo p) (q : Pid) {r : Reason}
    (hr : r ≠ .kill) : (s.terminate q r).NoKillTo p := by
  intro src hx
  rcases (terminate_mem_signals_iff s q r _).mp hx with hx | ⟨q', hq', _⟩
  · exact h src hx
  · exact hr (congrArg (·.2.2) hq').symm

theorem NoKillTo.applyEffects {p : Pid} {s : Sys σ μ} (h : s.NoKillTo p) (q : Pid)
    {effs : List (Effect σ μ)} (he : Effect.signal p .kill ∉ effs) :
    (applyEffects q s effs).1.NoKillTo p := by
  intro src hx
  rcases applyEffects_mem_signals_cases q s effs hx with hx | ⟨q', hq'⟩ | ⟨q', r, hx, hmem⟩
  · exact h src hx
  · cases hq'
  · cases hx
    exact he hmem

/-- `runE` by `q` keeps `p` kill-free if the popped message makes `q` emit
no `signal p .kill`. -/
theorem NoKillTo.runE {beh : EBehavior σ μ} {s s' : Sys σ μ} {q : Pid} (h : runE beh s q = some s')
    {p : Pid} (hk : s.NoKillTo p)
    (hb : ∀ st m rest, s.cfg.get q = some ⟨st, m :: rest⟩ →
      Effect.signal p .kill ∉ (beh q s.next st m).2) : s'.NoKillTo p := by
  obtain ⟨st, m, rest, hget, hs'⟩ := runE_cases h
  simp only at hs'
  have h1 : NoKillTo p { s with cfg := s.cfg.set q ⟨(beh q s.next st m).1, rest⟩ } := hk
  have h2 := h1.applyEffects q (hb st m rest hget)
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact h2
  · exact h2.terminate q (Reason.propagated_ne_kill reason)

theorem NoKillTo.signalE {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s')
    {p : Pid} (hk : s.NoKillTo p) : s'.NoKillTo p := by
  obtain ⟨q, src, r, rest, hsg, hc⟩ := signalE_cases h
  have hpop := hk.of_cons hsg
  rcases hc with ⟨_, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, _, rfl⟩ | ⟨a, _, _, rfl⟩
  · exact hpop
  · exact hpop
  · exact hpop
  · exact hpop.terminate q (by simp)
  · exact hpop.terminate q (by simp)

theorem NoKillTo.downE {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s')
    {p : Pid} (hk : s.NoKillTo p) : s'.NoKillTo p :=
  hk.of_signals_eq (downE_signals h)

theorem NoKillTo.timerE {s s' : Sys σ μ} {i : Nat} (h : timerE s i = some s')
    {p : Pid} (hk : s.NoKillTo p) : s'.NoKillTo p :=
  hk.of_signals_eq (timerE_signals h)

end Sys

/-- `NoKillTo p` is preserved by every step as long as no actor's popped
message makes it `signal p .kill`. -/
theorem SysStep.noKillTo {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysStep beh sig s s') {p : Pid} (hk : s.NoKillTo p)
    (hb : ∀ q st m rest, s.cfg.get q = some ⟨st, m :: rest⟩ →
      Effect.signal p .kill ∉ (beh q s.next st m).2) : s'.NoKillTo p := by
  cases h with
  | run q _ hrun => exact hk.runE hrun (hb q)
  | signal _ hsig => exact hk.signalE hsig
  | down _ hdown => exact hk.downE hdown
  | timer i _ htimer => exact hk.timerE htimer

/-- A behaviour that never emits `signal` at all keeps every pid kill-free. -/
theorem SysReach.noKillTo_of_no_signal {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    (h : SysReach beh sig s s') {p : Pid} (hk : s.NoKillTo p)
    (hb : ∀ q fresh st m q' r, Effect.signal q' r ∉ (beh q fresh st m).2) : s'.NoKillTo p :=
  h.inv (fun hst hk => hst.noKillTo hk (fun q st m _ _ => hb q _ st m p .kill)) hk

/-! ## Timers only grow, except by firing

Every `runE` appends to `timers` (a death keeps them), a signal or DOWN
step leaves them alone; the timer-driven liveness proofs rank a pending
timer by its position in the list. -/

namespace Sys

/-- One effect only appends to `timers`. -/
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

theorem timers_applyEffects_append (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) :
    ∃ new, (applyEffects p s effs).1.timers = s.timers ++ new :=
  timers_foldl_applyEffect_append p effs s none

/-- A `runE` only appends to `timers` (a death keeps them). -/
theorem runE_timers_append {beh : EBehavior σ μ} {s s' : Sys σ μ} {p : Pid}
    (h : runE beh s p = some s') : ∃ new, s'.timers = s.timers ++ new := by
  obtain ⟨st, m, rest, _, hs'⟩ := runE_cases h
  simp only at hs'
  obtain ⟨new, hnew⟩ := timers_applyEffects_append p
    { s with cfg := s.cfg.set p ⟨(beh p s.next st m).1, rest⟩ } (beh p s.next st m).2
  simp only at hnew
  rcases hs' with ⟨_, rfl⟩ | ⟨reason, _, rfl⟩
  · exact ⟨new, hnew⟩
  · exact ⟨new, by rw [terminate_timers, hnew]⟩

/-- A signal step never touches `timers`. -/
theorem signalE_timers {sig : Signals σ μ} {s s' : Sys σ μ} (h : signalE sig s = some s') :
    s'.timers = s.timers := by
  obtain ⟨q, src, r, rest, _, hc⟩ := signalE_cases h
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    <;> rfl

/-- Nor does a DOWN step. -/
theorem downE_timers {sig : Signals σ μ} {s s' : Sys σ μ} (h : downE sig s = some s') :
    s'.timers = s.timers := by
  obtain ⟨w, t, r, rest, _, hc⟩ := downE_cases h
  rcases hc with ⟨_, _, _, rfl⟩ | rfl <;> rfl

end Sys

end Leanactors
