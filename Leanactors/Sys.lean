import Leanactors.Count
/-!
# Leanactors.Sys

Spawn, links and exits, as a layer over `Config`.

* An `EBehavior` returns a list of `Effect`s instead of bare sends. It also
  receives the next fresh pid, so a spawner knows its child's pid (spawns in
  one step take `fresh`, `fresh+1`, ...).
* A `Sys` is a `Config` plus the fresh-pid counter, the link list, and a
  FIFO of pending exit signals.
* Exits propagate **asynchronously**, as on the BEAM: terminating `p` queues
  a signal `(q, p, reason)` for every linked `q`; a separate `signalE` step
  delivers the oldest signal. A `kill` signal (`Process.exit(q, :kill)`)
  terminates its target whether or not it traps, and the target's own
  links and monitors then see `error` (`:killed`). Any other signal: a
  trapping target gets it as a message via the codec `Signals.exitMsg`; a
  non-trapping target ignores `normal` (so a remote `Process.exit(q,
  :normal)` is a no-op, exactly as on the BEAM) and is itself terminated
  by `error`, queueing more signals. No recursion, so every step is a
  plain function.
* Monitors are one-directional and never cascade: terminating `p` queues a
  DOWN notification for every watcher, delivered as a message via
  `Signals.downMsg` by the `downE` step (dropped if no codec is declared).
* Timers are untimed: `sendAfter p m` records a pending delivery and the
  `timerE i` step fires the `i`-th pending timer, in any order. That
  over-approximates real durations, which is sound for safety.
* `Effect.signal q r` is `Process.exit(q, r)`: it queues an exit signal to
  `q` from self, handled exactly like a link-propagated exit (except that
  `kill` is untrappable). `Effect.exit r` is a self-exit: the actor dies
  with `r`, and its links and monitors see `r.propagated` (`kill` becomes
  `error`, the BEAM's `:killed`).
* `lift` embeds a message-only `Behavior`; `runE_lift` shows the old `step`
  is exactly the new one on systems with no links and no signals, so every
  earlier theorem still applies.
-/

namespace Leanactors

/-- Exit reasons. `normal` and `error` are the BEAM's `:normal` and
everything else; `kill` is the untrappable `:kill` of `Process.exit/2`. -/
inductive Reason | normal | error | kill
  deriving Repr, DecidableEq

/-- What links and monitors see when an actor dies with reason `r`: a
death by `kill` is reported as `error` (the BEAM's `:killed`). -/
def Reason.propagated : Reason → Reason
  | .kill => .error
  | r => r

@[simp] theorem Reason.propagated_kill : Reason.kill.propagated = .error := rfl
@[simp] theorem Reason.propagated_normal : Reason.normal.propagated = .normal := rfl
@[simp] theorem Reason.propagated_error : Reason.error.propagated = .error := rfl

theorem Reason.propagated_ne_kill (r : Reason) : r.propagated ≠ .kill := by
  cases r <;> simp [Reason.propagated]

inductive Effect (σ μ : Type)
  | send (to : Pid) (m : μ)
  | spawn (init : σ)
  | spawnLink (init : σ)
  | link (p : Pid)
  | monitor (p : Pid)
  | spawnMonitor (init : σ)
  | sendAfter (to : Pid) (m : μ)
  | signal (q : Pid) (r : Reason)
  | exit (r : Reason)
  deriving Repr

/-- `self → fresh → state → message → (state', effects)`. -/
abbrev EBehavior (σ μ : Type) := Pid → Pid → σ → μ → σ × List (Effect σ μ)

/-- How exit signals become messages, and who traps them
(`Process.flag(:trap_exit, true)` is a property of the actor's state here). -/
structure Signals (σ μ : Type) where
  traps : σ → Bool
  exitMsg : Pid → Reason → μ
  /-- `{:DOWN, ref, :process, pid, reason}`; `none` if the program never monitors. -/
  downMsg : Option (Pid → Reason → μ) := none

structure Sys (σ μ : Type) where
  cfg : Config σ μ
  next : Pid
  links : List (Pid × Pid)
  /-- `(target, source, reason)`, oldest first. -/
  signals : List (Pid × Pid × Reason)
  /-- `(watcher, target)` monitors. -/
  monitors : List (Pid × Pid) := []
  /-- Pending DOWN notifications `(watcher, target, reason)`, oldest first. -/
  downs : List (Pid × Pid × Reason) := []
  /-- Pending timers `(target, message)`; any may fire at any time. -/
  timers : List (Pid × μ) := []

namespace Config

variable {σ μ : Type}

@[simp] theorem get_remove_self (c : Config σ μ) (p : Pid) : (c.remove p).get p = none := by
  simp [get, remove]

theorem get_remove_ne (c : Config σ μ) {p q : Pid} (h : q ≠ p) : (c.remove p).get q = c.get q := by
  simp [get, remove, h]

theorem stateOf_remove (c : Config σ μ) (p q : Pid) :
    (c.remove p).stateOf q = if q = p then none else c.stateOf q := by
  by_cases h : q = p
  · subst h; simp [stateOf]
  · simp [stateOf, get_remove_ne _ h, h]

theorem isSome_remove (c : Config σ μ) (p q : Pid) :
    ((c.remove p).get q).isSome = if q = p then false else (c.get q).isSome := by
  by_cases h : q = p
  · subst h; simp
  · simp [get_remove_ne _ h, h]

theorem mcount_remove [DecidableEq μ] (c : Config σ μ) (p q : Pid) (m : μ) :
    (c.remove p).mcount q m = if q = p then 0 else c.mcount q m := by
  by_cases h : q = p
  · subst h; simp [mcount]
  · simp [mcount, get_remove_ne _ h, h]

end Config

/-- Everyone linked to `p`. -/
def linkedTo (links : List (Pid × Pid)) (p : Pid) : List Pid :=
  links.filterMap fun ab => if ab.1 = p then some ab.2 else if ab.2 = p then some ab.1 else none

/-- Drop every link involving `p`. -/
def unlink (links : List (Pid × Pid)) (p : Pid) : List (Pid × Pid) :=
  links.filter fun ab => ab.1 != p && ab.2 != p

theorem mem_linkedTo_of_mem {links : List (Pid × Pid)} {q p : Pid} (h : (q, p) ∈ links) :
    q ∈ linkedTo links p := by
  unfold linkedTo
  rw [List.mem_filterMap]
  refine ⟨(q, p), h, ?_⟩
  by_cases hq : q = p
  · subst hq; simp
  · simp [hq]

/-- Everyone watching `p`. -/
def watchers (monitors : List (Pid × Pid)) (p : Pid) : List Pid :=
  monitors.filterMap fun wt => if wt.2 = p then some wt.1 else none

/-- Drop every monitor involving `p`. -/
def unmonitor (monitors : List (Pid × Pid)) (p : Pid) : List (Pid × Pid) :=
  monitors.filter fun wt => wt.1 != p && wt.2 != p

theorem mem_watchers_of_mem {monitors : List (Pid × Pid)} {w p : Pid} (h : (w, p) ∈ monitors) :
    w ∈ watchers monitors p := by
  unfold watchers
  rw [List.mem_filterMap]
  exact ⟨(w, p), h, by simp⟩

theorem mem_unmonitor {monitors : List (Pid × Pid)} {a b p : Pid} (h : (a, b) ∈ monitors)
    (ha : a ≠ p) (hb : b ≠ p) : (a, b) ∈ unmonitor monitors p := by
  unfold unmonitor
  rw [List.mem_filter]
  exact ⟨h, by simp [ha, hb]⟩

theorem mem_unlink {links : List (Pid × Pid)} {a b p : Pid} (h : (a, b) ∈ links)
    (ha : a ≠ p) (hb : b ≠ p) : (a, b) ∈ unlink links p := by
  unfold unlink
  rw [List.mem_filter]
  exact ⟨h, by simp [ha, hb]⟩

namespace Sys

variable {σ μ : Type}

/-- Terminate `p`: remove it, drop its links, queue a signal to each linked actor. -/
def terminate (s : Sys σ μ) (p : Pid) (r : Reason) : Sys σ μ :=
  { cfg := s.cfg.remove p
    next := s.next
    links := unlink s.links p
    signals := s.signals ++ (linkedTo s.links p).map fun q => (q, p, r)
    monitors := unmonitor s.monitors p
    downs := s.downs ++ (watchers s.monitors p).map fun w => (w, p, r)
    timers := s.timers }

/-- One effect on behalf of `p`; the `Option Reason` records a pending self-exit. -/
def applyEffect (p : Pid) : Sys σ μ × Option Reason → Effect σ μ → Sys σ μ × Option Reason
  | (s, d), .send to m => ({ s with cfg := s.cfg.deliver to m }, d)
  | (s, d), .spawn init =>
      ({ s with cfg := s.cfg.set s.next ⟨init, []⟩, next := s.next + 1 }, d)
  | (s, d), .spawnLink init =>
      ({ s with cfg := s.cfg.set s.next ⟨init, []⟩, next := s.next + 1,
                links := (p, s.next) :: s.links }, d)
  | (s, d), .link q =>
      if (s.cfg.get q).isSome then ({ s with links := (p, q) :: s.links }, d)
      else ({ s with signals := s.signals ++ [(p, q, .error)] }, d)  -- noproc
  | (s, d), .monitor q =>
      if (s.cfg.get q).isSome then ({ s with monitors := (p, q) :: s.monitors }, d)
      else ({ s with downs := s.downs ++ [(p, q, .error)] }, d)  -- noproc
  | (s, d), .spawnMonitor init =>
      ({ s with cfg := s.cfg.set s.next ⟨init, []⟩, next := s.next + 1,
                monitors := (p, s.next) :: s.monitors }, d)
  | (s, d), .sendAfter to m => ({ s with timers := s.timers ++ [(to, m)] }, d)
  | (s, d), .signal q r => ({ s with signals := s.signals ++ [(q, p, r)] }, d)
  | (s, _), .exit r => (s, some r)

def applyEffects (p : Pid) (s : Sys σ μ) (effs : List (Effect σ μ)) : Sys σ μ × Option Reason :=
  effs.foldl (applyEffect p) (s, none)

/-- Actor `p` handles the head of its mailbox. A self-exit with `reason`
is reported to links and monitors as `reason.propagated`. -/
def runE (beh : EBehavior σ μ) (s : Sys σ μ) (p : Pid) : Option (Sys σ μ) :=
  match s.cfg.get p with
  | some ⟨st, m :: rest⟩ =>
    let out := beh p s.next st m
    let r := applyEffects p { s with cfg := s.cfg.set p ⟨out.1, rest⟩ } out.2
    some (match r.2 with
      | none => r.1
      | some reason => r.1.terminate p reason.propagated)
  | _ => none

/-- Deliver the oldest pending exit signal. `kill` is untrappable and the
killed actor's links see `error`; otherwise a trapping target gets a
message, a non-trapping one ignores `normal` and dies of `error`. -/
def signalE (sig : Signals σ μ) (s : Sys σ μ) : Option (Sys σ μ) :=
  match s.signals with
  | [] => none
  | (q, src, r) :: rest =>
    let s' : Sys σ μ := { s with signals := rest }
    some (match s.cfg.get q with
      | none => s'
      | some a =>
        match r with
        | .kill => s'.terminate q .error
        | .normal => if sig.traps a.state then { s' with cfg := s'.cfg.deliver q (sig.exitMsg src r) } else s'
        | .error =>
          if sig.traps a.state then { s' with cfg := s'.cfg.deliver q (sig.exitMsg src r) }
          else s'.terminate q .error)

/-- Deliver the oldest pending DOWN notification (dropped without a codec
or if the watcher is gone). -/
def downE (sig : Signals σ μ) (s : Sys σ μ) : Option (Sys σ μ) :=
  match s.downs with
  | [] => none
  | (w, t, r) :: rest =>
    let s' : Sys σ μ := { s with downs := rest }
    some (match sig.downMsg, s.cfg.get w with
      | some codec, some _ => { s' with cfg := s'.cfg.deliver w (codec t r) }
      | _, _ => s')

/-- Fire the `i`-th pending timer (dropped if the target is gone). -/
def timerE (s : Sys σ μ) (i : Nat) : Option (Sys σ μ) :=
  match s.timers[i]? with
  | none => none
  | some (to, m) =>
    some { s with cfg := s.cfg.deliver to m, timers := s.timers.eraseIdx i }

end Sys

/-- Relational semantics: any actor with a message may run, or the oldest
signal may be delivered. -/
inductive SysStep {σ μ : Type} (beh : EBehavior σ μ) (sig : Signals σ μ) : Sys σ μ → Sys σ μ → Prop
  | run (s : Sys σ μ) (p : Pid) (s' : Sys σ μ) (h : Sys.runE beh s p = some s') : SysStep beh sig s s'
  | signal (s s' : Sys σ μ) (h : Sys.signalE sig s = some s') : SysStep beh sig s s'
  | down (s s' : Sys σ μ) (h : Sys.downE sig s = some s') : SysStep beh sig s s'
  | timer (s : Sys σ μ) (i : Nat) (s' : Sys σ μ) (h : Sys.timerE s i = some s') : SysStep beh sig s s'

inductive SysReach {σ μ : Type} (beh : EBehavior σ μ) (sig : Signals σ μ) : Sys σ μ → Sys σ μ → Prop
  | refl (s) : SysReach beh sig s s
  | step {a b c} : SysStep beh sig a b → SysReach beh sig b c → SysReach beh sig a c

/-- A scheduler choice for `Sys` (the core's `Choice` is just a pid). -/
inductive SysChoice
  | run (p : Pid)
  | signal
  | down
  | timer (i : Nat)
  deriving Repr, DecidableEq

/-- Executable schedule. Stops at the first choice that is not enabled. -/
def runSys {σ μ : Type} (beh : EBehavior σ μ) (sig : Signals σ μ) :
    Sys σ μ → List SysChoice → Sys σ μ
  | s, [] => s
  | s, .run p :: ch => match Sys.runE beh s p with
    | some s' => runSys beh sig s' ch
    | none => s
  | s, .signal :: ch => match Sys.signalE sig s with
    | some s' => runSys beh sig s' ch
    | none => s
  | s, .down :: ch => match Sys.downE sig s with
    | some s' => runSys beh sig s' ch
    | none => s
  | s, .timer i :: ch => match Sys.timerE s i with
    | some s' => runSys beh sig s' ch
    | none => s

theorem SysReach.inv {σ μ : Type} {beh : EBehavior σ μ} {sig : Signals σ μ} {I : Sys σ μ → Prop}
    (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b)
    {s s' : Sys σ μ} (h : SysReach beh sig s s') (hs : I s) : I s' := by
  induction h with
  | refl => exact hs
  | step hst _ ih => exact ih (hstep hst hs)

theorem runSys_sound {σ μ : Type} (beh : EBehavior σ μ) (sig : Signals σ μ)
    (s : Sys σ μ) (ch : List SysChoice) : SysReach beh sig s (runSys beh sig s ch) := by
  induction ch generalizing s with
  | nil => exact .refl s
  | cons c ch ih =>
    cases c with
    | run p =>
      simp only [runSys]
      cases h : Sys.runE beh s p with
      | none => exact .refl s
      | some s' => exact .step (.run s p s' h) (ih s')
    | signal =>
      simp only [runSys]
      cases h : Sys.signalE sig s with
      | none => exact .refl s
      | some s' => exact .step (.signal s s' h) (ih s')
    | down =>
      simp only [runSys]
      cases h : Sys.downE sig s with
      | none => exact .refl s
      | some s' => exact .step (.down s s' h) (ih s')
    | timer i =>
      simp only [runSys]
      cases h : Sys.timerE s i with
      | none => exact .refl s
      | some s' => exact .step (.timer s i s' h) (ih s')

/-! ## Conservativity: message-only behaviours -/

/-- A `Behavior` as an `EBehavior` that only sends. -/
def lift {σ μ : Type} (beh : Behavior σ μ) : EBehavior σ μ := fun me _ s m =>
  ((beh me s m).1, (beh me s m).2.map fun pm => .send pm.1 pm.2)

theorem Sys.applyEffects_sends {σ μ : Type} (p : Pid) (s : Sys σ μ) (l : List (Pid × μ)) :
    Sys.applyEffects p s (l.map fun pm => Effect.send pm.1 pm.2)
      = ({ s with cfg := s.cfg.deliverAll l }, none) := by
  induction l generalizing s with
  | nil => simp [Sys.applyEffects, Config.deliverAll]
  | cons pm rest ih =>
    obtain ⟨q, m⟩ := pm
    simp only [List.map_cons, Sys.applyEffects, List.foldl_cons, Sys.applyEffect, Config.deliverAll]
    exact ih _

/-- On a system with no links and no signals, the old `step` is the new `runE`. -/
theorem runE_lift {σ μ : Type} (beh : Behavior σ μ) (c : Config σ μ) (n : Pid) (p : Pid) :
    Sys.runE (lift beh) ⟨c, n, [], [], [], [], []⟩ p = (step beh c p).map fun c' => ⟨c', n, [], [], [], [], []⟩ := by
  unfold Sys.runE step
  cases hg : c.get p with
  | none => rfl
  | some a =>
    obtain ⟨st, mb⟩ := a
    cases mb with
    | nil => rfl
    | cons m rest =>
      simp only [lift, Sys.applyEffects_sends, Option.map_some]

end Leanactors
