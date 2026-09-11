import Leanactors.Sys
/-!
# Leanactors.Fair

Fairness and liveness for both layers. Safety theorems in this repository
are stated over `Reach`/`ReachEnv`/`SysReach`, which say nothing about what
*must* happen. This file adds infinite runs, weak fairness, the temporal
combinators `Eventually`/`Always`/`LeadsTo`, and the two workhorse lemmas
liveness proofs are built from: `stable_until` (one fair choice establishes
the goal) and `rank_leads_to` (a `Nat` measure drops at every fair-taken
step). Everything is proved once over an abstract run `ρ : Nat → α` and
instantiated for the `Config` layer (`CRun`), the closed `Sys` layer
(`SysRun`) and the open `Sys` layer (`SysRunE`, system steps plus a
parameter environment relation, mirroring `CRun`'s `env`).
A run is infinite; at each time it takes a labelled step or an idle step
(`ch t = none`, the state repeats), so every finite execution extends to a
run and a theorem over runs is never vacuous. Weak fairness of a choice
says it is disabled infinitely often or taken infinitely often, which
forbids idling (or scheduling others) forever while it is enabled.

API summary (the signatures below are the contract; see the declarations):

Temporal combinators, generic in `{α : Type}`:
* `def Eventually (ρ : Nat → α) (t : Nat) (P : α → Prop) : Prop := ∃ t' ≥ t, P (ρ t')`
* `def Always (ρ : Nat → α) (t : Nat) (P : α → Prop) : Prop := ∀ t' ≥ t, P (ρ t')`
* `def LeadsTo (ρ : Nat → α) (P Q : α → Prop) : Prop := ∀ t, P (ρ t) → Eventually ρ t Q`
* `Eventually.now (h : P (ρ t)) : Eventually ρ t P`
* `Eventually.mono (h : Eventually ρ t P) (hpq : ∀ a, P a → Q a) : Eventually ρ t Q`
* `Eventually.of_le (htt : t ≤ t') (h : Eventually ρ t' P) : Eventually ρ t P`
* `Eventually.bind (h : Eventually ρ t P) (hq : ∀ t' ≥ t, P (ρ t') → Eventually ρ t' Q) : Eventually ρ t Q`
* `Always.at (h : Always ρ t P) (htt : t ≤ t') : P (ρ t')`
* `Always.mono (h : Always ρ t P) (hpq : ∀ a, P a → Q a) : Always ρ t Q`
* `Always.of_le (htt : t ≤ t') (h : Always ρ t P) : Always ρ t' P`
* `Always.and (hp : Always ρ t P) (hq : Always ρ t Q) : Always ρ t (fun a => P a ∧ Q a)`
* `Always.eventually (hp : Always ρ t P) (hq : Eventually ρ t Q) : Eventually ρ t (fun a => P a ∧ Q a)`
* `LeadsTo.refl (ρ : Nat → α) (P : α → Prop) : LeadsTo ρ P P`
* `LeadsTo.of_imp (h : ∀ a, P a → Q a) : LeadsTo ρ P Q`
* `LeadsTo.trans (h₁ : LeadsTo ρ P Q) (h₂ : LeadsTo ρ Q R) : LeadsTo ρ P R`
* `LeadsTo.mono (hp : ∀ a, P' a → P a) (hq : ∀ a, Q a → Q' a) (h : LeadsTo ρ P Q) : LeadsTo ρ P' Q'`
* `LeadsTo.or (h₁ : LeadsTo ρ P R) (h₂ : LeadsTo ρ Q R) : LeadsTo ρ (fun a => P a ∨ Q a) R`
* `LeadsTo.eventually (h : LeadsTo ρ P Q) (he : Eventually ρ t P) : Eventually ρ t Q`
* `LeadsTo.rank_induction (f : α → Nat)
     (h : ∀ n, LeadsTo ρ (fun a => P a ∧ f a = n) (fun a => Q a ∨ (P a ∧ f a < n))) : LeadsTo ρ P Q`

Weak fairness of one choice, abstractly (`en t` : enabled at time `t`,
`tk t` : taken at the step from `t` to `t+1`):
* `def WeakFairOn (en tk : Nat → Prop) : Prop := (∀ t, ∃ t' ≥ t, ¬ en t') ∨ (∀ t, ∃ t' ≥ t, tk t')`
* `WeakFairOn.taken (h : WeakFairOn en tk) (hen : ∀ t' ≥ t, en t') : ∃ t' ≥ t, tk t'`
* `WeakFairOn.of_taken (h : ∀ t, (∀ t' ≥ t, en t') → ∃ t' ≥ t, tk t') : WeakFairOn en tk`
* `WeakFairOn.iff : WeakFairOn en tk ↔ ∀ t, (∀ t' ≥ t, en t') → ∃ t' ≥ t, tk t'`

The two workhorses, generic:
* `stable_until (hfair : WeakFairOn en tk) (hP : P (ρ t))
     (hstable : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
     (hen : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → en u)
     (htaken : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → tk u → Q (ρ (u+1))) : Eventually ρ t Q`
* `stable_until_leadsTo (hfair : WeakFairOn en tk)
     (hstable : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
     (hen : ∀ u, P (ρ u) → ¬ Q (ρ u) → en u)
     (htaken : ∀ u, P (ρ u) → ¬ Q (ρ u) → tk u → Q (ρ (u+1))) : LeadsTo ρ P Q`
* `rank_leads_to (f : α → Nat) (hfair : WeakFairOn en tk)
     (hstable : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
     (hnoinc : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) → f (ρ (u+1)) ≤ f (ρ u))
     (hen : ∀ u, P (ρ u) → ¬ Q (ρ u) → en u)
     (hdec : ∀ u, P (ρ u) → ¬ Q (ρ u) → tk u → P (ρ (u+1)) → f (ρ (u+1)) < f (ρ u)) : LeadsTo ρ P Q`

Config layer (`{σ μ : Type}`, `beh : Behavior σ μ`, `env : Config σ μ → Config σ μ → Prop`;
the lock uses `env := EnvStep`):
* `inductive CChoice | run (p : Pid) | env`
* `inductive CStepL beh env : CChoice → Config σ μ → Config σ μ → Prop` with
  `| run (c) (p) (s) (m) (rest) (h : c.get p = some ⟨s, m :: rest⟩) :
       CStepL beh env (.run p) c ((c.set p ⟨(beh p s m).1, rest⟩).deliverAll (beh p s m).2)`
  `| env (c c') (h : env c c') : CStepL beh env .env c c'`
* `CStepL.toStep (h : CStepL beh env (.run p) a b) : Step beh a b`
* `CStepL.cases (h : CStepL beh env ch a b) : Step beh a b ∨ env a b`
* `Step.exists_cStepL (env) (h : Step beh a b) : ∃ p, CStepL beh env (.run p) a b`
* `inductive ReachE beh env : Config σ μ → Config σ μ → Prop`
  `| refl (c) | step (Step beh a b) (ReachE beh env b c) | env (env a b) (ReachE beh env b c)`
* `ReachE.trans (h₁ : ReachE beh env a b) (h₂ : ReachE beh env b c) : ReachE beh env a c`
* `ReachE.single (h : CStepL beh env ch a b) : ReachE beh env a b`
* `ReachE.inv (hstep : ∀ {a b}, Step beh a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
     (h : ReachE beh env c c') (hc : I c) : I c'`
* `ReachE.elim {R : Config σ μ → Config σ μ → Prop} (hrefl : ∀ c, R c c)
     (hstep : ∀ {a b c}, Step beh a b → R b c → R a c) (henv : ∀ {a b c}, env a b → R b c → R a c)
     (h : ReachE beh env a b) : R a b`
  (so `h.elim ReachEnv.refl ReachEnv.step ReachEnv.env : ReachEnv a b` for the lock)
* `ReachE.toReach (hno : ∀ a b, ¬ env a b) (h : ReachE beh env a b) : Reach beh a b`
* `def CEnabled (c : Config σ μ) : CChoice → Prop`
  (`.run p ↦ ∃ s m rest, c.get p = some ⟨s, m :: rest⟩`, `.env ↦ True`)
* `CEnabled_run_iff (c) (p) : CEnabled c (.run p) ↔ ∃ mb, c.mboxOf p = some mb ∧ mb ≠ []`
* `CEnabled.exists_step (beh) (env) (h : CEnabled c (.run p)) : ∃ c', CStepL beh env (.run p) c c'`
* `CStepL.enabled (h : CStepL beh env (.run p) c c') : CEnabled c (.run p)`
* `inductive CStepI beh env : Option CChoice → Config σ μ → Config σ μ → Prop` with
  `| step (c) (a b) (h : CStepL beh env c a b) : CStepI beh env (some c) a b`
  `| idle (a) : CStepI beh env none a a`
  (a labelled step, or an idle step in which nothing happens: idle steps make
  every finite execution an infinite run, and weak fairness forbids idling
  forever while a choice is enabled)
* `CStepI.of_some (h : CStepI beh env (some c) a b) : CStepL beh env c a b`
* `CStepI.cases (h : CStepI beh env oc a b) : (∃ c, CStepL beh env c a b) ∨ b = a`
* `structure CRun beh env where st : Nat → Config σ μ; ch : Nat → Option CChoice;
     step : ∀ t, CStepI beh env (ch t) (st t) (st (t+1))`
* `def CRun.idle (beh) (env) (c) : CRun beh env` (idles forever in `c`: a run exists from every configuration)
* `CRun.step_at (ρ) (h : ρ.ch t = some c) : CStepL beh env c (ρ.st t) (ρ.st (t+1))`
* `CRun.step_or (ρ) (t) : Step beh (ρ.st t) (ρ.st (t+1)) ∨ env (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t`
* `CRun.reach (ρ) (t) : ReachE beh env (ρ.st 0) (ρ.st t)`
* `CRun.reach_from (ρ) (h : t ≤ t') : ReachE beh env (ρ.st t) (ρ.st t')`
* `CRun.inv (ρ) (hstep : ∀ {a b}, Step beh a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
     (h0 : I (ρ.st 0)) (t) : I (ρ.st t)`
* `def CRun.WeakFair (ρ) (c : CChoice) : Prop :=
     (∀ t, ∃ t' ≥ t, ¬ CEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some c)`
* `CRun.WeakFair.weakFairOn (h : ρ.WeakFair c) : WeakFairOn (fun t => CEnabled (ρ.st t) c) (fun t => ρ.ch t = some c)`
* `CRun.WeakFair.taken (h : ρ.WeakFair c) (hen : ∀ t' ≥ t, CEnabled (ρ.st t') c) : ∃ t' ≥ t, ρ.ch t' = some c`
* `CRun.WeakFair.of_taken (h : ∀ t, (∀ t' ≥ t, CEnabled (ρ.st t') c) → ∃ t' ≥ t, ρ.ch t' = some c) : ρ.WeakFair c`
* `def CRun.EnvFair (ρ) (P : Config σ μ → Prop) (e : Config σ μ → Config σ μ → Prop) : Prop :=
     ∀ t, (∀ t' ≥ t, P (ρ.st t')) → ∃ t' ≥ t, ρ.ch t' = some .env ∧ e (ρ.st t') (ρ.st (t'+1))`
* `CRun.EnvFair.weakFairOn (h : ρ.EnvFair P e) :
     WeakFairOn (fun t => P (ρ.st t)) (fun t => ρ.ch t = some .env ∧ e (ρ.st t) (ρ.st (t+1)))`
* `CRun.stable_until_run (ρ) (p) (hfair : ρ.WeakFair (.run p))
     (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
     (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
     (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → CEnabled a (.run p))
     (htaken : ∀ {a b}, ReachE beh env (ρ.st 0) a → CStepL beh env (.run p) a b → P a → ¬ Q a → Q b) :
     LeadsTo ρ.st P Q`
* `CRun.stable_until_env (ρ) (hfair : ρ.EnvFair P₀ e)
     (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
     (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
     (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
     (htaken : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → Q b) :
     LeadsTo ρ.st P Q`
* `CRun.rank_leads_to_run (ρ) (p) (f : Config σ μ → Nat) (hfair : ρ.WeakFair (.run p))
     (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
     (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
     (hnoinc : ∀ {ch a b}, ReachE beh env (ρ.st 0) a → CStepL beh env ch a b → P a → ¬ Q a → P b → f b ≤ f a)
     (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → CEnabled a (.run p))
     (hdec : ∀ {a b}, ReachE beh env (ρ.st 0) a → CStepL beh env (.run p) a b → P a → ¬ Q a → P b → f b < f a) :
     LeadsTo ρ.st P Q`
* `CRun.rank_leads_to_env (ρ) (f : Config σ μ → Nat) (hfair : ρ.EnvFair P₀ e)
     (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
     (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
     (hnoinc : ∀ {ch a b}, ReachE beh env (ρ.st 0) a → CStepL beh env ch a b → P a → ¬ Q a → P b → f b ≤ f a)
     (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
     (hdec : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → P b → f b < f a) :
     LeadsTo ρ.st P Q`

Sys layer (`beh : EBehavior σ μ`, `sig : Signals σ μ`, choices are `SysChoice`):
* `inductive SysStepL beh sig : SysChoice → Sys σ μ → Sys σ μ → Prop` with
  `| run (s) (p) (s') (h : Sys.runE beh s p = some s') : SysStepL beh sig (.run p) s s'`
  `| signal (s s') (h : Sys.signalE sig s = some s') : SysStepL beh sig .signal s s'`
  `| down (s s') (h : Sys.downE sig s = some s') : SysStepL beh sig .down s s'`
  `| timer (s) (i) (s') (h : Sys.timerE s i = some s') : SysStepL beh sig (.timer i) s s'`
* `SysStepL.toSysStep (h : SysStepL beh sig c a b) : SysStep beh sig a b`
* `SysStep.exists_sysStepL (h : SysStep beh sig a b) : ∃ c, SysStepL beh sig c a b`
* `SysReach.trans (h₁ : SysReach beh sig a b) (h₂ : SysReach beh sig b c) : SysReach beh sig a c`
* `SysReach.single (h : SysStep beh sig a b) : SysReach beh sig a b`
* `inductive SysReachEnv beh sig : Sys σ μ → Sys σ μ → Prop` (`refl`, `step (SysStep)`,
  `env (p) (m)` delivering any message to any pid: the systems the environment can produce)
  with `SysReachEnv.inv (hstep) (henv : ∀ {a} p m, I a → I { a with cfg := a.cfg.deliver p m }) (h) (hc)`,
  `SysReachEnv.of_reach`, `SysReachEnv.trans`
* `def SysEnabled (s : Sys σ μ) : SysChoice → Prop`
  (`.run p ↦ ∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩`, `.signal ↦ s.signals ≠ []`,
   `.down ↦ s.downs ≠ []`, `.timer i ↦ i < s.timers.length`)
* `SysEnabled_run_iff (s) (p) : SysEnabled s (.run p) ↔ ∃ mb, s.cfg.mboxOf p = some mb ∧ mb ≠ []`
* `SysEnabled.exists_step (beh) (sig) (h : SysEnabled s c) : ∃ s', SysStepL beh sig c s s'`
* `SysStepL.enabled (h : SysStepL beh sig c s s') : SysEnabled s c`
* `SysEnabled_iff (beh) (sig) (s) (c) : SysEnabled s c ↔ ∃ s', SysStepL beh sig c s s'`
* `inductive SysStepI beh sig : Option SysChoice → Sys σ μ → Sys σ μ → Prop` with
  `| step (c) (a b) (h : SysStepL beh sig c a b) : SysStepI beh sig (some c) a b`
  `| idle (a) : SysStepI beh sig none a a`
  (idle steps matter here: a closed `Sys` with nothing enabled, such as the
  supervisor once its worker is idle, has no infinite run without them)
* `SysStepI.of_some (h : SysStepI beh sig (some c) a b) : SysStepL beh sig c a b`
* `SysStepI.cases (h : SysStepI beh sig oc a b) : SysStep beh sig a b ∨ b = a`
* `structure SysRun beh sig where st : Nat → Sys σ μ; ch : Nat → Option SysChoice;
     step : ∀ t, SysStepI beh sig (ch t) (st t) (st (t+1))`
* `def SysRun.idle (beh) (sig) (s) : SysRun beh sig` (idles forever in `s`)
* `SysRun.step_at (ρ) (h : ρ.ch t = some c) : SysStepL beh sig c (ρ.st t) (ρ.st (t+1))`
* `SysRun.sysStep_or (ρ) (t) : SysStep beh sig (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t`
* `SysRun.reach (ρ) (t) : SysReach beh sig (ρ.st 0) (ρ.st t)`
* `SysRun.reach_from (ρ) (h : t ≤ t') : SysReach beh sig (ρ.st t) (ρ.st t')`
* `SysRun.inv (ρ) (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b) (h0 : I (ρ.st 0)) (t) : I (ρ.st t)`
* `def SysRun.WeakFair (ρ) (c : SysChoice) : Prop :=
     (∀ t, ∃ t' ≥ t, ¬ SysEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some c)`
* `SysRun.WeakFair.weakFairOn (h : ρ.WeakFair c) : WeakFairOn (fun t => SysEnabled (ρ.st t) c) (fun t => ρ.ch t = some c)`
* `SysRun.WeakFair.taken (h : ρ.WeakFair c) (hen : ∀ t' ≥ t, SysEnabled (ρ.st t') c) : ∃ t' ≥ t, ρ.ch t' = some c`
* `SysRun.WeakFair.of_taken (h : ∀ t, (∀ t' ≥ t, SysEnabled (ρ.st t') c) → ∃ t' ≥ t, ρ.ch t' = some c) : ρ.WeakFair c`
* `SysRun.stable_until (ρ) (c) (hfair : ρ.WeakFair c)
     (hstable : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b → P a → ¬ Q a → P b ∨ Q b)
     (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
     (htaken : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig c a b → P a → ¬ Q a → Q b) :
     LeadsTo ρ.st P Q`
* `SysRun.rank_leads_to (ρ) (c) (f : Sys σ μ → Nat) (hfair : ρ.WeakFair c)
     (hstable : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b → P a → ¬ Q a → P b ∨ Q b)
     (hnoinc : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b → P a → ¬ Q a → P b → f b ≤ f a)
     (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
     (hdec : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig c a b → P a → ¬ Q a → P b → f b < f a) :
     LeadsTo ρ.st P Q`

Open Sys layer (`env : Sys σ μ → Sys σ μ → Prop`; the task uses `env := Sys.Deliver`):
* `inductive SysChoiceE | sys (c : SysChoice) | env`
* `inductive SysStepLE beh sig env : SysChoiceE → Sys σ μ → Sys σ μ → Prop` with
  `| sys (c) (a b) (h : SysStepL beh sig c a b) : SysStepLE beh sig env (.sys c) a b`
  `| env (a b) (h : env a b) : SysStepLE beh sig env .env a b`
* `SysStepLE.cases (h : SysStepLE beh sig env ch a b) : SysStep beh sig a b ∨ env a b`
* `SysStepLE.of_sys (h : SysStepLE beh sig env (.sys c) a b) : SysStepL beh sig c a b`
* `SysStepLE.of_env (h : SysStepLE beh sig env .env a b) : env a b`
* `inductive Sys.Deliver : Sys σ μ → Sys σ μ → Prop` with
  `| deliver (s) (p) (m) : Sys.Deliver s { s with cfg := s.cfg.deliver p m }` (the canonical environment)
* `inductive SysReachE beh sig env : Sys σ μ → Sys σ μ → Prop`
  `| refl (s) | step (SysStep beh sig a b) (SysReachE beh sig env b c) | env (env a b) (SysReachE beh sig env b c)`
* `SysReachE.trans`, `SysReachE.single (h : SysStepLE beh sig env ch a b)`, `SysReachE.of_reach (h : SysReach beh sig a b)`
* `SysReachE.inv (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
     (h : SysReachE beh sig env c c') (hc : I c) : I c'`
* `SysReachE.toReachEnv (h : SysReachE beh sig Sys.Deliver a b) : SysReachEnv beh sig a b` and
  `SysReachEnv.toReachE (h : SysReachEnv beh sig a b) : SysReachE beh sig Sys.Deliver a b`
* `def SysEnabledE (s : Sys σ μ) : SysChoiceE → Prop` (`.sys c ↦ SysEnabled s c`, `.env ↦ True`)
* `inductive SysStepIE beh sig env : Option SysChoiceE → Sys σ μ → Sys σ μ → Prop` with
  `| step (c) (a b) (h : SysStepLE beh sig env c a b) : SysStepIE beh sig env (some c) a b`
  `| idle (a) : SysStepIE beh sig env none a a`
* `SysStepIE.of_some`, `SysStepIE.cases (h : SysStepIE beh sig env oc a b) : (∃ c, SysStepLE beh sig env c a b) ∨ b = a`
* `structure SysRunE beh sig env where st : Nat → Sys σ μ; ch : Nat → Option SysChoiceE;
     step : ∀ t, SysStepIE beh sig env (ch t) (st t) (st (t+1))`
* `def SysRunE.idle (beh) (sig) (env) (s) : SysRunE beh sig env` (idles forever in `s`)
* `SysRunE.step_at (ρ) (h : ρ.ch t = some c) : SysStepLE beh sig env c (ρ.st t) (ρ.st (t+1))`
* `SysRunE.step_or (ρ) (t) : SysStep beh sig (ρ.st t) (ρ.st (t+1)) ∨ env (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t`
* `SysRunE.reach (ρ) (t) : SysReachE beh sig env (ρ.st 0) (ρ.st t)`
* `SysRunE.reach_from (ρ) (h : t ≤ t') : SysReachE beh sig env (ρ.st t) (ρ.st t')`
* `SysRunE.inv (ρ) (hstep) (henv) (h0 : I (ρ.st 0)) (t) : I (ρ.st t)`
* `def SysRunE.WeakFair (ρ) (c : SysChoice) : Prop :=
     (∀ t, ∃ t' ≥ t, ¬ SysEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some (.sys c))`
  with `SysRunE.WeakFair.weakFairOn`, `SysRunE.WeakFair.taken`, `SysRunE.WeakFair.of_taken` as for `SysRun`
* `def SysRunE.EnvFair (ρ) (P : Sys σ μ → Prop) (e : Sys σ μ → Sys σ μ → Prop) : Prop :=
     ∀ t, (∀ t' ≥ t, P (ρ.st t')) → ∃ t' ≥ t, ρ.ch t' = some .env ∧ e (ρ.st t') (ρ.st (t'+1))`
  with `SysRunE.EnvFair.weakFairOn`
* `SysRunE.stable_until_sys (ρ) (c) (hfair : ρ.WeakFair c) (hstable) (henv) (hen) (htaken) : LeadsTo ρ.st P Q`,
  `SysRunE.stable_until_env (ρ) (hfair : ρ.EnvFair P₀ e) (hstable) (henv) (hen) (htaken) : LeadsTo ρ.st P Q`,
  `SysRunE.rank_leads_to_sys (ρ) (c) (f) (hfair : ρ.WeakFair c) (hstable) (henv) (hnoinc) (hen) (hdec) : LeadsTo ρ.st P Q`,
  `SysRunE.rank_leads_to_env (ρ) (f) (hfair : ρ.EnvFair P₀ e) (hstable) (henv) (hnoinc) (hen) (hdec) : LeadsTo ρ.st P Q`
  (the `CRun` signatures with `ReachE beh env` replaced by `SysReachE beh sig env`, `Step beh` by
  `SysStep beh sig`, `CStepL beh env` by `SysStepLE beh sig env` / `SysStepL beh sig`, `CEnabled` by `SysEnabled`)
* `def SysRun.toE (ρ : SysRun beh sig) (env) : SysRunE beh sig env` (never takes an `env` step), with
  `SysRun.toE_st : (ρ.toE env).st = ρ.st`, `SysRun.toE_ch_iff`, and
  `SysRun.toE_weakFair (env) (h : ρ.WeakFair c) : (ρ.toE env).WeakFair c`

`FairDemo` at the end is a two-state sanity check of the `Config` API: an
actor that switches from `off` to `on` on any message, an environment that
may deliver a message to any pid; under `WeakFair (.run 0)` and an
`EnvFair` that eventually delivers to pid 0 while it is off, `off` leads to
`on` (`FairDemo.off_leadsTo_on`), by `stable_until_env`, `stable_until_run`
and `LeadsTo.trans`.
-/

namespace Leanactors

/-! ## List facts for rank arguments: erasing an entry that is not the hit

Used by the timer-driven liveness proofs (`WatchdogLive`, `TtlLive`): a
firing timer is an `eraseIdx` on `timers`. -/

/-- Erasing some other entry keeps `y` in the list. -/
theorem List.mem_eraseIdx_of_ne {α : Type} {l : List α} {i : Nat} {x y : α} (hy : y ∈ l)
    (hx : l[i]? = some x) (hne : y ≠ x) : y ∈ l.eraseIdx i := by
  induction l generalizing i with
  | nil => cases hy
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [List.eraseIdx_cons_zero]
      rcases List.mem_cons.mp hy with rfl | h
      · exact absurd rfl hne
      · exact h
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      rw [List.eraseIdx_cons_succ]
      rcases List.mem_cons.mp hy with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h hx)

/-- Erasing an entry that does not satisfy `p` never moves the first hit later. -/
theorem List.findIdx_eraseIdx_le {α : Type} {l : List α} {p : α → Bool} {i : Nat} {x : α}
    (hx : l[i]? = some x) (hpx : p x = false) : (l.eraseIdx i).findIdx p ≤ l.findIdx p := by
  induction l generalizing i with
  | nil => simp at hx
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [List.eraseIdx_cons_zero, List.findIdx_cons, hpx, cond_false]
      exact Nat.le_succ _
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      rw [List.eraseIdx_cons_succ]
      simp only [List.findIdx_cons]
      cases p a with
      | true => exact Nat.le_refl _
      | false => exact Nat.succ_le_succ (ih hx)

/-- Erasing the head when it is not the hit moves the first hit earlier. -/
theorem List.findIdx_eraseIdx_zero {α : Type} {l : List α} {p : α → Bool} {x : α}
    (hx : l[0]? = some x) (hpx : p x = false) : (l.eraseIdx 0).findIdx p < l.findIdx p := by
  cases l with
  | nil => simp at hx
  | cons a rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    rw [List.eraseIdx_cons_zero, List.findIdx_cons, hpx, cond_false]
    exact Nat.lt_succ_self _


/-! ## Temporal combinators over an arbitrary run -/

section Temporal

variable {α : Type}

/-- `P` holds at some time `t' ≥ t`. -/
def Eventually (ρ : Nat → α) (t : Nat) (P : α → Prop) : Prop := ∃ t' ≥ t, P (ρ t')

/-- `P` holds at every time `t' ≥ t`. -/
def Always (ρ : Nat → α) (t : Nat) (P : α → Prop) : Prop := ∀ t' ≥ t, P (ρ t')

/-- Whenever `P` holds, `Q` holds later (or now). -/
def LeadsTo (ρ : Nat → α) (P Q : α → Prop) : Prop := ∀ t, P (ρ t) → Eventually ρ t Q

theorem Eventually.now {ρ : Nat → α} {t : Nat} {P : α → Prop} (h : P (ρ t)) :
    Eventually ρ t P := ⟨t, Nat.le_refl t, h⟩

theorem Eventually.mono {ρ : Nat → α} {t : Nat} {P Q : α → Prop} (h : Eventually ρ t P)
    (hpq : ∀ a, P a → Q a) : Eventually ρ t Q := by
  obtain ⟨t', ht', hp⟩ := h
  exact ⟨t', ht', hpq _ hp⟩

theorem Eventually.of_le {ρ : Nat → α} {t t' : Nat} (htt : t ≤ t') {P : α → Prop}
    (h : Eventually ρ t' P) : Eventually ρ t P := by
  obtain ⟨u, hu, hp⟩ := h
  exact ⟨u, Nat.le_trans htt hu, hp⟩

theorem Eventually.bind {ρ : Nat → α} {t : Nat} {P Q : α → Prop} (h : Eventually ρ t P)
    (hq : ∀ t' ≥ t, P (ρ t') → Eventually ρ t' Q) : Eventually ρ t Q := by
  obtain ⟨t', ht', hp⟩ := h
  exact (hq t' ht' hp).of_le ht'

theorem Always.at {ρ : Nat → α} {t t' : Nat} {P : α → Prop} (h : Always ρ t P) (htt : t ≤ t') :
    P (ρ t') := h t' htt

theorem Always.mono {ρ : Nat → α} {t : Nat} {P Q : α → Prop} (h : Always ρ t P)
    (hpq : ∀ a, P a → Q a) : Always ρ t Q := fun t' ht' => hpq _ (h t' ht')

theorem Always.of_le {ρ : Nat → α} {t t' : Nat} (htt : t ≤ t') {P : α → Prop}
    (h : Always ρ t P) : Always ρ t' P := fun u hu => h u (Nat.le_trans htt hu)

theorem Always.and {ρ : Nat → α} {t : Nat} {P Q : α → Prop} (hp : Always ρ t P)
    (hq : Always ρ t Q) : Always ρ t (fun a => P a ∧ Q a) := fun t' ht' => ⟨hp t' ht', hq t' ht'⟩

theorem Always.eventually {ρ : Nat → α} {t : Nat} {P Q : α → Prop} (hp : Always ρ t P)
    (hq : Eventually ρ t Q) : Eventually ρ t (fun a => P a ∧ Q a) := by
  obtain ⟨t', ht', hq⟩ := hq
  exact ⟨t', ht', hp t' ht', hq⟩

theorem LeadsTo.refl (ρ : Nat → α) (P : α → Prop) : LeadsTo ρ P P :=
  fun _ h => Eventually.now h

theorem LeadsTo.of_imp {ρ : Nat → α} {P Q : α → Prop} (h : ∀ a, P a → Q a) : LeadsTo ρ P Q :=
  fun _ hp => Eventually.now (h _ hp)

theorem LeadsTo.trans {ρ : Nat → α} {P Q R : α → Prop} (h₁ : LeadsTo ρ P Q)
    (h₂ : LeadsTo ρ Q R) : LeadsTo ρ P R :=
  fun t hp => (h₁ t hp).bind fun t' _ hq => h₂ t' hq

theorem LeadsTo.mono {ρ : Nat → α} {P P' Q Q' : α → Prop} (hp : ∀ a, P' a → P a)
    (hq : ∀ a, Q a → Q' a) (h : LeadsTo ρ P Q) : LeadsTo ρ P' Q' :=
  fun t hp' => (h t (hp _ hp')).mono hq

theorem LeadsTo.or {ρ : Nat → α} {P Q R : α → Prop} (h₁ : LeadsTo ρ P R) (h₂ : LeadsTo ρ Q R) :
    LeadsTo ρ (fun a => P a ∨ Q a) R := by
  intro t h
  rcases h with h | h
  · exact h₁ t h
  · exact h₂ t h

theorem LeadsTo.eventually {ρ : Nat → α} {P Q : α → Prop} (h : LeadsTo ρ P Q) {t : Nat}
    (he : Eventually ρ t P) : Eventually ρ t Q :=
  he.bind fun t' _ hp => h t' hp

/-- **Well-founded leads-to.** If from every `P`-state of rank `n` the run
reaches `Q` or a `P`-state of smaller rank, then `P` leads to `Q`. -/
theorem LeadsTo.rank_induction {ρ : Nat → α} {P Q : α → Prop} (f : α → Nat)
    (h : ∀ n, LeadsTo ρ (fun a => P a ∧ f a = n) (fun a => Q a ∨ (P a ∧ f a < n))) :
    LeadsTo ρ P Q := by
  have key : ∀ n, ∀ m ≤ n, ∀ t, P (ρ t) → f (ρ t) = m → Eventually ρ t Q := by
    intro n
    induction n with
    | zero =>
      intro m hm t hp hf
      obtain ⟨t', ht', hq⟩ := h m t ⟨hp, hf⟩
      rcases hq with hq | ⟨_, hlt⟩
      · exact ⟨t', ht', hq⟩
      · exact absurd hlt (by omega)
    | succ n ih =>
      intro m hm t hp hf
      obtain ⟨t', ht', hq⟩ := h m t ⟨hp, hf⟩
      rcases hq with hq | ⟨hp', hlt⟩
      · exact ⟨t', ht', hq⟩
      · exact (ih (f (ρ t')) (by omega) t' hp' rfl).of_le ht'
  intro t hp
  exact key _ _ (Nat.le_refl _) t hp rfl

/-! ## Weak fairness, abstractly -/

/-- Weak fairness of one choice along a run, given `en t` (the choice is
enabled at time `t`) and `tk t` (the step from `t` to `t+1` takes it):
either the choice is disabled infinitely often, or it is taken infinitely
often. Equivalently (`WeakFairOn.iff`): if it is enabled from some time on,
it is eventually taken. -/
def WeakFairOn (en tk : Nat → Prop) : Prop :=
  (∀ t, ∃ t' ≥ t, ¬ en t') ∨ (∀ t, ∃ t' ≥ t, tk t')

theorem WeakFairOn.taken {en tk : Nat → Prop} (h : WeakFairOn en tk) {t : Nat}
    (hen : ∀ t' ≥ t, en t') : ∃ t' ≥ t, tk t' := by
  rcases h with h | h
  · obtain ⟨t', ht', hn⟩ := h t
    exact absurd (hen t' ht') hn
  · exact h t

theorem WeakFairOn.of_taken {en tk : Nat → Prop}
    (h : ∀ t, (∀ t' ≥ t, en t') → ∃ t' ≥ t, tk t') : WeakFairOn en tk := by
  by_cases hc : ∃ t, ∀ t' ≥ t, en t'
  · right
    intro u
    obtain ⟨t, ht⟩ := hc
    obtain ⟨t', ht', htk⟩ := h (max t u) (fun v hv => ht v (Nat.le_trans (Nat.le_max_left t u) hv))
    exact ⟨t', Nat.le_trans (Nat.le_max_right t u) ht', htk⟩
  · left
    intro t
    by_cases h2 : ∃ t' ≥ t, ¬ en t'
    · exact h2
    · exact absurd ⟨t, fun t' ht' => Classical.byContradiction fun hne => h2 ⟨t', ht', hne⟩⟩ hc

theorem WeakFairOn.iff {en tk : Nat → Prop} :
    WeakFairOn en tk ↔ ∀ t, (∀ t' ≥ t, en t') → ∃ t' ≥ t, tk t' :=
  ⟨fun h _ hen => h.taken hen, WeakFairOn.of_taken⟩

/-! ## The workhorses -/

/-- **`stable_until`.** `P` holds at `t`; every step from a `P ∧ ¬Q` state
keeps `P` or establishes `Q`; the choice is enabled in every `P ∧ ¬Q`
state and, taken from one, establishes `Q`. Then `Q` eventually holds. -/
theorem stable_until {ρ : Nat → α} {en tk : Nat → Prop} {P Q : α → Prop}
    (hfair : WeakFairOn en tk) {t : Nat} (hP : P (ρ t))
    (hstable : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
    (hen : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → en u)
    (htaken : ∀ u ≥ t, P (ρ u) → ¬ Q (ρ u) → tk u → Q (ρ (u+1))) :
    Eventually ρ t Q := by
  apply Classical.byContradiction
  intro hno
  have hnq : ∀ u ≥ t, ¬ Q (ρ u) := fun u hu hq => hno ⟨u, hu, hq⟩
  have hp' : ∀ k, P (ρ (t + k)) := by
    intro k
    induction k with
    | zero => exact hP
    | succ k ih =>
      have hk : t + k ≥ t := Nat.le_add_right t k
      rcases hstable (t + k) hk ih (hnq _ hk) with h | h
      · exact h
      · exact absurd h (hnq _ (by omega))
  have hp : ∀ u ≥ t, P (ρ u) := fun u hu => by
    have := hp' (u - t)
    rwa [Nat.add_sub_of_le hu] at this
  obtain ⟨u, hu, htk⟩ := hfair.taken (fun u hu => hen u hu (hp u hu) (hnq u hu))
  exact hnq (u+1) (by omega) (htaken u hu (hp u hu) (hnq u hu) htk)

/-- `stable_until` with time-independent hypotheses, as a `LeadsTo`. -/
theorem stable_until_leadsTo {ρ : Nat → α} {en tk : Nat → Prop} {P Q : α → Prop}
    (hfair : WeakFairOn en tk)
    (hstable : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
    (hen : ∀ u, P (ρ u) → ¬ Q (ρ u) → en u)
    (htaken : ∀ u, P (ρ u) → ¬ Q (ρ u) → tk u → Q (ρ (u+1))) :
    LeadsTo ρ P Q :=
  fun _ hP => stable_until hfair hP (fun u _ => hstable u) (fun u _ => hen u) (fun u _ => htaken u)

/-- **`rank_leads_to`.** A `Nat` measure that never increases while `P ∧ ¬Q`
persists and strictly decreases whenever the fair choice is taken (and `P`
persists) gives `P` leads to `Q`. -/
theorem rank_leads_to {ρ : Nat → α} {en tk : Nat → Prop} {P Q : α → Prop} (f : α → Nat)
    (hfair : WeakFairOn en tk)
    (hstable : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) ∨ Q (ρ (u+1)))
    (hnoinc : ∀ u, P (ρ u) → ¬ Q (ρ u) → P (ρ (u+1)) → f (ρ (u+1)) ≤ f (ρ u))
    (hen : ∀ u, P (ρ u) → ¬ Q (ρ u) → en u)
    (hdec : ∀ u, P (ρ u) → ¬ Q (ρ u) → tk u → P (ρ (u+1)) → f (ρ (u+1)) < f (ρ u)) :
    LeadsTo ρ P Q := by
  apply LeadsTo.rank_induction f
  intro n
  apply stable_until_leadsTo hfair
  · intro u ⟨hp, hf⟩ hnq
    have hq : ¬ Q (ρ u) := fun h => hnq (Or.inl h)
    rcases hstable u hp hq with hp' | hq'
    · have hle := hnoinc u hp hq hp'
      by_cases heq : f (ρ (u+1)) = n
      · exact Or.inl ⟨hp', heq⟩
      · exact Or.inr (Or.inr ⟨hp', by omega⟩)
    · exact Or.inr (Or.inl hq')
  · intro u ⟨hp, _⟩ hnq
    exact hen u hp (fun h => hnq (Or.inl h))
  · intro u ⟨hp, hf⟩ hnq htk
    have hq : ¬ Q (ρ u) := fun h => hnq (Or.inl h)
    rcases hstable u hp hq with hp' | hq'
    · exact Or.inr ⟨hp', by have := hdec u hp hq htk hp'; omega⟩
    · exact Or.inl hq'

end Temporal

/-! ## Config layer -/

variable {σ μ : Type}

/-- A scheduler choice in a `Config`-layer run: run actor `p`, or let the
environment act. -/
inductive CChoice
  | run (p : Pid)
  | env
  deriving Repr, DecidableEq

/-- Labelled step: `Step beh` via pid `p` (the constructor mirrors
`Step.run`), or one environment step of the parameter relation `env`. -/
inductive CStepL (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop) :
    CChoice → Config σ μ → Config σ μ → Prop
  | run (c : Config σ μ) (p : Pid) (s : σ) (m : μ) (rest : List μ)
      (h : c.get p = some ⟨s, m :: rest⟩) :
      CStepL beh env (.run p) c ((c.set p ⟨(beh p s m).1, rest⟩).deliverAll (beh p s m).2)
  | env (c c' : Config σ μ) (h : env c c') : CStepL beh env .env c c'

theorem CStepL.toStep {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop} {p : Pid}
    {a b : Config σ μ} (h : CStepL beh env (.run p) a b) : Step beh a b := by
  cases h with
  | run _ _ s m rest hget => exact .run _ p s m rest hget

theorem CStepL.cases {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop} {ch : CChoice}
    {a b : Config σ μ} (h : CStepL beh env ch a b) : Step beh a b ∨ env a b := by
  cases h with
  | run _ p s m rest hget => exact Or.inl (.run _ p s m rest hget)
  | env _ _ he => exact Or.inr he

theorem Step.exists_cStepL {beh : Behavior σ μ} (env : Config σ μ → Config σ μ → Prop)
    {a b : Config σ μ} (h : Step beh a b) : ∃ p, CStepL beh env (.run p) a b := by
  cases h with
  | run p s m rest hget => exact ⟨p, .run _ p s m rest hget⟩

/-- Reachability by actor steps and environment steps; `LockProof`'s
`ReachEnv` is `ReachE beh EnvStep` (see `ReachE.elim`). -/
inductive ReachE (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop) :
    Config σ μ → Config σ μ → Prop
  | refl (c) : ReachE beh env c c
  | step {a b c} : Step beh a b → ReachE beh env b c → ReachE beh env a c
  | env {a b c} : env a b → ReachE beh env b c → ReachE beh env a c

namespace ReachE

variable {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop}

theorem trans {a b c : Config σ μ} (h₁ : ReachE beh env a b) (h₂ : ReachE beh env b c) :
    ReachE beh env a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)
  | env he _ ih => exact .env he (ih h₂)

theorem single {ch : CChoice} {a b : Config σ μ} (h : CStepL beh env ch a b) :
    ReachE beh env a b := by
  rcases h.cases with hs | he
  · exact .step hs (.refl b)
  · exact .env he (.refl b)

theorem inv {I : Config σ μ → Prop}
    (hstep : ∀ {a b}, Step beh a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
    {c c' : Config σ μ} (h : ReachE beh env c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hstep hs hc)
  | env he _ ih => exact ih (henv he hc)

/-- Map into any relation closed under the same three rules; for the lock
`h.elim ReachEnv.refl ReachEnv.step ReachEnv.env`. -/
theorem elim {R : Config σ μ → Config σ μ → Prop} (hrefl : ∀ c, R c c)
    (hstep : ∀ {a b c}, Step beh a b → R b c → R a c)
    (henv : ∀ {a b c}, env a b → R b c → R a c)
    {a b : Config σ μ} (h : ReachE beh env a b) : R a b := by
  induction h with
  | refl c => exact hrefl c
  | step hs _ ih => exact hstep hs ih
  | env he _ ih => exact henv he ih

theorem toReach (hno : ∀ a b, ¬ env a b) {a b : Config σ μ} (h : ReachE beh env a b) :
    Reach beh a b :=
  h.elim Reach.refl (fun hs hr => Reach.step hs hr) (fun he _ => absurd he (hno _ _))

end ReachE

/-- Which choices can move: `run p` iff `p` has a message; `env` always
(environment fairness is a separate assumption, `CRun.EnvFair`). -/
def CEnabled (c : Config σ μ) : CChoice → Prop
  | .run p => ∃ s m rest, c.get p = some ⟨s, m :: rest⟩
  | .env => True

theorem CEnabled_run_iff (c : Config σ μ) (p : Pid) :
    CEnabled c (.run p) ↔ ∃ mb, c.mboxOf p = some mb ∧ mb ≠ [] := by
  constructor
  · rintro ⟨s, m, rest, h⟩
    exact ⟨m :: rest, by simp [Config.mboxOf, h], List.cons_ne_nil m rest⟩
  · rintro ⟨mb, hmb, hne⟩
    unfold Config.mboxOf at hmb
    cases hget : c.get p with
    | none => rw [hget] at hmb; cases hmb
    | some a =>
      rw [hget] at hmb
      simp at hmb
      subst hmb
      cases hml : a.mailbox with
      | nil => exact absurd hml hne
      | cons m rest => exact ⟨a.state, m, rest, by rw [hget]; cases a; simp_all⟩

theorem CEnabled.exists_step (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop)
    {c : Config σ μ} {p : Pid} (h : CEnabled c (.run p)) :
    ∃ c', CStepL beh env (.run p) c c' := by
  obtain ⟨s, m, rest, hget⟩ := h
  exact ⟨_, .run c p s m rest hget⟩

theorem CStepL.enabled {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop}
    {c c' : Config σ μ} {p : Pid} (h : CStepL beh env (.run p) c c') : CEnabled c (.run p) := by
  cases h with
  | run _ _ s m rest hget => exact ⟨s, m, rest, hget⟩

/-- One step of a `Config`-layer run: a labelled step, or an idle step in
which nothing happens. Idle steps make every finite execution an infinite
run (so theorems over runs are never vacuous); weak fairness forbids
idling forever while a choice is enabled. -/
inductive CStepI (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop) :
    Option CChoice → Config σ μ → Config σ μ → Prop
  | step (c : CChoice) (a b : Config σ μ) (h : CStepL beh env c a b) :
      CStepI beh env (some c) a b
  | idle (a : Config σ μ) : CStepI beh env none a a

theorem CStepI.of_some {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop}
    {c : CChoice} {a b : Config σ μ} (h : CStepI beh env (some c) a b) :
    CStepL beh env c a b := by
  cases h with
  | step _ _ _ h => exact h

theorem CStepI.cases {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop}
    {oc : Option CChoice} {a b : Config σ μ} (h : CStepI beh env oc a b) :
    (∃ c, CStepL beh env c a b) ∨ b = a := by
  cases h with
  | step c _ _ h => exact Or.inl ⟨c, h⟩
  | idle _ => exact Or.inr rfl

/-- An infinite `Config`-layer run: states, the choice taken at each time
(`none` for an idle step), and the proof that consecutive states are
related by that choice. -/
structure CRun (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop) where
  st : Nat → Config σ μ
  ch : Nat → Option CChoice
  step : ∀ t, CStepI beh env (ch t) (st t) (st (t+1))

namespace CRun

variable {beh : Behavior σ μ} {env : Config σ μ → Config σ μ → Prop}

/-- The run that idles forever in `c`: a run exists from every
configuration (it is weakly fair only for choices disabled in `c`). -/
def idle (beh : Behavior σ μ) (env : Config σ μ → Config σ μ → Prop) (c : Config σ μ) :
    CRun beh env := ⟨fun _ => c, fun _ => none, fun _ => .idle c⟩

theorem step_at (ρ : CRun beh env) {t : Nat} {c : CChoice} (h : ρ.ch t = some c) :
    CStepL beh env c (ρ.st t) (ρ.st (t+1)) := by
  have hs := ρ.step t
  rw [h] at hs
  exact hs.of_some

theorem step_or (ρ : CRun beh env) (t : Nat) :
    Step beh (ρ.st t) (ρ.st (t+1)) ∨ env (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t := by
  rcases (ρ.step t).cases with ⟨_, hs⟩ | heq
  · rcases hs.cases with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr heq)

theorem reach (ρ : CRun beh env) (t : Nat) : ReachE beh env (ρ.st 0) (ρ.st t) := by
  induction t with
  | zero => exact .refl _
  | succ t ih =>
    rcases (ρ.step t).cases with ⟨_, hs⟩ | heq
    · exact ih.trans (.single hs)
    · rw [heq]; exact ih

theorem reach_from (ρ : CRun beh env) {t t' : Nat} (h : t ≤ t') :
    ReachE beh env (ρ.st t) (ρ.st t') := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.le_zero.mp h
    subst this; exact .refl _
  | succ t' ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · rcases (ρ.step t').cases with ⟨_, hs⟩ | heq'
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (.single hs)
      · rw [heq']; exact ih (Nat.le_of_lt_succ hlt)
    · subst heq; exact .refl _

theorem inv (ρ : CRun beh env) {I : Config σ μ → Prop}
    (hstep : ∀ {a b}, Step beh a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
    (h0 : I (ρ.st 0)) (t : Nat) : I (ρ.st t) :=
  (ρ.reach t).inv hstep henv h0

/-- Weak fairness of choice `c`: disabled infinitely often, or taken
infinitely often. -/
def WeakFair (ρ : CRun beh env) (c : CChoice) : Prop :=
  (∀ t, ∃ t' ≥ t, ¬ CEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some c)

theorem WeakFair.weakFairOn {ρ : CRun beh env} {c : CChoice} (h : ρ.WeakFair c) :
    WeakFairOn (fun t => CEnabled (ρ.st t) c) (fun t => ρ.ch t = some c) := h

theorem WeakFair.taken {ρ : CRun beh env} {c : CChoice} (h : ρ.WeakFair c) {t : Nat}
    (hen : ∀ t' ≥ t, CEnabled (ρ.st t') c) : ∃ t' ≥ t, ρ.ch t' = some c :=
  h.weakFairOn.taken hen

theorem WeakFair.of_taken {ρ : CRun beh env} {c : CChoice}
    (h : ∀ t, (∀ t' ≥ t, CEnabled (ρ.st t') c) → ∃ t' ≥ t, ρ.ch t' = some c) : ρ.WeakFair c :=
  WeakFairOn.of_taken h

/-- Environment fairness: if `P` holds from `t` on, an environment step
satisfying `e` happens at some `t' ≥ t`. -/
def EnvFair (ρ : CRun beh env) (P : Config σ μ → Prop)
    (e : Config σ μ → Config σ μ → Prop) : Prop :=
  ∀ t, (∀ t' ≥ t, P (ρ.st t')) → ∃ t' ≥ t, ρ.ch t' = some .env ∧ e (ρ.st t') (ρ.st (t'+1))

theorem EnvFair.weakFairOn {ρ : CRun beh env} {P : Config σ μ → Prop}
    {e : Config σ μ → Config σ μ → Prop} (h : ρ.EnvFair P e) :
    WeakFairOn (fun t => P (ρ.st t)) (fun t => ρ.ch t = some .env ∧ e (ρ.st t) (ρ.st (t+1))) :=
  WeakFairOn.of_taken h

/-- `stable_until` for a fair actor `p`, with state-level hypotheses that
need only hold on configurations reachable from `ρ.st 0`. -/
theorem stable_until_run (ρ : CRun beh env) (p : Pid) (hfair : ρ.WeakFair (.run p))
    {P Q : Config σ μ → Prop}
    (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → CEnabled a (.run p))
    (htaken : ∀ {a b}, ReachE beh env (ρ.st 0) a → CStepL beh env (.run p) a b →
      P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk
    exact htaken (ρ.reach u) (ρ.step_at htk) hp hq

/-- `stable_until` for a fair environment (`ρ.EnvFair P₀ e`): the goal is
established by any `e`-step, and `P₀` holds in every `P ∧ ¬Q` state. -/
theorem stable_until_env (ρ : CRun beh env) {P₀ : Config σ μ → Prop}
    {e : Config σ μ → Config σ μ → Prop} (hfair : ρ.EnvFair P₀ e)
    {P Q : Config σ μ → Prop}
    (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
    (htaken : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq ⟨hch, he⟩
    have hstep := ρ.step_at hch
    cases hstep with
    | env _ _ henv' => exact htaken (ρ.reach u) henv' he hp hq

/-- `rank_leads_to` for a fair actor `p`. -/
theorem rank_leads_to_run (ρ : CRun beh env) (p : Pid) (f : Config σ μ → Nat)
    (hfair : ρ.WeakFair (.run p)) {P Q : Config σ μ → Prop}
    (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hnoinc : ∀ {ch a b}, ReachE beh env (ρ.st 0) a → CStepL beh env ch a b →
      P a → ¬ Q a → P b → f b ≤ f a)
    (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → CEnabled a (.run p))
    (hdec : ∀ {a b}, ReachE beh env (ρ.st 0) a → CStepL beh env (.run p) a b →
      P a → ¬ Q a → P b → f b < f a) :
    LeadsTo ρ.st P Q := by
  apply rank_leads_to f hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq hp'
    rcases (ρ.step u).cases with ⟨_, hs⟩ | heq
    · exact hnoinc (ρ.reach u) hs hp hq hp'
    · rw [heq]; exact Nat.le_refl _
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk hp'
    exact hdec (ρ.reach u) (ρ.step_at htk) hp hq hp'

/-- `rank_leads_to` for a fair environment. -/
theorem rank_leads_to_env (ρ : CRun beh env) (f : Config σ μ → Nat) {P₀ : Config σ μ → Prop}
    {e : Config σ μ → Config σ μ → Prop} (hfair : ρ.EnvFair P₀ e) {P Q : Config σ μ → Prop}
    (hstable : ∀ {a b}, ReachE beh env (ρ.st 0) a → Step beh a b → P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hnoinc : ∀ {ch a b}, ReachE beh env (ρ.st 0) a → CStepL beh env ch a b →
      P a → ¬ Q a → P b → f b ≤ f a)
    (hen : ∀ {a}, ReachE beh env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
    (hdec : ∀ {a b}, ReachE beh env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → P b → f b < f a) :
    LeadsTo ρ.st P Q := by
  apply rank_leads_to f hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq hp'
    rcases (ρ.step u).cases with ⟨_, hs⟩ | heq
    · exact hnoinc (ρ.reach u) hs hp hq hp'
    · rw [heq]; exact Nat.le_refl _
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq ⟨hch, he⟩ hp'
    have hstep := ρ.step_at hch
    cases hstep with
    | env _ _ henv' => exact hdec (ρ.reach u) henv' he hp hq hp'

end CRun

/-! ## Sys layer -/

/-- `SysStep` labelled by the `SysChoice` that was taken. -/
inductive SysStepL (beh : EBehavior σ μ) (sig : Signals σ μ) :
    SysChoice → Sys σ μ → Sys σ μ → Prop
  | run (s : Sys σ μ) (p : Pid) (s' : Sys σ μ) (h : Sys.runE beh s p = some s') :
      SysStepL beh sig (.run p) s s'
  | signal (s s' : Sys σ μ) (h : Sys.signalE sig s = some s') : SysStepL beh sig .signal s s'
  | down (s s' : Sys σ μ) (h : Sys.downE sig s = some s') : SysStepL beh sig .down s s'
  | timer (s : Sys σ μ) (i : Nat) (s' : Sys σ μ) (h : Sys.timerE s i = some s') :
      SysStepL beh sig (.timer i) s s'

theorem SysStepL.toSysStep {beh : EBehavior σ μ} {sig : Signals σ μ} {c : SysChoice}
    {a b : Sys σ μ} (h : SysStepL beh sig c a b) : SysStep beh sig a b := by
  cases h with
  | run _ p _ h => exact .run _ p _ h
  | signal _ _ h => exact .signal _ _ h
  | down _ _ h => exact .down _ _ h
  | timer _ i _ h => exact .timer _ i _ h

theorem SysStep.exists_sysStepL {beh : EBehavior σ μ} {sig : Signals σ μ} {a b : Sys σ μ}
    (h : SysStep beh sig a b) : ∃ c, SysStepL beh sig c a b := by
  cases h with
  | run p _ h => exact ⟨.run p, .run _ p _ h⟩
  | signal _ h => exact ⟨.signal, .signal _ _ h⟩
  | down _ h => exact ⟨.down, .down _ _ h⟩
  | timer i _ h => exact ⟨.timer i, .timer _ i _ h⟩

theorem SysReach.trans {beh : EBehavior σ μ} {sig : Signals σ μ} {a b c : Sys σ μ}
    (h₁ : SysReach beh sig a b) (h₂ : SysReach beh sig b c) : SysReach beh sig a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem SysReach.single {beh : EBehavior σ μ} {sig : Signals σ μ} {a b : Sys σ μ}
    (h : SysStep beh sig a b) : SysReach beh sig a b := .step h (.refl b)

/-- Reachability by system steps and environment deliveries: any message
to any pid at any time (a delivery to a dead pid is the identity). The
`Sys` safety proofs are over the closed `SysReach`; this is the set of
systems the environment can drive a closed system to, the `Sys` analogue
of `ReachE`. -/
inductive SysReachEnv (beh : EBehavior σ μ) (sig : Signals σ μ) : Sys σ μ → Sys σ μ → Prop
  | refl (s : Sys σ μ) : SysReachEnv beh sig s s
  | step {a b c : Sys σ μ} (h : SysStep beh sig a b) (h' : SysReachEnv beh sig b c) :
      SysReachEnv beh sig a c
  | env {a c : Sys σ μ} (p : Pid) (m : μ)
      (h' : SysReachEnv beh sig { a with cfg := a.cfg.deliver p m } c) : SysReachEnv beh sig a c

namespace SysReachEnv

variable {beh : EBehavior σ μ} {sig : Signals σ μ}

theorem inv {I : Sys σ μ → Prop} (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b)
    (henv : ∀ {a} (p : Pid) (m : μ), I a → I { a with cfg := a.cfg.deliver p m })
    {c c' : Sys σ μ} (h : SysReachEnv beh sig c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hstep hs hc)
  | env p m _ ih => exact ih (henv p m hc)

theorem of_reach {a b : Sys σ μ} (h : SysReach beh sig a b) : SysReachEnv beh sig a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

theorem trans {a b c : Sys σ μ} (h₁ : SysReachEnv beh sig a b) (h₂ : SysReachEnv beh sig b c) :
    SysReachEnv beh sig a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)
  | env p m _ ih => exact .env p m (ih h₂)

end SysReachEnv

/-- Which choices can move: `run p` iff `p` has a message, `signal` iff a
signal is pending, `down` iff a DOWN is pending, `timer i` iff timer `i`
exists. Exactly the domain of `SysStepL` (`SysEnabled_iff`). -/
def SysEnabled (s : Sys σ μ) : SysChoice → Prop
  | .run p => ∃ st m rest, s.cfg.get p = some ⟨st, m :: rest⟩
  | .signal => s.signals ≠ []
  | .down => s.downs ≠ []
  | .timer i => i < s.timers.length

theorem SysEnabled_run_iff (s : Sys σ μ) (p : Pid) :
    SysEnabled s (.run p) ↔ ∃ mb, s.cfg.mboxOf p = some mb ∧ mb ≠ [] :=
  CEnabled_run_iff s.cfg p

theorem SysEnabled.exists_step (beh : EBehavior σ μ) (sig : Signals σ μ) {s : Sys σ μ}
    {c : SysChoice} (h : SysEnabled s c) : ∃ s', SysStepL beh sig c s s' := by
  cases c with
  | run p =>
    obtain ⟨st, m, rest, hget⟩ := h
    cases hr : Sys.runE beh s p with
    | none => simp [Sys.runE, hget] at hr
    | some s' => exact ⟨s', .run s p s' hr⟩
  | signal =>
    cases hs : s.signals with
    | nil => exact absurd hs h
    | cons x rest =>
      obtain ⟨q, src, r⟩ := x
      cases hr : Sys.signalE sig s with
      | none => simp [Sys.signalE, hs] at hr
      | some s' => exact ⟨s', .signal s s' hr⟩
  | down =>
    cases hs : s.downs with
    | nil => exact absurd hs h
    | cons x rest =>
      obtain ⟨w, tgt, r⟩ := x
      cases hr : Sys.downE sig s with
      | none => simp [Sys.downE, hs] at hr
      | some s' => exact ⟨s', .down s s' hr⟩
  | timer i =>
    have hget : s.timers[i]? = some s.timers[i] := List.getElem?_eq_getElem h
    cases hr : Sys.timerE s i with
    | none => simp [Sys.timerE, hget] at hr
    | some s' => exact ⟨s', .timer s i s' hr⟩

theorem SysStepL.enabled {beh : EBehavior σ μ} {sig : Signals σ μ} {s s' : Sys σ μ}
    {c : SysChoice} (h : SysStepL beh sig c s s') : SysEnabled s c := by
  cases h with
  | run _ p _ h =>
    unfold Sys.runE at h
    split at h
    · rename_i st m rest hget
      exact ⟨st, m, rest, hget⟩
    · cases h
  | signal _ _ h =>
    unfold Sys.signalE at h
    split at h
    · cases h
    · rename_i x rest hs
      simp only [SysEnabled, hs]
      exact List.cons_ne_nil _ _
  | down _ _ h =>
    unfold Sys.downE at h
    split at h
    · cases h
    · rename_i x rest hs
      simp only [SysEnabled, hs]
      exact List.cons_ne_nil _ _
  | timer _ i _ h =>
    unfold Sys.timerE at h
    split at h
    · cases h
    · rename_i x hget
      simp only [SysEnabled]
      exact (List.getElem?_eq_some_iff.mp hget).1

theorem SysEnabled_iff (beh : EBehavior σ μ) (sig : Signals σ μ) (s : Sys σ μ) (c : SysChoice) :
    SysEnabled s c ↔ ∃ s', SysStepL beh sig c s s' :=
  ⟨SysEnabled.exists_step beh sig, fun ⟨_, h⟩ => h.enabled⟩

/-- One step of a `Sys`-layer run: a labelled step, or an idle step. Idle
steps matter here: a closed `Sys` in which nothing is enabled (the
supervisor once its worker has nothing to do) has no infinite run without
them, and a theorem over its runs would be vacuous. -/
inductive SysStepI (beh : EBehavior σ μ) (sig : Signals σ μ) :
    Option SysChoice → Sys σ μ → Sys σ μ → Prop
  | step (c : SysChoice) (a b : Sys σ μ) (h : SysStepL beh sig c a b) :
      SysStepI beh sig (some c) a b
  | idle (a : Sys σ μ) : SysStepI beh sig none a a

theorem SysStepI.of_some {beh : EBehavior σ μ} {sig : Signals σ μ} {c : SysChoice}
    {a b : Sys σ μ} (h : SysStepI beh sig (some c) a b) : SysStepL beh sig c a b := by
  cases h with
  | step _ _ _ h => exact h

theorem SysStepI.cases {beh : EBehavior σ μ} {sig : Signals σ μ} {oc : Option SysChoice}
    {a b : Sys σ μ} (h : SysStepI beh sig oc a b) : SysStep beh sig a b ∨ b = a := by
  cases h with
  | step _ _ _ h => exact Or.inl h.toSysStep
  | idle _ => exact Or.inr rfl

/-- An infinite `Sys`-layer run: states, the choice taken at each time
(`none` for an idle step), and the proof that consecutive states are
related by that choice. -/
structure SysRun (beh : EBehavior σ μ) (sig : Signals σ μ) where
  st : Nat → Sys σ μ
  ch : Nat → Option SysChoice
  step : ∀ t, SysStepI beh sig (ch t) (st t) (st (t+1))

namespace SysRun

variable {beh : EBehavior σ μ} {sig : Signals σ μ}

/-- The run that idles forever in `s`: a run exists from every system. -/
def idle (beh : EBehavior σ μ) (sig : Signals σ μ) (s : Sys σ μ) : SysRun beh sig :=
  ⟨fun _ => s, fun _ => none, fun _ => .idle s⟩

theorem step_at (ρ : SysRun beh sig) {t : Nat} {c : SysChoice} (h : ρ.ch t = some c) :
    SysStepL beh sig c (ρ.st t) (ρ.st (t+1)) := by
  have hs := ρ.step t
  rw [h] at hs
  exact hs.of_some

theorem sysStep_or (ρ : SysRun beh sig) (t : Nat) :
    SysStep beh sig (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t := (ρ.step t).cases

theorem reach (ρ : SysRun beh sig) (t : Nat) : SysReach beh sig (ρ.st 0) (ρ.st t) := by
  induction t with
  | zero => exact .refl _
  | succ t ih =>
    rcases ρ.sysStep_or t with hs | heq
    · exact ih.trans (.single hs)
    · rw [heq]; exact ih

theorem reach_from (ρ : SysRun beh sig) {t t' : Nat} (h : t ≤ t') :
    SysReach beh sig (ρ.st t) (ρ.st t') := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.le_zero.mp h
    subst this; exact .refl _
  | succ t' ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · rcases ρ.sysStep_or t' with hs | heq'
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (.single hs)
      · rw [heq']; exact ih (Nat.le_of_lt_succ hlt)
    · subst heq; exact .refl _

theorem inv (ρ : SysRun beh sig) {I : Sys σ μ → Prop}
    (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b) (h0 : I (ρ.st 0)) (t : Nat) :
    I (ρ.st t) :=
  (ρ.reach t).inv hstep h0

/-- Weak fairness of choice `c`: disabled infinitely often, or taken
infinitely often. -/
def WeakFair (ρ : SysRun beh sig) (c : SysChoice) : Prop :=
  (∀ t, ∃ t' ≥ t, ¬ SysEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some c)

theorem WeakFair.weakFairOn {ρ : SysRun beh sig} {c : SysChoice} (h : ρ.WeakFair c) :
    WeakFairOn (fun t => SysEnabled (ρ.st t) c) (fun t => ρ.ch t = some c) := h

theorem WeakFair.taken {ρ : SysRun beh sig} {c : SysChoice} (h : ρ.WeakFair c) {t : Nat}
    (hen : ∀ t' ≥ t, SysEnabled (ρ.st t') c) : ∃ t' ≥ t, ρ.ch t' = some c :=
  h.weakFairOn.taken hen

theorem WeakFair.of_taken {ρ : SysRun beh sig} {c : SysChoice}
    (h : ∀ t, (∀ t' ≥ t, SysEnabled (ρ.st t') c) → ∃ t' ≥ t, ρ.ch t' = some c) : ρ.WeakFair c :=
  WeakFairOn.of_taken h

/-- `stable_until` for a fair choice `c`, with state-level hypotheses that
need only hold on systems reachable from `ρ.st 0`. -/
theorem stable_until (ρ : SysRun beh sig) (c : SysChoice) (hfair : ρ.WeakFair c)
    {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
    (htaken : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig c a b →
      P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.sysStep_or u with hs | heq
    · exact hstable (ρ.reach u) hs hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk
    exact htaken (ρ.reach u) (ρ.step_at htk) hp hq

/-- `rank_leads_to` for a fair choice `c`. -/
theorem rank_leads_to (ρ : SysRun beh sig) (c : SysChoice) (f : Sys σ μ → Nat)
    (hfair : ρ.WeakFair c) {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (hnoinc : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b → f b ≤ f a)
    (hen : ∀ {a}, SysReach beh sig (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
    (hdec : ∀ {a b}, SysReach beh sig (ρ.st 0) a → SysStepL beh sig c a b →
      P a → ¬ Q a → P b → f b < f a) :
    LeadsTo ρ.st P Q := by
  apply Leanactors.rank_leads_to f hfair.weakFairOn
  · intro u hp hq
    rcases ρ.sysStep_or u with hs | heq
    · exact hstable (ρ.reach u) hs hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq hp'
    rcases ρ.sysStep_or u with hs | heq
    · exact hnoinc (ρ.reach u) hs hp hq hp'
    · rw [heq]; exact Nat.le_refl _
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk hp'
    exact hdec (ρ.reach u) (ρ.step_at htk) hp hq hp'

end SysRun

/-! ## Open `Sys` layer: runs with environment steps

A `SysRun` is closed: nothing enters from outside. `SysRunE` is the `Sys`
analogue of `CRun`: at each time a system choice or one step of a
parameter relation `env` (for the examples `Sys.Deliver`, any message to
any pid). The wrappers are the same two workhorses; a `SysRun` embeds as a
`SysRunE` that never takes an environment step (`SysRun.toE`). -/

/-- A scheduler choice in an open `Sys`-layer run: a system choice, or one
step of the environment. -/
inductive SysChoiceE
  | sys (c : SysChoice)
  | env
  deriving Repr, DecidableEq

/-- Labelled step of an open run: a `SysStepL`, or an `env` step. -/
inductive SysStepLE (beh : EBehavior σ μ) (sig : Signals σ μ) (env : Sys σ μ → Sys σ μ → Prop) :
    SysChoiceE → Sys σ μ → Sys σ μ → Prop
  | sys (c : SysChoice) (a b : Sys σ μ) (h : SysStepL beh sig c a b) :
      SysStepLE beh sig env (.sys c) a b
  | env (a b : Sys σ μ) (h : env a b) : SysStepLE beh sig env .env a b

theorem SysStepLE.cases {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}
    {ch : SysChoiceE} {a b : Sys σ μ} (h : SysStepLE beh sig env ch a b) :
    SysStep beh sig a b ∨ env a b := by
  cases h with
  | sys c _ _ h => exact Or.inl h.toSysStep
  | env _ _ h => exact Or.inr h

theorem SysStepLE.of_sys {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}
    {c : SysChoice} {a b : Sys σ μ} (h : SysStepLE beh sig env (.sys c) a b) :
    SysStepL beh sig c a b := by
  cases h with
  | sys _ _ _ h => exact h

theorem SysStepLE.of_env {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}
    {a b : Sys σ μ} (h : SysStepLE beh sig env .env a b) : env a b := by
  cases h with
  | env _ _ h => exact h

/-- The canonical environment of a `Sys`: deliver any message to any pid
(a delivery to a dead pid is the identity). `SysReachE beh sig Deliver` is
`SysReachEnv`. -/
inductive Sys.Deliver : Sys σ μ → Sys σ μ → Prop
  | deliver (s : Sys σ μ) (p : Pid) (m : μ) : Sys.Deliver s { s with cfg := s.cfg.deliver p m }

/-- Reachability by system steps and `env` steps: the `Sys` analogue of
`ReachE`. -/
inductive SysReachE (beh : EBehavior σ μ) (sig : Signals σ μ) (env : Sys σ μ → Sys σ μ → Prop) :
    Sys σ μ → Sys σ μ → Prop
  | refl (s) : SysReachE beh sig env s s
  | step {a b c} : SysStep beh sig a b → SysReachE beh sig env b c → SysReachE beh sig env a c
  | env {a b c} : env a b → SysReachE beh sig env b c → SysReachE beh sig env a c

namespace SysReachE

variable {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}

theorem trans {a b c : Sys σ μ} (h₁ : SysReachE beh sig env a b) (h₂ : SysReachE beh sig env b c) :
    SysReachE beh sig env a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)
  | env he _ ih => exact .env he (ih h₂)

theorem single {ch : SysChoiceE} {a b : Sys σ μ} (h : SysStepLE beh sig env ch a b) :
    SysReachE beh sig env a b := by
  rcases h.cases with hs | he
  · exact .step hs (.refl b)
  · exact .env he (.refl b)

theorem inv {I : Sys σ μ → Prop}
    (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
    {c c' : Sys σ μ} (h : SysReachE beh sig env c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hstep hs hc)
  | env he _ ih => exact ih (henv he hc)

theorem of_reach {a b : Sys σ μ} (h : SysReach beh sig a b) : SysReachE beh sig env a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

/-- With deliveries as the environment this is exactly `SysReachEnv`. -/
theorem toReachEnv {a b : Sys σ μ} (h : SysReachE beh sig Sys.Deliver a b) :
    SysReachEnv beh sig a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih
  | env he _ ih => cases he with | deliver p m => exact .env p m ih

end SysReachE

theorem SysReachEnv.toReachE {beh : EBehavior σ μ} {sig : Signals σ μ} {a b : Sys σ μ}
    (h : SysReachEnv beh sig a b) : SysReachE beh sig Sys.Deliver a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih
  | env p m _ ih => exact .env (.deliver _ p m) ih

/-- Which choices can move: a system choice iff `SysEnabled`; `env` always
(environment fairness is a separate assumption, `SysRunE.EnvFair`). -/
def SysEnabledE (s : Sys σ μ) : SysChoiceE → Prop
  | .sys c => SysEnabled s c
  | .env => True

/-- One step of an open run: a labelled step, or an idle step. -/
inductive SysStepIE (beh : EBehavior σ μ) (sig : Signals σ μ) (env : Sys σ μ → Sys σ μ → Prop) :
    Option SysChoiceE → Sys σ μ → Sys σ μ → Prop
  | step (c : SysChoiceE) (a b : Sys σ μ) (h : SysStepLE beh sig env c a b) :
      SysStepIE beh sig env (some c) a b
  | idle (a : Sys σ μ) : SysStepIE beh sig env none a a

theorem SysStepIE.of_some {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}
    {c : SysChoiceE} {a b : Sys σ μ} (h : SysStepIE beh sig env (some c) a b) :
    SysStepLE beh sig env c a b := by
  cases h with
  | step _ _ _ h => exact h

theorem SysStepIE.cases {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}
    {oc : Option SysChoiceE} {a b : Sys σ μ} (h : SysStepIE beh sig env oc a b) :
    (∃ c, SysStepLE beh sig env c a b) ∨ b = a := by
  cases h with
  | step c _ _ h => exact Or.inl ⟨c, h⟩
  | idle _ => exact Or.inr rfl

/-- An infinite open `Sys`-layer run. -/
structure SysRunE (beh : EBehavior σ μ) (sig : Signals σ μ) (env : Sys σ μ → Sys σ μ → Prop) where
  st : Nat → Sys σ μ
  ch : Nat → Option SysChoiceE
  step : ∀ t, SysStepIE beh sig env (ch t) (st t) (st (t+1))

namespace SysRunE

variable {beh : EBehavior σ μ} {sig : Signals σ μ} {env : Sys σ μ → Sys σ μ → Prop}

/-- The run that idles forever in `s`: a run exists from every system. -/
def idle (beh : EBehavior σ μ) (sig : Signals σ μ) (env : Sys σ μ → Sys σ μ → Prop) (s : Sys σ μ) :
    SysRunE beh sig env := ⟨fun _ => s, fun _ => none, fun _ => .idle s⟩

theorem step_at (ρ : SysRunE beh sig env) {t : Nat} {c : SysChoiceE} (h : ρ.ch t = some c) :
    SysStepLE beh sig env c (ρ.st t) (ρ.st (t+1)) := by
  have hs := ρ.step t
  rw [h] at hs
  exact hs.of_some

theorem step_or (ρ : SysRunE beh sig env) (t : Nat) :
    SysStep beh sig (ρ.st t) (ρ.st (t+1)) ∨ env (ρ.st t) (ρ.st (t+1)) ∨ ρ.st (t+1) = ρ.st t := by
  rcases (ρ.step t).cases with ⟨_, hs⟩ | heq
  · rcases hs.cases with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr heq)

theorem reach (ρ : SysRunE beh sig env) (t : Nat) : SysReachE beh sig env (ρ.st 0) (ρ.st t) := by
  induction t with
  | zero => exact .refl _
  | succ t ih =>
    rcases (ρ.step t).cases with ⟨_, hs⟩ | heq
    · exact ih.trans (.single hs)
    · rw [heq]; exact ih

theorem reach_from (ρ : SysRunE beh sig env) {t t' : Nat} (h : t ≤ t') :
    SysReachE beh sig env (ρ.st t) (ρ.st t') := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.le_zero.mp h
    subst this; exact .refl _
  | succ t' ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · rcases (ρ.step t').cases with ⟨_, hs⟩ | heq'
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (.single hs)
      · rw [heq']; exact ih (Nat.le_of_lt_succ hlt)
    · subst heq; exact .refl _

theorem inv (ρ : SysRunE beh sig env) {I : Sys σ μ → Prop}
    (hstep : ∀ {a b}, SysStep beh sig a b → I a → I b) (henv : ∀ {a b}, env a b → I a → I b)
    (h0 : I (ρ.st 0)) (t : Nat) : I (ρ.st t) :=
  (ρ.reach t).inv hstep henv h0

/-- Weak fairness of the system choice `c`: disabled infinitely often, or
taken infinitely often. -/
def WeakFair (ρ : SysRunE beh sig env) (c : SysChoice) : Prop :=
  (∀ t, ∃ t' ≥ t, ¬ SysEnabled (ρ.st t') c) ∨ (∀ t, ∃ t' ≥ t, ρ.ch t' = some (.sys c))

theorem WeakFair.weakFairOn {ρ : SysRunE beh sig env} {c : SysChoice} (h : ρ.WeakFair c) :
    WeakFairOn (fun t => SysEnabled (ρ.st t) c) (fun t => ρ.ch t = some (.sys c)) := h

theorem WeakFair.taken {ρ : SysRunE beh sig env} {c : SysChoice} (h : ρ.WeakFair c) {t : Nat}
    (hen : ∀ t' ≥ t, SysEnabled (ρ.st t') c) : ∃ t' ≥ t, ρ.ch t' = some (.sys c) :=
  h.weakFairOn.taken hen

theorem WeakFair.of_taken {ρ : SysRunE beh sig env} {c : SysChoice}
    (h : ∀ t, (∀ t' ≥ t, SysEnabled (ρ.st t') c) → ∃ t' ≥ t, ρ.ch t' = some (.sys c)) :
    ρ.WeakFair c :=
  WeakFairOn.of_taken h

/-- Environment fairness: if `P` holds from `t` on, an environment step
satisfying `e` happens at some `t' ≥ t`. -/
def EnvFair (ρ : SysRunE beh sig env) (P : Sys σ μ → Prop) (e : Sys σ μ → Sys σ μ → Prop) : Prop :=
  ∀ t, (∀ t' ≥ t, P (ρ.st t')) → ∃ t' ≥ t, ρ.ch t' = some .env ∧ e (ρ.st t') (ρ.st (t'+1))

theorem EnvFair.weakFairOn {ρ : SysRunE beh sig env} {P : Sys σ μ → Prop}
    {e : Sys σ μ → Sys σ μ → Prop} (h : ρ.EnvFair P e) :
    WeakFairOn (fun t => P (ρ.st t)) (fun t => ρ.ch t = some .env ∧ e (ρ.st t) (ρ.st (t+1))) :=
  WeakFairOn.of_taken h

/-- `stable_until` for a fair system choice `c`. -/
theorem stable_until_sys (ρ : SysRunE beh sig env) (c : SysChoice) (hfair : ρ.WeakFair c)
    {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, SysReachE beh sig env (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
    (htaken : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStepL beh sig c a b →
      P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk
    exact htaken (ρ.reach u) (ρ.step_at htk).of_sys hp hq

/-- `stable_until` for a fair environment (`ρ.EnvFair P₀ e`). -/
theorem stable_until_env (ρ : SysRunE beh sig env) {P₀ : Sys σ μ → Prop}
    {e : Sys σ μ → Sys σ μ → Prop} (hfair : ρ.EnvFair P₀ e) {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hen : ∀ {a}, SysReachE beh sig env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
    (htaken : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → Q b) :
    LeadsTo ρ.st P Q := by
  apply stable_until_leadsTo hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq ⟨hch, he⟩
    exact htaken (ρ.reach u) (ρ.step_at hch).of_env he hp hq

/-- `rank_leads_to` for a fair system choice `c`. -/
theorem rank_leads_to_sys (ρ : SysRunE beh sig env) (c : SysChoice) (f : Sys σ μ → Nat)
    (hfair : ρ.WeakFair c) {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hnoinc : ∀ {ch a b}, SysReachE beh sig env (ρ.st 0) a → SysStepLE beh sig env ch a b →
      P a → ¬ Q a → P b → f b ≤ f a)
    (hen : ∀ {a}, SysReachE beh sig env (ρ.st 0) a → P a → ¬ Q a → SysEnabled a c)
    (hdec : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStepL beh sig c a b →
      P a → ¬ Q a → P b → f b < f a) :
    LeadsTo ρ.st P Q := by
  apply Leanactors.rank_leads_to f hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq hp'
    rcases (ρ.step u).cases with ⟨_, hs⟩ | heq
    · exact hnoinc (ρ.reach u) hs hp hq hp'
    · rw [heq]; exact Nat.le_refl _
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq htk hp'
    exact hdec (ρ.reach u) (ρ.step_at htk).of_sys hp hq hp'

/-- `rank_leads_to` for a fair environment. -/
theorem rank_leads_to_env (ρ : SysRunE beh sig env) (f : Sys σ μ → Nat) {P₀ : Sys σ μ → Prop}
    {e : Sys σ μ → Sys σ μ → Prop} (hfair : ρ.EnvFair P₀ e) {P Q : Sys σ μ → Prop}
    (hstable : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → SysStep beh sig a b →
      P a → ¬ Q a → P b ∨ Q b)
    (henv : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → P a → ¬ Q a → P b ∨ Q b)
    (hnoinc : ∀ {ch a b}, SysReachE beh sig env (ρ.st 0) a → SysStepLE beh sig env ch a b →
      P a → ¬ Q a → P b → f b ≤ f a)
    (hen : ∀ {a}, SysReachE beh sig env (ρ.st 0) a → P a → ¬ Q a → P₀ a)
    (hdec : ∀ {a b}, SysReachE beh sig env (ρ.st 0) a → env a b → e a b → P a → ¬ Q a → P b →
      f b < f a) :
    LeadsTo ρ.st P Q := by
  apply Leanactors.rank_leads_to f hfair.weakFairOn
  · intro u hp hq
    rcases ρ.step_or u with hs | he | heq
    · exact hstable (ρ.reach u) hs hp hq
    · exact henv (ρ.reach u) he hp hq
    · rw [heq]; exact Or.inl hp
  · intro u hp hq hp'
    rcases (ρ.step u).cases with ⟨_, hs⟩ | heq
    · exact hnoinc (ρ.reach u) hs hp hq hp'
    · rw [heq]; exact Nat.le_refl _
  · intro u hp hq
    exact hen (ρ.reach u) hp hq
  · intro u hp hq ⟨hch, he⟩ hp'
    exact hdec (ρ.reach u) (ρ.step_at hch).of_env he hp hq hp'

end SysRunE

/-! ### A closed run is an open run with no environment steps -/

namespace SysRun

variable {beh : EBehavior σ μ} {sig : Signals σ μ}

/-- Embed a closed run as an open one that never takes an `env` step. -/
def toE (ρ : SysRun beh sig) (env : Sys σ μ → Sys σ μ → Prop) : SysRunE beh sig env where
  st := ρ.st
  ch := fun t => (ρ.ch t).map .sys
  step := fun t => by
    have hs := ρ.step t
    revert hs
    generalize ρ.ch t = oc
    generalize ρ.st t = a
    generalize ρ.st (t+1) = b
    intro hs
    cases hs with
    | step c _ _ h => exact .step (.sys c) _ _ (.sys c _ _ h)
    | idle _ => exact .idle _

@[simp] theorem toE_st (ρ : SysRun beh sig) (env : Sys σ μ → Sys σ μ → Prop) :
    (ρ.toE env).st = ρ.st := rfl

theorem toE_ch_iff (ρ : SysRun beh sig) (env : Sys σ μ → Sys σ μ → Prop) (t : Nat)
    (c : SysChoice) : (ρ.toE env).ch t = some (.sys c) ↔ ρ.ch t = some c := by
  show (ρ.ch t).map SysChoiceE.sys = some (.sys c) ↔ _
  cases ρ.ch t with
  | none => simp
  | some c' => simp

/-- Weak fairness transfers along the embedding. -/
theorem toE_weakFair {ρ : SysRun beh sig} (env : Sys σ μ → Sys σ μ → Prop) {c : SysChoice}
    (h : ρ.WeakFair c) : (ρ.toE env).WeakFair c := by
  rcases h with h | h
  · exact Or.inl h
  · right
    intro t
    obtain ⟨t', ht', hc⟩ := h t
    exact ⟨t', ht', (toE_ch_iff ρ env t' c).mpr hc⟩

end SysRun

/-! ## Sanity example: a two-state system -/

namespace FairDemo

inductive Light | off | on
  deriving DecidableEq, Repr

inductive Sig | go
  deriving DecidableEq, Repr

/-- Any message switches the light on; nothing is sent. -/
def beh : Behavior Light Sig := fun _ _ _ => (.on, [])

/-- The environment may deliver `go` to any pid. -/
inductive Env : Config Light Sig → Config Light Sig → Prop
  | go (c : Config Light Sig) (p : Pid) : Env c (c.deliver p .go)

open Config

def Off (c : Config Light Sig) : Prop := c.stateOf 0 = some .off
def On (c : Config Light Sig) : Prop := c.stateOf 0 = some .on
/-- Off, with a message waiting. -/
def Ready (c : Config Light Sig) : Prop := Off c ∧ CEnabled c (.run 0)

theorem Off.get {c : Config Light Sig} (h : Off c) : ∃ x, c.get 0 = some x ∧ x.state = .off := by
  unfold Off stateOf at h
  cases hget : c.get 0 with
  | none => rw [hget] at h; cases h
  | some x => rw [hget] at h; exact ⟨x, rfl, by simpa using h⟩

theorem stateOf_env {a b : Config Light Sig} (h : Env a b) : b.stateOf 0 = a.stateOf 0 := by
  cases h with
  | go p => exact stateOf_deliver _ p 0 Sig.go

theorem mboxOf_set_ne (c : Config Light Sig) {p q : Pid} (a : Actor Light Sig) (h : q ≠ p) :
    (c.set p a).mboxOf q = c.mboxOf q := by
  unfold mboxOf; rw [get_set_ne _ _ h]

theorem get_deliver_self (c : Config Light Sig) {p : Pid} {x : Actor Light Sig}
    (h : c.get p = some x) (m : Sig) :
    (c.deliver p m).get p = some { x with mailbox := x.mailbox ++ [m] } := by
  have h' : c.actors p = some x := h
  simp only [deliver, h', get_set_self]

/-- A step at pid 0 needs a message there and turns the light on; any other
step leaves pid 0's state alone and only appends to its mailbox. -/
theorem step_cases {a b : Config Light Sig} (h : Step beh a b) :
    (CEnabled a (.run 0) ∧ On b) ∨
    (b.stateOf 0 = a.stateOf 0 ∧ ∃ new, b.mboxOf 0 = (a.mboxOf 0).map (· ++ new)) := by
  cases h with
  | run p s m rest hget =>
    by_cases hp : p = 0
    · subst hp
      left
      exact ⟨⟨s, m, rest, hget⟩, by simp [On, stateOf_deliverAll, stateOf_set, beh]⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [stateOf_deliverAll, stateOf_set]
        simp [Ne.symm hp]
      · obtain ⟨new, hnew⟩ := mboxOf_deliverAll (a.set p ⟨(beh p s m).1, rest⟩) (beh p s m).2 0
        exact ⟨new, by rw [hnew, mboxOf_set_ne _ _ (Ne.symm hp)]⟩

/-- Stage 1: while off, a fair environment eventually puts a message in
pid 0's mailbox. -/
theorem off_leadsTo_ready (ρ : CRun beh Env)
    (henv : ρ.EnvFair Off (fun a b => b = a.deliver 0 .go)) :
    LeadsTo ρ.st Off Ready := by
  apply ρ.stable_until_env henv
  · intro a b _ hs hoff hnr
    rcases step_cases hs with ⟨hen, _⟩ | ⟨hst, _⟩
    · exact absurd ⟨hoff, hen⟩ hnr
    · left; unfold Off at *; rwa [hst]
  · intro a b _ he hoff _
    left; unfold Off at *; rwa [stateOf_env he]
  · intro a _ hoff _
    exact hoff
  · intro a b _ _ he hoff _
    subst he
    obtain ⟨x, hget, hx⟩ := hoff.get
    have hget' := get_deliver_self a hget .go
    refine ⟨?_, (CEnabled_run_iff _ _).mpr ⟨x.mailbox ++ [.go], ?_, by simp⟩⟩
    · unfold Off at *; rwa [stateOf_deliver]
    · simp [mboxOf, hget']

/-- Stage 2: with a message waiting, a fair scheduler eventually runs pid 0. -/
theorem ready_leadsTo_on (ρ : CRun beh Env) (hfair : ρ.WeakFair (.run 0)) :
    LeadsTo ρ.st Ready On := by
  apply ρ.stable_until_run 0 hfair
  · intro a b _ hs ⟨hoff, hen⟩ _
    rcases step_cases hs with ⟨_, hon⟩ | ⟨hst, new, hmb⟩
    · exact Or.inr hon
    · left
      refine ⟨by unfold Off at *; rwa [hst], (CEnabled_run_iff _ _).mpr ?_⟩
      obtain ⟨mb, hmb', hne⟩ := (CEnabled_run_iff _ _).mp hen
      refine ⟨mb ++ new, by rw [hmb, hmb']; rfl, ?_⟩
      intro h
      exact hne (List.append_eq_nil_iff.mp h).1
  · intro a b _ he ⟨hoff, hen⟩ _
    left
    refine ⟨by unfold Off at *; rwa [stateOf_env he], ?_⟩
    cases he with
    | go p =>
      obtain ⟨mb, hmb, hne⟩ := (CEnabled_run_iff _ _).mp hen
      obtain ⟨new, hnew⟩ := mboxOf_deliver a p 0 .go
      refine (CEnabled_run_iff _ _).mpr ⟨mb ++ new, by rw [hnew, hmb]; rfl, ?_⟩
      intro h
      exact hne (List.append_eq_nil_iff.mp h).1
  · intro a _ ⟨_, hen⟩ _
    exact hen
  · intro a b _ hs _ _
    cases hs with
    | run _ _ s m rest _ => simp [On, stateOf_deliverAll, stateOf_set, beh]

/-- The sanity theorem: under a fair scheduler for pid 0 and a fair
environment, `off` leads to `on`. -/
theorem off_leadsTo_on (ρ : CRun beh Env) (hfair : ρ.WeakFair (.run 0))
    (henv : ρ.EnvFair Off (fun a b => b = a.deliver 0 .go)) :
    LeadsTo ρ.st Off On :=
  (off_leadsTo_ready ρ henv).trans (ready_leadsTo_on ρ hfair)

end FairDemo

end Leanactors
