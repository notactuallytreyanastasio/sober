import Leanactors.SysProps
import Leanactors.Examples.SupervisorProof
/-!
# Leanactors.Examples.SysPropsDemo

What `Leanactors.SysProps` buys. `SupervisorProof.Inv.step` handles the
`timer` and `down` cases by unfolding `timerE` / `downE`, splitting on the
queue, and feeding six hand-proved facts to `Inv.frame` (about a dozen lines
each). With the library: show once that `Inv` is monotone along `Sys.Grows`
(three lines), then each case is one line. The `down` case no longer needs
to know that this program declares no DOWN codec.
-/

namespace Leanactors.Examples.Supervisor

open Leanactors Config Sys

/-- `Inv` only looks at `next`, states, liveness, links, signals and counts,
all of which are monotone along `Grows`. -/
theorem Inv.grows {a b : Sys St Msg} (hi : Inv a) (h : Grows a b) : Inv b :=
  Inv.frame hi h.next (h.stateOf 0 hi.next_pos) h.alive (fun c => h.links (0, c))
    (fun _ _ hs => Or.inl (h.signals _ hs)) (fun _ _ _ _ => h.mcount 0 _ hi.next_pos)

/-- `Inv` ignores `timers` and `downs`. -/
theorem Inv.set_timers {a : Sys St Msg} (hi : Inv a) (t : List (Pid × Msg)) :
    Inv { a with timers := t } := ⟨hi.next_pos, hi.sup_alive, hi.child_ok⟩

theorem Inv.set_downs {a : Sys St Msg} (hi : Inv a) (d : List (Pid × Pid × Reason)) :
    Inv { a with downs := d } := ⟨hi.next_pos, hi.sup_alive, hi.child_ok⟩

/-- The `timer` case of `Inv.step`. -/
theorem Inv.timer {a b : Sys St Msg} {i : Nat} (h : timerE a i = some b) (hi : Inv a) : Inv b :=
  (hi.set_timers _).grows (timerE_grows h)

/-- The `down` case of `Inv.step`. -/
theorem Inv.down {a b : Sys St Msg} (h : downE sig a = some b) (hi : Inv a) : Inv b := by
  obtain ⟨_, _, _, rest, _, hg⟩ := downE_grows h
  exact (hi.set_downs rest).grows hg

/-- A worker step that emits no `exit` (the `job`, `start` and `EXIT`
clauses) is a frame around a pid other than the supervisor, plus liveness
and links kept by `runE_of_no_exit`. -/
theorem Inv.worker_noexit {a b : Sys St Msg} (hi : Inv a) {p : Pid} (hp : p ≠ 0)
    (h : runE beh a p = some b)
    (hexit : ∀ st m rest, a.cfg.get p = some ⟨st, m :: rest⟩ →
      ∀ r, Effect.exit r ∉ (beh p a.next st m).2) : Inv b :=
  let f := runE_frame h
  let n := runE_of_no_exit h hexit
  Inv.frame hi f.next (f.stateOf 0 (Ne.symm hp) hi.next_pos) n.1 (fun c => n.2.1 (0, c))
    (fun _ _ hs => Or.inl (f.signals _ hs)) (fun _ _ _ _ => f.mcount 0 _ (Ne.symm hp) hi.next_pos)

end Leanactors.Examples.Supervisor
