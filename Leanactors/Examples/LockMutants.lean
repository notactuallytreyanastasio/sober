import Leanactors.Examples.Lock
/-!
# Leanactors.Examples.LockMutants

Does the invariant have teeth? Three plausible implementation bugs.

* Two are caught by the bounded checker with a concrete trace. For those,
  `Inv.step` cannot be proven: the failing case is exactly the wrong line.
* One is **not** caught, and that is correct: with honest clients the buggy
  branch is unreachable. The invariant already says why (`r c p = 0` for
  every non-holder), so the sender check in `Lock.handle_cast({:release, p}, ...)`
  is defensive against misbehaving clients, not load-bearing for this
  protocol. The model tells you which checks you can drop.
-/

namespace Leanactors.Examples.Lock

/-- **Mutant A** (caught): on `acquire` while held, grant anyway instead of
queueing. The classic "forgot the busy case" bug. -/
def behGrantWhileHeld : Behavior St Msg
  | .srv _ q,        .acquire p => (.srv (some p) q, [(p, .grant)])
  | .srv (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.srv none [], [])
        | n :: rest => (.srv (some n) rest, [(n, .grant)])
      else (.srv (some h) q, [])
  | .cli me .idle,    .tick  => (.cli me .waiting, [(server, .acquire me)])
  | .cli me .waiting, .grant => (.cli me .holding, [])
  | .cli me .holding, .tick  => (.cli me .idle, [(server, .release me)])
  | s, _ => (s, [])

/-- **Mutant B** (caught, but *not* by mutex): a waiting client re-sends
`acquire` on every tick. It gets queued twice, is granted a second time
while idle, ignores the grant, and the token is lost: the server believes
the client holds the lock forever. Mutual exclusion still holds, so a
mutex-only check would miss this; `Inv` catches it because `a + qn = w`
fails the moment the duplicate request lands. -/
def behDuplicateAcquire : Behavior St Msg
  | .srv none q,     .acquire p => (.srv (some p) q, [(p, .grant)])
  | .srv (some h) q, .acquire p => (.srv (some h) (q ++ [p]), [])
  | .srv (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.srv none [], [])
        | n :: rest => (.srv (some n) rest, [(n, .grant)])
      else (.srv (some h) q, [])
  | .cli me .idle,    .tick  => (.cli me .waiting, [(server, .acquire me)])
  | .cli me .waiting, .tick  => (.cli me .waiting, [(server, .acquire me)])
  | .cli me .waiting, .grant => (.cli me .holding, [])
  | .cli me .holding, .tick  => (.cli me .idle, [(server, .release me)])
  | s, _ => (s, [])

/-- **Mutant C** (not caught, correctly): the server does not check that
the releaser is the holder. Harmless here because only a holder ever sends
`release`. It becomes a bug the moment a client can crash-and-restart or a
third party can cast `{:release, pid}`. -/
def behNoSenderCheck : Behavior St Msg
  | .srv none q,     .acquire p => (.srv (some p) q, [(p, .grant)])
  | .srv (some h) q, .acquire p => (.srv (some h) (q ++ [p]), [])
  | .srv (some _) q, .release _ =>
      match q with
      | []        => (.srv none [], [])
      | n :: rest => (.srv (some n) rest, [(n, .grant)])
  | .cli me .idle,    .tick  => (.cli me .waiting, [(server, .acquire me)])
  | .cli me .waiting, .grant => (.cli me .holding, [])
  | .cli me .holding, .tick  => (.cli me .idle, [(server, .release me)])
  | s, _ => (s, [])

-- A and B must return a path; C must return `none`.
#eval explore behGrantWhileHeld  (initCfg 2) [0, 1, 2] 10 5
#eval explore behDuplicateAcquire (initCfg 2) [0, 1, 2] 10 5
#eval explore behNoSenderCheck   (initCfg 2) [0, 1, 2] 9 5

end Leanactors.Examples.Lock
