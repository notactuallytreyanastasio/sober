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
  | _,  .lock _ q,        .acquire p => (.lock (some p) q, [(p, .reply .ok)])
  | _,  .lock (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.lock none [], [])
        | n :: rest => (.lock (some n) rest, [(n, .reply .ok)])
      else (.lock (some h) q, [])
  | me, .client .idle,    .tick      => (.client_await0, [(server, .acquire me)])
  | me, .client .holding, .tick      => (.client .idle, [(server, .release me)])
  | _,  .client_await0,   .reply .ok => (.client .holding, [])
  | me, .client_await0,   m          => (.client_await0, [(me, m)])
  | _,  s, _ => (s, [])

/-- **Mutant B** (caught, but *not* by mutex): a blocked client re-sends
`acquire` on every tick instead of deferring it (a hand-written receive
loop that forgot the `after`/selective-receive discipline). It gets queued twice, is granted a second time
while idle, ignores the grant, and the token is lost: the server believes
the client holds the lock forever. Mutual exclusion still holds, so a
mutex-only check would miss this; `Inv` catches it because `a + qn = w`
fails the moment the duplicate request lands. -/
def behDuplicateAcquire : Behavior St Msg
  | _,  .lock none q,     .acquire p => (.lock (some p) q, [(p, .reply .ok)])
  | _,  .lock (some h) q, .acquire p => (.lock (some h) (q ++ [p]), [])
  | _,  .lock (some h) q, .release p =>
      if p = h then
        match q with
        | []        => (.lock none [], [])
        | n :: rest => (.lock (some n) rest, [(n, .reply .ok)])
      else (.lock (some h) q, [])
  | me, .client .idle,    .tick      => (.client_await0, [(server, .acquire me)])
  | me, .client .holding, .tick      => (.client .idle, [(server, .release me)])
  | _,  .client_await0,   .reply .ok => (.client .holding, [])
  | me, .client_await0,   .tick      => (.client_await0, [(server, .acquire me)])
  | me, .client_await0,   m          => (.client_await0, [(me, m)])
  | _,  s, _ => (s, [])

/-- **Mutant C** (not caught, correctly): the server does not check that
the releaser is the holder. Harmless here because only a holder ever sends
`release`. It becomes a bug the moment a client can crash-and-restart or a
third party can cast `{:release, pid}`. -/
def behNoSenderCheck : Behavior St Msg
  | _,  .lock none q,     .acquire p => (.lock (some p) q, [(p, .reply .ok)])
  | _,  .lock (some h) q, .acquire p => (.lock (some h) (q ++ [p]), [])
  | _,  .lock (some _) q, .release _ =>
      match q with
      | []        => (.lock none [], [])
      | n :: rest => (.lock (some n) rest, [(n, .reply .ok)])
  | me, .client .idle,    .tick      => (.client_await0, [(server, .acquire me)])
  | me, .client .holding, .tick      => (.client .idle, [(server, .release me)])
  | _,  .client_await0,   .reply .ok => (.client .holding, [])
  | me, .client_await0,   m          => (.client_await0, [(me, m)])
  | _,  s, _ => (s, [])

-- A and B must return a path; C must return `none`.
#eval explore behGrantWhileHeld  (initCfg 2) [0, 1, 2] 10 5
#eval explore behDuplicateAcquire (initCfg 2) [0, 1, 2] 10 5
#eval explore behNoSenderCheck   (initCfg 2) [0, 1, 2] 9 5

end Leanactors.Examples.Lock
