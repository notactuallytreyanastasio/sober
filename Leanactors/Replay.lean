import Leanactors.Examples.Bank
import Leanactors.Examples.Ttl
/-!
# Leanactors.Replay

An executable front end to the two interpreters, `run` (`Core.lean`) and
`runSys` (`Sys.lean`), for differential testing against the BEAM. It is
the `replay` target of `lakefile.toml` (`lake build replay`, binary at
`.lake/build/bin/replay`) and is driven by `elixir/fuzz.exs`, which
generates random scripts, replays each here and on the BEAM, and
compares the two outputs byte for byte.

**Script.** One command per line on stdin, ended by EOF or a line `end`
(a BEAM port cannot half-close stdin). Blank lines and `#` comments are
skipped. The first command names the example; the rest are the
scheduler's choices, in order:

```
example bank | example ttl
deliver <pid> <msg>     the environment sends <msg> to <pid> (Config.deliver)
run <pid>               <pid> handles the head of its mailbox
signal                  deliver the oldest pending exit signal   (ttl only)
down                    deliver the oldest pending DOWN           (ttl only)
timer <i>               fire the i-th pending timer               (ttl only)
```

Messages are the environment's vocabulary of each example, exactly the
messages the BEAM twin can send from outside: `deposit <n>`, `withdraw
<n>`, `tick`, `audit` for the bank; `put <n>`, `ask` for the TTL cache.
Internal messages (`balance`, `reply`, `get`, `value`, `after_run`) are
refused. A choice that is not enabled (`run` on an empty mailbox, `timer`
out of range, ...) is an error, unlike `runSys` which would silently
stop: a script is a schedule, and a schedule the model cannot follow is
a bug in the script, not a result.

**Observables.** The final configuration in a canonical text form, the
subset a BEAM twin can also report.

Bank (`Examples/Bank.lean`, start `Bank.init`: the bank at pid 0 with 10,
clients at 1 and 2):

```
bank <balance>
client 1 none | some <v> | await
client 2 none | some <v> | await
pending <messages left in the three mailboxes>
```

TTL (`Examples/Ttl.lean`, start `Ttl.init`: the cache at pid 0, empty,
generation 0, its generation-0 timer armed; the reader at pid 1):

```
cache none | some <v> | dead
reader <values counted by the reader's state>
values <every value delivered to the reader, oldest first; none or a number>
pending <messages left in the two mailboxes>
```

`values` is an observation on the mailbox, not on any actor's state: a
`value v` appended to the reader's mailbox by another actor's `run` step
(the reader's own steps only re-enqueue what it already had). On the
BEAM the twin traces the reader's receives, which is the same event.

Exit status 0 with the observables on stdout, or 2 with a message on
stderr for a malformed script or a disabled choice.
-/

namespace Leanactors.Replay

open Leanactors

/-- One scheduler choice of a script. -/
inductive Cmd
  | deliver (p : Pid) (msg : List String)
  | run (p : Pid)
  | signal
  | down
  | timer (i : Nat)

/-- Parse the words of line `ln`. -/
def parseCmd (ln : Nat) : List String → Except String Cmd
  | ["run", p] => match p.toNat? with
    | some p => .ok (.run p)
    | none => .error s!"line {ln}: bad pid {p}"
  | ["signal"] => .ok .signal
  | ["down"] => .ok .down
  | ["timer", i] => match i.toNat? with
    | some i => .ok (.timer i)
    | none => .error s!"line {ln}: bad timer index {i}"
  | "deliver" :: p :: msg => match p.toNat? with
    | some p => if msg.isEmpty then .error s!"line {ln}: deliver needs a message" else .ok (.deliver p msg)
    | none => .error s!"line {ln}: bad pid {p}"
  | words => .error s!"line {ln}: unknown command `{" ".intercalate words}`"

/-! ## Bank: the `Config` layer, `run` -/

namespace Bank

open Leanactors.Examples.Bank

/-- The environment's messages: `GenServer.cast(Bank, ...)` and
`send(client, ...)` in `elixir/fuzz.exs`. -/
def parseMsg : List String → Option Msg
  | ["deposit", n] => n.toNat?.map .deposit
  | ["withdraw", n] => n.toNat?.map .withdraw
  | ["tick"] => some .tick
  | ["audit"] => some .audit
  | _ => none

/-- `Bank.init` has pids 0, 1, 2. -/
def numPids : Nat := 3

def stateLine (c : Config St Msg) (p : Pid) : String :=
  match c.stateOf p with
  | some (.bank b) => s!"bank {b}"
  | some (.client none) => s!"client {p} none"
  | some (.client (some v)) => s!"client {p} some {v}"
  | some _ => s!"client {p} await"
  | none => s!"pid {p} dead"

def pending (c : Config St Msg) : Nat :=
  (List.range numPids).foldl (fun n p => n + ((c.get p).map (·.mailbox.length)).getD 0) 0

def step (c : Config St Msg) (ln : Nat) : Cmd → Except String (Config St Msg)
  | .deliver p ws => match parseMsg ws with
    | some m => .ok (c.deliver p m)
    | none => .error s!"line {ln}: not a bank environment message: {" ".intercalate ws}"
  | .run p => match c.get p with
    | some ⟨_, _ :: _⟩ => .ok (run beh c [p])
    | _ => .error s!"line {ln}: run {p} is not enabled"
  | _ => .error s!"line {ln}: the bank has no signals, DOWNs or timers"

def replay (cmds : List (Nat × Cmd)) : Except String String := do
  let c ← cmds.foldlM (fun c (ln, cmd) => step c ln cmd) init
  return "\n".intercalate ((List.range numPids).map (stateLine c) ++ [s!"pending {pending c}"]) ++ "\n"

end Bank

/-! ## TTL cache: the `Sys` layer, `runSys` -/

namespace Ttl

open Leanactors.Examples.Ttl

/-- The environment's messages: `send(cache, {:put, n})` and
`send(reader, :ask)` in `elixir/fuzz.exs`. -/
def parseMsg : List String → Option Msg
  | ["put", n] => n.toNat?.map .put
  | ["ask"] => some .ask
  | _ => none

/-- The system plus every `value` delivered to the reader so far. -/
structure Run where
  sys : Sys St Msg
  values : List (Option Nat)

def mailbox (s : Sys St Msg) (p : Pid) : List Msg := ((s.cfg.get p).map (·.mailbox)).getD []

def valuesIn (ms : List Msg) : List (Option Nat) :=
  ms.filterMap fun | .value v => some v | _ => none

/-- The reader is pid 1. -/
def reader : Pid := 1

def step (r : Run) (ln : Nat) : Cmd → Except String Run
  | .deliver p ws => match parseMsg ws with
    | some m => .ok { r with sys := { r.sys with cfg := r.sys.cfg.deliver p m } }
    | none => .error s!"line {ln}: not a ttl environment message: {" ".intercalate ws}"
  | .run p => match r.sys.cfg.get p with
    | some ⟨_, _ :: _⟩ =>
      let before := (mailbox r.sys reader).length
      let s' := runSys beh sig r.sys [.run p]
      let delivered := if p = reader then [] else valuesIn ((mailbox s' reader).drop before)
      .ok { sys := s', values := r.values ++ delivered }
    | _ => .error s!"line {ln}: run {p} is not enabled"
  | .signal => if r.sys.signals.isEmpty then .error s!"line {ln}: no pending signal"
    else .ok { r with sys := runSys beh sig r.sys [.signal] }
  | .down => if r.sys.downs.isEmpty then .error s!"line {ln}: no pending DOWN"
    else .ok { r with sys := runSys beh sig r.sys [.down] }
  | .timer i => if i < r.sys.timers.length then .ok { r with sys := runSys beh sig r.sys [.timer i] }
    else .error s!"line {ln}: timer {i} out of range ({r.sys.timers.length} pending)"

def showValue : Option Nat → String
  | none => "none"
  | some v => toString v

def render (r : Run) : String :=
  let cacheLine := match r.sys.cfg.stateOf cache with
    | some (.cache none _) => "cache none"
    | some (.cache (some v) _) => s!"cache some {v}"
    | some (.reader _) => "cache other"
    | none => "cache dead"
  let readerLine := match r.sys.cfg.stateOf reader with
    | some (.reader n) => s!"reader {n}"
    | some (.cache _ _) => "reader other"
    | none => "reader dead"
  let pending := (mailbox r.sys cache).length + (mailbox r.sys reader).length
  "\n".intercalate [cacheLine, readerLine,
    " ".intercalate ("values" :: r.values.map showValue), s!"pending {pending}"] ++ "\n"

def replay (cmds : List (Nat × Cmd)) : Except String String := do
  let r ← cmds.foldlM (fun r (ln, cmd) => step r ln cmd) { sys := init, values := [] }
  return render r

end Ttl

/-! ## Driver -/

/-- Read the script: numbered word lists, without blank lines and
comments, up to EOF or an `end` line. -/
def readScript (h : IO.FS.Stream) : IO (List (Nat × List String)) := do
  let mut out : List (Nat × List String) := []
  let mut ln := 0
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    ln := ln + 1
    let words := ((line.replace "\n" " " |>.replace "\r" " " |>.replace "\t" " ").splitOn " ").filter (· ≠ "")
    match words with
    | [] => pure ()
    | w :: _ =>
      if w.startsWith "#" then pure ()
      else if w == "end" then break
      else out := (ln, words) :: out
  return out.reverse

def replay (script : List (Nat × List String)) : Except String String := do
  match script with
  | [] => throw "empty script; the first line must be `example bank` or `example ttl`"
  | (ln, ["example", name]) :: rest =>
    let cmds ← rest.mapM fun (ln, ws) => (parseCmd ln ws).map (ln, ·)
    match name with
    | "bank" => Bank.replay cmds
    | "ttl" => Ttl.replay cmds
    | _ => throw s!"line {ln}: unknown example `{name}` (bank or ttl)"
  | (ln, _) :: _ => throw s!"line {ln}: the first line must be `example bank` or `example ttl`"

def main : IO UInt32 := do
  let script ← readScript (← IO.getStdin)
  match replay script with
  | .ok out => IO.print out; return 0
  | .error e => (← IO.getStderr).putStrLn s!"replay: {e}"; return 2

end Leanactors.Replay

def main : IO UInt32 := Leanactors.Replay.main
