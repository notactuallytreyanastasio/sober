/-!
# Leanactors.Core

A shallow embedding of an actor system in Lean 4, intended as a semantic
target for a pure subset of Elixir/BEAM programs.

Design:
* An actor is a `Behavior σ μ`: a pure function from (state, message) to
  (new state, list of sends). This is `GenServer.handle_cast/2` with the
  side effect of `send/2` reified as data.
* A `Config` holds every live actor's state and mailbox.
* `Step` is a nondeterministic labelled transition: any actor with a
  nonempty mailbox may run. The choice of *which* one is the scheduler.
* Mailboxes are lists; `send` appends. This gives BEAM's per-pair FIFO
  guarantee for free and is the only ordering BEAM actually promises.
-/

namespace Leanactors

/-- A process identifier. -/
abbrev Pid := Nat

/-- An actor's behaviour: given its own pid (`self()`), its state and one
message, return the new state and the messages it wants sent, in order. -/
abbrev Behavior (σ μ : Type) := Pid → σ → μ → σ × List (Pid × μ)

/-- One live actor. -/
structure Actor (σ μ : Type) where
  state : σ
  mailbox : List μ
  deriving Repr

/-- A whole system. All actors share the behaviour `beh` and state type `σ`;
heterogeneous systems are modelled by making `σ` and `μ` sum types. -/
structure Config (σ μ : Type) where
  actors : Pid → Option (Actor σ μ)

namespace Config

variable {σ μ : Type}

/-- Look up an actor. -/
def get (c : Config σ μ) (p : Pid) : Option (Actor σ μ) := c.actors p

/-- Replace (or create) an actor. -/
def set (c : Config σ μ) (p : Pid) (a : Actor σ μ) : Config σ μ :=
  ⟨fun q => if q = p then some a else c.actors q⟩

/-- Deliver one message to `p`'s mailbox. Sends to a dead or nonexistent
pid are silently dropped, exactly as on the BEAM. -/
def deliver (c : Config σ μ) (p : Pid) (m : μ) : Config σ μ :=
  match c.actors p with
  | none => c
  | some a => c.set p { a with mailbox := a.mailbox ++ [m] }

/-- Deliver a batch of sends in order. -/
def deliverAll (c : Config σ μ) : List (Pid × μ) → Config σ μ
  | [] => c
  | (p, m) :: rest => (c.deliver p m).deliverAll rest

/-- Remove an actor (process exit). -/
def remove (c : Config σ μ) (p : Pid) : Config σ μ :=
  ⟨fun q => if q = p then none else c.actors q⟩

/-- Build a configuration from a list of `(pid, initial state)` pairs. -/
def ofList (xs : List (Pid × σ)) : Config σ μ :=
  ⟨fun p => (xs.find? (·.1 = p)).map fun (_, s) => ⟨s, []⟩⟩

end Config

/-- The scheduler's choice: which pid to run next. -/
abbrev Choice := Pid

/-- Executable single step. Returns `none` if the chosen pid does not exist
or has an empty mailbox. -/
def step {σ μ : Type} (beh : Behavior σ μ) (c : Config σ μ) (p : Choice) :
    Option (Config σ μ) :=
  match c.get p with
  | some ⟨s, m :: rest⟩ =>
    some ((c.set p ⟨(beh p s m).1, rest⟩).deliverAll (beh p s m).2)
  | _ => none

/-- Relational single step: `Step beh c c'` holds iff some actor with a
nonempty mailbox can take `c` to `c'`. -/
inductive Step {σ μ : Type} (beh : Behavior σ μ) : Config σ μ → Config σ μ → Prop
  | run (c : Config σ μ) (p : Pid) (s : σ) (m : μ) (rest : List μ)
      (h : c.get p = some ⟨s, m :: rest⟩) :
      Step beh c ((c.set p ⟨(beh p s m).1, rest⟩).deliverAll (beh p s m).2)

/-- Reflexive-transitive closure: reachability under any fair or unfair
scheduler. -/
inductive Reach {σ μ : Type} (beh : Behavior σ μ) : Config σ μ → Config σ μ → Prop
  | refl (c) : Reach beh c c
  | step {a b c} : Step beh a b → Reach beh b c → Reach beh a c

/-- Run a fixed schedule executably. Stops at the first invalid choice. -/
def run {σ μ : Type} (beh : Behavior σ μ) : Config σ μ → List Choice → Config σ μ
  | c, [] => c
  | c, p :: ps =>
    match step beh c p with
    | some c' => run beh c' ps
    | none => c

end Leanactors
