import Leanactors.Props
/-!
# Leanactors.Examples.Bank

A bank-account GenServer and a client. The Elixir we are modelling:

```elixir
defmodule Bank do
  use GenServer
  @spec handle_cast({:deposit, non_neg_integer()} | {:withdraw, non_neg_integer()}
                    | {:balance, pid()}, non_neg_integer()) :: {:noreply, non_neg_integer()}
  def handle_cast({:deposit, n}, b),  do: {:noreply, b + n}
  def handle_cast({:withdraw, n}, b) when n <= b, do: {:noreply, b - n}
  def handle_cast({:withdraw, _}, b), do: {:noreply, b}
  def handle_cast({:balance, to}, b), do: send(to, {:reply, b}); {:noreply, b}
end
```

Elixir's type checker can verify each clause returns a `non_neg_integer()`
*given* the state is one. It cannot verify the state stays one across
arbitrary interleavings with other processes. That is what we prove here.
-/

namespace Leanactors.Examples.Bank

open Leanactors

inductive Msg
  | deposit (n : Nat)
  | withdraw (n : Nat)
  | balance (replyTo : Pid)
  | reply (v : Int)
  deriving Repr, DecidableEq

/-- Heterogeneous system: a bank and clients share one state type. -/
inductive St
  | bank (balance : Int)
  | client (seen : Option Int)
  deriving Repr, DecidableEq

/-- The behaviour. Note the bank stores an `Int`, not a `Nat`: the
non-negativity is a *proven invariant*, not baked into the type. This
mirrors Elixir where the runtime value is just an integer. -/
def beh : Behavior St Msg
  | _, .bank b,   .deposit n     => (.bank (b + n), [])
  | _, .bank b,   .withdraw n    => if (n : Int) ≤ b then (.bank (b - n), []) else (.bank b, [])
  | _, .bank b,   .balance to    => (.bank b, [(to, .reply b)])
  | _, .client _, .reply v       => (.client (some v), [])
  | _, s,         _              => (s, [])

/-- The invariant: bank balances are non-negative; clients are unconstrained. -/
def Ok : St → Prop
  | .bank b => 0 ≤ b
  | .client _ => True

/-- Each handler clause preserves `Ok`. This is the only proof that touches
the business logic. -/
theorem beh_preserves : Preserves beh Ok := by
  intro _ s m hs
  cases s with
  | client seen => cases m <;> simp [beh, Ok]
  | bank b =>
    simp [Ok] at hs
    cases m with
    | deposit n => simp [beh, Ok]; omega
    | withdraw n =>
      simp only [beh]
      split <;> simp [Ok] <;> omega
    | balance to => simpa [beh, Ok] using hs
    | reply v => simpa [beh, Ok] using hs

/-- Initial configuration: pid 0 is the bank with 10, pids 1 and 2 are clients. -/
def init : Config St Msg :=
  Config.ofList [(0, .bank 10), (1, .client none), (2, .client none)]

theorem init_ok : AllStates Ok init :=
  Config.ofList_allStates _ (by simp [Ok])

/-- **Main theorem.** Starting from any configuration whose banks are
solvent, under any scheduler and any interleaving, every bank's balance
stays non-negative. -/
theorem balance_never_negative {c₀ c : Config St Msg}
    (h₀ : AllStates Ok c₀) (hr : Reach beh c₀ c) :
    ∀ p b mb, c.get p = some ⟨.bank b, mb⟩ → 0 ≤ b := by
  intro p b mb h
  exact hr.preserves beh_preserves h₀ p _ h

/-- Corollary for our concrete initial state plus *any* external stimulus. -/
theorem init_balance_never_negative (stim : List (Pid × Msg)) {c : Config St Msg}
    (hr : Reach beh (init.deliverAll stim) c) :
    ∀ p b mb, c.get p = some ⟨.bank b, mb⟩ → 0 ≤ b :=
  balance_never_negative (Config.deliverAll_allStates stim init_ok) hr

/-! ## Executable trace

`run_sound` says every `run` result is `Reach`-able, so the theorem above
applies to this concrete trace with no extra work. -/

/-- External stimulus: what a shell would `GenServer.cast` in. -/
def stimulus : List (Pid × Msg) :=
  [ (0, .withdraw 4), (0, .deposit 3), (0, .withdraw 100), (0, .balance 1),
    (0, .withdraw 9), (0, .balance 2) ]

def start : Config St Msg := init.deliverAll stimulus

/-- Bank drains its mailbox, then clients read replies. -/
def schedule : List Choice := [0, 0, 0, 0, 0, 0, 1, 2]

def final : Config St Msg := run beh start schedule

def snapshot (c : Config St Msg) (n : Nat) : List (Pid × Option (Actor St Msg)) :=
  (List.range n).map fun p => (p, c.get p)

#eval snapshot final 3

/-- The trace is a witness: `final` is reachable, so the theorem applies
to it with no further proof. -/
example : ∀ p b mb, final.get p = some ⟨.bank b, mb⟩ → 0 ≤ b :=
  init_balance_never_negative stimulus (run_sound start schedule)

end Leanactors.Examples.Bank
