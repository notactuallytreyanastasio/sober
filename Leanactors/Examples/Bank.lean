import Leanactors.Props
import Leanactors.Gen.Bank
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

-- `Msg`, `St` and `bank` come from the translation of `elixir/src/bank.ex`.
-- `St.client_await0` is the generated continuation state for the client's
-- blocking `GenServer.call`.
export Leanactors.Gen.Bank (Msg St bank)

/-- The behaviour, hand-written. Note the bank stores an `Int`, not a `Nat`:
non-negativity is a *proven invariant*, not baked into the type. -/
def beh : Behavior St Msg
  | _,  .bank b, .deposit n      => (.bank (b + n), [])
  | _,  .bank b, .withdraw n     => if (n : Int) ≤ b then (.bank (b - n), []) else (.bank b, [])
  | _,  .bank b, .balance to     => (.bank b, [(to, .reply b)])
  | me, .client _, .tick         => (.client_await0, [(bank, .balance me)])
  | _,  .client_await0, .reply v => (.client (some v), [])
  | me, .client_await0, m        => (.client_await0, [(me, m)])
  | _,  s, _                     => (s, [])

/-- The translated Elixir is extensionally the same behaviour. -/
theorem beh_eq_gen : Gen.Bank.beh = beh := by
  funext p s m
  cases s <;> cases m <;> first | rfl | simp [Gen.Bank.beh, beh]

/-- The invariant: bank balances are non-negative; clients are unconstrained. -/
def Ok : St → Prop
  | .bank b => 0 ≤ b
  | .client _ => True
  | .client_await0 => True

/-- Each handler clause preserves `Ok`. This is the only proof that touches
the business logic. -/
theorem beh_preserves : Preserves beh Ok := by
  intro _ s m hs
  cases s with
  | client seen => cases m <;> simp [beh, Ok]
  | client_await0 => cases m <;> simp [beh, Ok]
  | bank b =>
    simp [Ok] at hs
    cases m with
    | deposit n => simp [beh, Ok]; omega
    | withdraw n =>
      simp only [beh]
      split <;> simp [Ok] <;> omega
    | balance to => simpa [beh, Ok] using hs
    | reply v => simpa [beh, Ok] using hs
    | tick => simpa [beh, Ok] using hs

/-- Initial configuration: the bank with 10, clients at pids 1 and 2. -/
def init : Config St Msg :=
  Config.ofList [(bank, .bank 10), (1, .client none), (2, .client none)]

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

/-! ## Executable trace

The driver `elixir/bank.exs` performs the same interleaving on the BEAM:
three casts, client 1 ticks and blocks on `GenServer.call`, one more cast,
client 2 ticks. `run_sound` makes every `run` result reachable, so the
theorem covers this trace with no extra proof. -/

def stim1 : List (Pid × Msg) := [(bank, .withdraw 4), (bank, .deposit 3), (bank, .withdraw 100), (1, .tick)]
def stim2 : List (Pid × Msg) := [(bank, .withdraw 9), (2, .tick)]

def mid : Config St Msg := run beh (init.deliverAll stim1) [1, 0, 0, 0, 0]
def final : Config St Msg := run beh (mid.deliverAll stim2) [2, 0, 0, 1, 2]

def snapshot (c : Config St Msg) (n : Nat) : List (Pid × Option (Actor St Msg)) :=
  (List.range n).map fun p => (p, c.get p)

#eval snapshot final 3

/-- **Selective receive check.** A second tick arrives while client 1 is
blocked in its call. The model re-enqueues it behind the reply, so it is
processed *after* the first call completes and triggers a second call,
which sees the deposit made in between. A model that dropped messages
during the call would end with `some 10`. -/
def deferred : Config St Msg :=
  let d1 := run beh (init.deliverAll [(1, .tick), (1, .tick)]) [1, 1, 0, 1, 1]
  run beh (d1.deliverAll [(bank, .deposit 5)]) [0, 1, 0, 1]

#eval snapshot deferred 2

theorem final_ok : AllStates Ok final :=
  (run_sound _ _).preserves beh_preserves
    (Config.deliverAll_allStates _
      ((run_sound _ _).preserves beh_preserves (Config.deliverAll_allStates _ init_ok)))

example : ∀ p b mb, final.get p = some ⟨.bank b, mb⟩ → 0 ≤ b :=
  fun p _ _ h => final_ok p _ h

end Leanactors.Examples.Bank
