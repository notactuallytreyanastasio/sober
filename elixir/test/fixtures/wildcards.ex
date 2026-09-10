# expect: ok
# lean: check
# Wildcards: each `_` in a clause becomes a distinct `_wN`; `_name` variables
# become `_`; a whole-state `_s` against a multi-field state binds `_s_i`
# per field; a `_from` argument is still the reply target.
defmodule Wild do
  use GenServer

  @type msg :: {:pair, non_neg_integer(), non_neg_integer()} | :zero
  @type call :: :peek
  @type reply :: non_neg_integer()
  @type state :: {non_neg_integer(), non_neg_integer(), pid() | nil}

  def init(s), do: {:ok, s}

  def handle_cast({:pair, a, _}, {_, c, _}) when a > c, do: {:noreply, {a, c, nil}}
  def handle_cast({:pair, _, _}, _s), do: {:noreply, {0, 0, nil}}
  def handle_cast(:zero, {_a, _b, _p}), do: {:noreply, {0, 0, nil}}

  def handle_call(:peek, _from, {a, _, _}), do: {:reply, a, {a, 0, nil}}
end
