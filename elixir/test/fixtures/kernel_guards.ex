# expect: ok
# lean: check
# Kernel guards and functions on the types the model has. A type test is
# decided statically, because a value of the model has exactly one type:
# `is_pid` on a `pid()` is `true`, `is_list` on a `[T]` is `true` and
# `is_map` on it is `false`; on a `T | nil`, `is_nil` is `isNone` and the
# other tests are `isSome`. `abs`, `min`, `max`, `div` and `rem` are the
# arithmetic (`div`/`rem` on non_neg_integer(), where Elixir and Lean agree),
# `x in l` is list membership, and `&&`, `||`, `!`, `*`, `===` and `!==` are
# the operators Elixir spells differently from `and`, `or` and `not`.
defmodule Probe do
  use GenServer

  @type msg :: {:watch, pid()} | :clear | {:scale, non_neg_integer()} | {:pick, non_neg_integer()}
  @type call :: :count
  @type reply :: non_neg_integer()
  @type state :: {pid() | nil, [non_neg_integer()], non_neg_integer()}

  def init(s), do: {:ok, s}

  # is_nil on an Option, is_pid on a Pid, `&&`
  def handle_cast({:watch, p}, {owner, l, n}) do
    if is_nil(owner) && is_pid(p) do
      {:noreply, {p, l, n}}
    else
      {:noreply, {owner, l, n}}
    end
  end

  # is_list / is_map / is_atom / is_boolean / is_integer / is_number /
  # is_float, `||` and `!`
  def handle_cast(:clear, {owner, l, n}) do
    if (is_list(l) || is_map(l)) && !is_atom(n) && is_integer(n) &&
         is_number(n) && !is_float(n) && !is_boolean(n) do
      {:noreply, {owner, [], n}}
    else
      {:noreply, {owner, l, n}}
    end
  end

  # abs, min, max, div, rem, `*`
  def handle_cast({:scale, k}, {owner, l, n}) do
    m = min(max(n * k, 1), 100)
    {:noreply, {owner, l, div(m, 2) + rem(m, 3) + abs(n)}}
  end

  # `x in l`, `===`, `!==`
  def handle_cast({:pick, k}, {owner, l, n}) do
    if k in l && k !== n do
      {:noreply, {owner, l, k}}
    else
      {:noreply, {owner, l, n}}
    end
  end

  def handle_call(:count, _from, {owner, l, n}) do
    {:reply, length(l) + n, {owner, l, n}}
  end
end
