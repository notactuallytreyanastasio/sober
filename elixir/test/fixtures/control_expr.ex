# expect: ok
# lean: check
# Control flow as an expression. Any sub-expression may be an `if`, a `case`
# or a block: an `if` inside a tuple element, a `case` nested inside another
# `case` in a cast body, a `cond` (nested `if`s, whose last clause must be
# `true ->`), and a block `(a; b; c)` as a sub-expression (nested `let`s,
# the last statement the value).
defmodule Gauge do
  use GenServer

  @type msg :: {:set, integer()} | {:adjust, integer()} | :tick | :classify
  @type level :: :low | :mid | :high
  @type state :: {integer(), level()}

  def init(s), do: {:ok, s}

  # an `if` inside a tuple element: one field of the new state is a branch
  def handle_cast({:set, v}, {_old, l}) do
    {:noreply, {v, if(v > 10, do: :high, else: l)}}
  end

  # a `case` inside a `case`, both as sub-expressions of a binding
  def handle_cast({:adjust, d}, {v, l}) do
    n =
      case l do
        :low -> v + d
        :mid ->
          case d do
            0 -> v
            _ -> v + 2 * d
          end
        :high -> v - d
      end

    {:noreply, {n, l}}
  end

  # `cond` is nested `if`s
  def handle_cast(:tick, {v, _l}) do
    {:noreply,
     {v,
      cond do
        v > 10 -> :high
        v > 0 -> :mid
        true -> :low
      end}}
  end

  # a block as a sub-expression
  def handle_cast(:classify, {v, _l}) do
    {:noreply,
     {(
        w = v * 2
        w - 1
      ), :mid}}
  end
end
