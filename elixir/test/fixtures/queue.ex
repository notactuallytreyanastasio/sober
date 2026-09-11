# expect: ok
# lean: check
# :queue as a list, oldest first. `:queue.queue(T)` is `List T`, `:queue.new()`
# is `[]`, `:queue.in(x, q)` is `q ++ [x]` (the tail is the young end),
# `:queue.to_list(q)` the identity, `:queue.len` and `:queue.is_empty` the
# List functions, `:queue.peek(q)` is `List.head?` (matched with `{:value, x}`
# and `:empty`), and `{_, q} = :queue.out(q0)` is `let q := List.tail q0`
# (out of an empty queue gives it back, as `tail` does). A `case :queue.out(q)`
# matches the list instead: `{{:value, x}, rest}` is `x :: rest` and
# `{:empty, q}` is `[]` with q aliased to it.
defmodule Fifo do
  use GenServer

  @type cast :: {:push, non_neg_integer()} | :pop | :clear
  @type call :: :size | :front | :serve
  @type reply :: {:n, non_neg_integer()} | {:head, non_neg_integer()} | :empty
  @type state :: {:queue.queue(non_neg_integer()), non_neg_integer()}

  def init(n), do: {:ok, {:queue.new(), n}}

  def handle_cast({:push, x}, {q, served}), do: {:noreply, {:queue.in(x, q), served}}

  def handle_cast(:pop, {q0, served}) do
    {_, q} = :queue.out(q0)
    {:noreply, {q, served}}
  end

  def handle_cast(:clear, {_q, served}), do: {:noreply, {:queue.new(), served}}

  def handle_call(:size, _from, {q, served}) do
    if :queue.is_empty(q) do
      {:reply, :empty, {q, served}}
    else
      {:reply, {:n, :queue.len(q) + length(:queue.to_list(q))}, {q, served}}
    end
  end

  # :queue.peek/1 is an Option, matched with {:value, x} and :empty
  def handle_call(:front, _from, {q, served}) do
    case :queue.peek(q) do
      {:value, x} -> {:reply, {:head, x}, {q, served}}
      :empty -> {:reply, :empty, {q, served}}
    end
  end

  # case :queue.out/1 matches head and rest at once
  def handle_call(:serve, _from, {q0, served}) do
    case :queue.out(q0) do
      {{:value, x}, rest} -> {:reply, {:head, x}, {rest, served + 1}}
      {:empty, q} -> {:reply, :empty, {q, served}}
    end
  end
end
