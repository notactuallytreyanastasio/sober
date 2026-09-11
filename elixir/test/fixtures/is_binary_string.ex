# expect: ok
# lean: check
# `is_binary/1` is decided statically like the other type tests, now that a
# binary is a Lean `String`: it is `true` at `String.t()` and `false` at
# every other modelled type. Both sides of the round-7 merge are needed for
# this fixture -- the type tests come from the expression compiler, the
# string type from the value families -- so it lives here rather than in
# `kernel_guards.ex` or `strings.ex`.
defmodule Sniffer do
  use GenServer

  @type msg :: {:note, String.t()} | {:count, non_neg_integer()}
  @type call :: :kinds
  @type reply :: non_neg_integer()
  @type state :: %{label: String.t(), n: non_neg_integer(), tag: pid() | nil}

  def init(l), do: {:ok, %{label: l, n: 0, tag: nil}}

  def handle_cast({:note, x}, s) do
    if is_binary(x), do: {:noreply, %{s | label: x}}, else: {:noreply, s}
  end

  def handle_cast({:count, k}, s) do
    # `is_binary` on a non_neg_integer() is `false`, so the `else` branch is
    # the one the model takes
    if is_binary(k), do: {:noreply, s}, else: {:noreply, %{s | n: s.n + k}}
  end

  # a binary is not an atom, a list, a map, a tuple or a pid
  def handle_call(:kinds, _from, s) do
    bad = is_atom(s.label) || is_list(s.label) || is_map(s.label) || is_tuple(s.label)
    if bad, do: {:reply, 0, s}, else: {:reply, s.n, s}
  end
end
