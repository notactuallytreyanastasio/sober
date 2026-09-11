# expect: ok
# lean: check
# Binaries are Lean Strings (Leanactors/Str.lean). A `String.t()` or
# `binary()` in a @type is `String`, a literal is the Lean literal, `<>` is
# `++`, and an interpolation `"a#{e}b"` is `"a" ++ Str.toStr e ++ "b"` --
# `Str.toStr` renders a value with no printable model through its derived
# `Repr`, which is an opaque but deterministic rendering. A string literal
# in a pattern is a Lean literal pattern (and never covers a clause, so the
# catch-all below is what makes `greet` total).
defmodule Greeter do
  use GenServer

  @type msg :: {:greet, String.t()} | {:suffix, binary()} | :clear
  @type call :: :render | :shout | :info
  @type reply :: String.t()
  @type state :: %{name: String.t(), suffix: String.t(), greeted: non_neg_integer()}

  def init(n), do: {:ok, %{name: n, suffix: "", greeted: 0}}

  # a string literal pattern: the empty name is ignored
  def handle_cast({:greet, ""}, s), do: {:noreply, s}
  def handle_cast({:greet, n}, s), do: {:noreply, %{s | name: n, greeted: s.greeted + 1}}
  def handle_cast({:suffix, x}, s), do: {:noreply, %{s | suffix: s.suffix <> x}}
  def handle_cast(:clear, s), do: {:noreply, %{s | suffix: ""}}

  def handle_call(:render, _from, s), do: {:reply, "hello, #{s.name}!#{s.suffix}", s}
  def handle_call(:shout, _from, s), do: {:reply, "#{s.name} (#{s.greeted} times)", s}

  # `inspect/1` and `to_string/1` are the same `Str.toStr` an interpolation
  # uses; String.length/1 is a @remote row of Lean's own String.length
  def handle_call(:info, _from, s) do
    {:reply, "len=" <> to_string(String.length(s.name)) <> " up=" <> String.upcase(s.name) <> " n=" <> inspect(s.greeted), s}
  end
end
