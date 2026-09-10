# expect: ok
# lean: check
# Elixir variables that are Lean keywords (`from`, `at`, `open`) get a
# trailing underscore, both as pattern variables and as the handle_call
# `from` argument.
defmodule Echo do
  use GenServer

  @type msg :: {:hello, pid()} | {:move, non_neg_integer()} | {:set, boolean()}
  @type call :: :whoami
  @type reply :: pid()
  @type state :: {GenServer.from() | nil, non_neg_integer(), boolean()}

  def init(s), do: {:ok, s}

  def handle_cast({:hello, from}, {f, at, open}) do
    send(from, {:hello, self()})
    {:noreply, {f, at, open}}
  end

  def handle_cast({:move, at}, {f, _, open}), do: {:noreply, {f, at, open}}
  def handle_cast({:set, open}, {f, at, _}), do: {:noreply, {f, at, open}}

  def handle_call(:whoami, from, {_, at, open}), do: {:reply, self(), {from, at, open}}
end
