# expect: ok
# lean: check
# `{:noreply, s, {:continue, x}}` and `{:reply, r, s, {:continue, x}}` run
# handle_continue(x, s) before any queued message is looked at, so the
# continue is not a message: the matching handle_continue body is inlined
# after the clause's own effects (and, for the reply form, after the
# reply), with its argument and state patterns bound to x and s. A continue
# body may continue again (`{:fetch, k}` continues into `:warm`), time out
# (`:sleep`) or branch (`:warm` is an `if`, so the reply of `:reload` is
# pushed into both branches). A continue's state pattern is a tuple of
# variables bound to the parts of a tuple literal (`{:load, k}`) or to the
# fields of the clause's whole-state variable (`:refresh`, `:reset`, whose
# unused field is pruned to `_`), or a variable bound to the whole new
# state (`:sleep`). `@type continue` is accepted and generates nothing.
defmodule Loader do
  use GenServer

  @type msg :: {:load, non_neg_integer()} | :refresh | :reset | :tick | :timeout | {:loaded, non_neg_integer()}
  @type call :: :reload
  @type reply :: :ok
  @type state :: {non_neg_integer(), pid()}
  @type continue :: {:fetch, non_neg_integer()} | :warm | :reset | :sleep

  def init(p), do: {:ok, p}

  def handle_cast({:load, k}, {n, sub}), do: {:noreply, {n, sub}, {:continue, {:fetch, k}}}
  def handle_cast(:refresh, s), do: {:noreply, s, {:continue, :warm}}
  def handle_cast(:reset, s), do: {:noreply, s, {:continue, :reset}}
  def handle_cast(:tick, s), do: {:noreply, s, {:continue, :sleep}}

  def handle_call(:reload, _from, {n, sub}) do
    send(sub, {:loaded, 0})
    {:reply, :ok, {n + 1, sub}, {:continue, :warm}}
  end

  def handle_info(:timeout, s), do: {:noreply, s}
  def handle_info({:loaded, m}, {n, sub}), do: {:noreply, {n + m, sub}}

  def handle_continue({:fetch, key}, {n, sub}) do
    send(sub, {:loaded, key})
    {:noreply, {n + key, sub}, {:continue, :warm}}
  end

  def handle_continue(:warm, {n, sub}) do
    if n > 10 do
      send(sub, {:loaded, n})
      {:noreply, {0, sub}}
    else
      {:noreply, {n + 1, sub}}
    end
  end

  def handle_continue(:reset, {_, sub}), do: {:noreply, {0, sub}}

  def handle_continue(:sleep, s), do: {:noreply, s, 100}
end
