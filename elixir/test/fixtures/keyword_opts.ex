# expect: ok
# lean: check
# A keyword list is the association list `List (Atom × V)` over the file's
# generated `Atom` inductive, so `Keyword` and `Access` are the same
# `Leanactors/AssocList.lean` a map uses: `Keyword.get/2` and `opts[:k]` are
# `get?` (an Option), `Keyword.get/3` is `(get? o k).getD d`, `Keyword.put`
# is `insert`, and `Keyword.fetch!/2` -- which raises on the BEAM, as an
# expression here cannot -- is the lookup at the value type's default.
defmodule Limits do
  use GenServer

  @type msg :: {:set, keyword(non_neg_integer())} | {:put, atom(), non_neg_integer()} | {:drop, atom()} | :defaults
  @type call :: :retries | :timeout | :must
  @type reply :: non_neg_integer()
  @type state :: keyword(non_neg_integer())

  def init(opts), do: {:ok, opts}

  def handle_cast({:set, o}, _), do: {:noreply, o}
  def handle_cast({:put, k, v}, opts), do: {:noreply, Keyword.put(opts, k, v)}
  def handle_cast({:drop, k}, opts), do: {:noreply, Keyword.delete(opts, k)}
  def handle_cast(:defaults, _), do: {:noreply, [retries: 3, timeout: 5000]}

  def handle_call(:retries, _from, opts), do: {:reply, Keyword.get(opts, :retries, 0), opts}
  def handle_call(:must, _from, opts), do: {:reply, Keyword.fetch!(opts, :retries), opts}

  # `opts[:timeout]` is Access.get/2: an Option, matched with nil
  def handle_call(:timeout, _from, opts) do
    case opts[:timeout] do
      nil -> {:reply, 0, opts}
      t -> {:reply, t, opts}
    end
  end
end
