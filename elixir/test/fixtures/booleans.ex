# expect: ok
# lean: check
# boolean() is Bool: true/false as patterns and as expressions, a bare Bool
# variable as a guard, and an `if` around a whole body. `{true, n}` and
# `{false, n}` together cover `:flip`, so `Flag` gets no crash clause;
# `Other` leaves its info tag without a total clause so the global catch-all
# is still reachable.
defmodule Flag do
  use GenServer

  @type msg :: :flip | {:set, boolean()} | :bump
  @type state :: {boolean(), non_neg_integer()}

  def init(s), do: {:ok, s}

  def handle_cast(:flip, {true, n}), do: {:noreply, {false, n}}
  def handle_cast(:flip, {false, n}), do: {:noreply, {true, n}}
  def handle_cast({:set, b}, {_, n}), do: {:noreply, {b, n}}

  def handle_cast(:bump, {on, n}) when on, do: {:noreply, {on, n + 1}}
  def handle_cast(:bump, {on, n}) do
    if n > 0 do
      {:noreply, {on, n - 1}}
    else
      {:noreply, {true, 0}}
    end
  end
end

defmodule Other do
  use GenServer

  @type msg :: :other
  @type state :: boolean()

  def init(s), do: {:ok, s}

  def handle_info(:other, b), do: {:noreply, b}
end
