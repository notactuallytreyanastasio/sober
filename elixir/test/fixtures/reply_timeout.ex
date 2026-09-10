# expect: ok
# lean: check
# `{:reply, r, s, t}` sends the reply and then arms the untimed self-timer
# for :timeout, like `{:noreply, s, t}`; `:hibernate` in either form is no
# timeout and nothing the model can see.
defmodule Session do
  use GenServer

  @type msg :: :timeout | :nap
  @type call :: :touch | :peek
  @type reply :: non_neg_integer()
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_call(:touch, _from, n), do: {:reply, n, n + 1, 500}
  def handle_call(:peek, _from, n), do: {:reply, n, n, :hibernate}

  def handle_cast(:nap, n), do: {:noreply, n, :hibernate}

  def handle_info(:timeout, _), do: {:noreply, 0}
end
