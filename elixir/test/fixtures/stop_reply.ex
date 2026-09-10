# expect: ok
# lean: check
# `{:stop, reason, reply, s}` from handle_call sends the reply and then
# exits with the reason (:normal stays normal, anything else is error).
defmodule Door do
  use GenServer

  @type call :: :close | :slam
  @type reply :: :bye
  @type state :: non_neg_integer()

  def init(n), do: {:ok, n}

  def handle_call(:close, _from, n), do: {:stop, :normal, :bye, n}
  def handle_call(:slam, _from, n), do: {:stop, :broken, :bye, n + 1}
end
