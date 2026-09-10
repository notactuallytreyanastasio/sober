# A cache with a time-to-live: a raw process that stores one value, answers
# reads, and forgets the value when no message arrives within the TTL.
# A reader asks it for the value. Executed by ../ttl.exs, translated by
# ../to_lean.exs.
#
# Translator conventions for after, registration and raise:
#   receive do ... after t -> body end   -> a model-only message :after_run
#                                           armed as an untimed self-timer on
#                                           every re-entry of the receive; the
#                                           after body handles it (a stale
#                                           timer may fire late in the model)
#   Process.register(pid, __MODULE__)    -> Cache is the constant pid `cache`
#                                           (no --pid flag needed)
#   raise ... as the last statement      -> the process exits with reason error,
#                                           state unchanged

defmodule Cache do
  @type msg :: {:put, non_neg_integer()} | {:get, pid()}
  @type state :: non_neg_integer() | nil

  def start do
    pid = spawn(__MODULE__, :run, [nil])
    Process.register(pid, __MODULE__)
    pid
  end

  @spec run(state()) :: no_return()
  def run(v) do
    receive do
      {:put, 0} -> raise ArgumentError, "0 is not a cacheable value"
      {:put, x} -> run(x)
      {:get, from} ->
        send(from, {:value, v})
        run(v)
    after
      200 -> run(nil)
    end
  end
end

defmodule Reader do
  @type msg :: :ask | {:value, non_neg_integer() | nil}
  # values received
  @type state :: non_neg_integer()

  @spec run(state()) :: no_return()
  def run(n) do
    receive do
      :ask ->
        send(Cache, {:get, self()})
        run(n)
      {:value, _} -> run(n + 1)
    end
  end
end
