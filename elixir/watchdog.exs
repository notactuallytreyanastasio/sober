# Elixir twin of Leanactors/Examples/Watchdog.lean.
# Run: elixir elixir/watchdog.exs
#
# Lean proves the watchdog never dies and a dead worker always has its
# restart in flight. Here: start, let ping/pong run, hang the worker, wait
# for the timeout to kill it, and check the watchdog restarted a new one.

Code.require_file("src/watchdog.ex", __DIR__)

{:ok, dog} = Watchdog.start_link()
send(dog, :start)
{w1, true} = :sys.get_state(dog)
true = Process.alive?(w1)
Process.sleep(50)                              # a few ping/pong rounds
{^w1, true} = :sys.get_state(dog)
{false, n} = :sys.get_state(w1)
true = n >= 1

send(w1, :hang)
# Do not poll: :sys.get_state is a message, and any message resets a
# GenServer timeout. Sleep past the 100ms timeout instead.
Process.sleep(400)
w2 =
  case :sys.get_state(dog) do
    {w2, true} when is_pid(w2) and w2 != w1 -> w2
    other -> raise "no restart: #{inspect(other)}"
  end

IO.puts("watchdog alive = #{Process.alive?(dog)}")
IO.puts("hung worker    = #{Process.alive?(w1)} (pongs before hang: #{n})")
IO.puts("new worker     = #{Process.alive?(w2)}")
if Process.alive?(dog) and not Process.alive?(w1) and Process.alive?(w2) do
  IO.puts("WATCHDOG OK: timeout killed the hung worker and a new one is running")
else
  IO.puts("WATCHDOG FAILED")
  System.halt(1)
end
