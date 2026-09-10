# Elixir twin of Leanactors/Examples/Supervisor.lean.
# Run: elixir elixir/supervisor.exs
#
# Lean proves `supervisor_alive` and `restart_in_flight` for the translated
# model. Here we run the same modules on the BEAM, crash the worker, and
# check the supervisor survived and restarted it. Matches `Supervisor.trace`
# in Lean: after start, job, crash, the restart count is 1 and the child is
# a new live pid.

Code.require_file("src/supervisor.ex", __DIR__)

{:ok, sup} = Sup.start_link()
send(sup, :start)
{child1, 0} = :sys.get_state(sup)
true = Process.alive?(child1)

# The worker is a raw process (no :sys.get_state); a job must leave it alive.
send(child1, :job)
Process.sleep(10)
true = Process.alive?(child1)

ref = Process.monitor(child1)
send(child1, :crash)
receive do
  {:DOWN, ^ref, :process, ^child1, _} -> :ok
after 1000 -> raise "worker did not die"
end

# The EXIT signal reaches the supervisor asynchronously; wait for the restart.
wait = fn wait, n ->
  case :sys.get_state(sup) do
    {c, 1} when is_pid(c) and c != child1 -> c
    _ when n > 0 -> Process.sleep(10); wait.(wait, n - 1)
    other -> raise "no restart: #{inspect(other)}"
  end
end
child2 = wait.(wait, 100)

IO.puts("supervisor alive = #{Process.alive?(sup)}")
IO.puts("old child alive  = #{Process.alive?(child1)}")
IO.puts("new child alive  = #{Process.alive?(child2)}")
IO.puts("restarts         = #{elem(:sys.get_state(sup), 1)}")

if Process.alive?(sup) and not Process.alive?(child1) and Process.alive?(child2) do
  IO.puts("RESTART OK: supervisor survived the crash and restarted the worker")
else
  IO.puts("RESTART FAILED")
  System.halt(1)
end
