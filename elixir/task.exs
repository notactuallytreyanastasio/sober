# Elixir twin of Leanactors/Examples/Task.lean.
# Run: elixir elixir/task.exs
#
# Lean proves a pending job is never lost. Here the same modules run on
# the BEAM: one job completes, one worker crashes, and the caller ends with
# no pending job either way. Matches `Task.done` (results 1) and
# `Task.crashed` (results 0) in Lean.

Code.require_file("src/task.ex", __DIR__)

{:ok, caller} = Caller.start_link()

# a completed job
send(caller, :go)
{w1, 0} = :sys.get_state(caller)
send(w1, :compute)
wait = fn wait, n, pred ->
  st = :sys.get_state(caller)
  cond do
    pred.(st) -> st
    n > 0 -> Process.sleep(10); wait.(wait, n - 1, pred)
    true -> raise "timeout, state #{inspect(st)}"
  end
end
{nil, 1} = wait.(wait, 100, &match?({nil, 1}, &1))

# a crashed job
send(caller, :go)
{w2, 1} = :sys.get_state(caller)
send(w2, :crash)
{nil, 1} = wait.(wait, 100, &match?({nil, 1}, &1))

IO.puts("caller alive  = #{Process.alive?(caller)}")
IO.puts("worker1 alive = #{Process.alive?(w1)}, worker2 alive = #{Process.alive?(w2)}")
IO.puts("final state   = #{inspect(:sys.get_state(caller))}")
IO.puts("TASK OK: completed job counted, crashed job cleared by DOWN, caller alive")
