# Randomized differential testing: the Lean interpreter against the BEAM.
#
#   lake build replay                                  # once; .lake/build/bin/replay
#   elixir elixir/fuzz.exs --seed 1 --runs 200         # what check.sh runs
#   elixir elixir/fuzz.exs --seed 1 --only 17          # replay one run, print everything
#   elixir elixir/fuzz.exs --seed 1 --runs 50 --example ttl
#
# Every run is a random script for one example (run i is bank, ttl or
# lock as i mod 3 is 0, 1 or 2, unless --example fixes one), generated
# from the seed and the run
# number (`:rand.seed(:exsss, {seed, run, 7})`), so a failure reported as
# "seed S run N" is reproduced by `--seed S --only N`. The script is
# replayed twice: in Lean, by piping it into the `replay` executable
# (`Leanactors/Replay.lean`: `run` for the bank and the lock, `runSys`
# for the cache),
# and on the BEAM, by driving the real modules in elixir/src with the
# same messages in the same order. Both print the same observables in the
# same text form; the first byte-for-byte difference stops the fuzzer
# with the script and both outputs, exit status 1.
#
# ## Why the comparison is sound: phases
#
# The Lean side is a schedule: every `run p` is a choice. The BEAM has its
# own scheduler, so a script whose result depends on the interleaving
# would compare an interleaving Lean took with one the BEAM may not have.
# The generator therefore only builds scripts out of *phases*, each of
# which has exactly one outcome whatever the scheduler does, and the BEAM
# twin waits for each phase to complete before starting the next:
#
#   bank   cast k    k casts to the bank, then `run 0` k times. One target,
#                    one sender: per-pair FIFO on both sides.
#                    BEAM: GenServer.cast x k, then :sys.get_state(bank).
#          tick c    `send(c, :tick)`; c calls the bank, the bank replies,
#                    c resumes. At every step exactly one actor has mail.
#                    Lean: run c, run 0, run c. BEAM: send, :sys.get_state(c)
#                    (queued behind :tick, answered after the handler and
#                    its blocking call have returned).
#          audit c   two nested calls: run c, run 0, run c, run 0, run c.
#          tick2 c   two ticks at once, the second arriving while c is
#                    blocked in the first call. It is deferred (re-enqueued
#                    to self in the model, left in the mailbox by the
#                    BEAM's selective receive) and served after the reply.
#                    Both orders of the one interleaving choice (bank or
#                    client first) end in the same state, since the bank's
#                    state does not change in between.
#   ttl    put x     `send(cache, {:put, x})`, x >= 1: run 0. No sync
#                    needed: on one node a send is an immediate mailbox
#                    append, so a later message from the driver or from
#                    a process the driver messages afterwards lands behind
#                    it.
#          ask       `send(reader, :ask)`: run 1, run 0, run 1. BEAM: the
#                    reader is traced (`:erlang.trace(reader, true,
#                    [:receive])`) and the driver waits for the trace of
#                    the `{:value, v}` the cache sent back; that event is
#                    causally after the cache handled the get.
#          expire    the live timer fires: `timer <last>`, run 0. The live
#                    timer is always the last pending one (each processed
#                    message appends the next generation; firing erases
#                    one and, if live, appends). BEAM: sleep 300ms > the
#                    200ms TTL with no message in between. A second expiry
#                    in that window is unobservable (nil stays nil).
#          stale i   a stale timer fires: `timer i`, run 0, i < last. Lean
#                    only: the model claims the cache consumes and ignores
#                    it; the BEAM cancelled it when the message after it
#                    was handled, so it has no BEAM counterpart at all.
#          put0      `send(cache, {:put, 0})`, always the last phase: the
#                    cache raises and dies. BEAM: monitored, wait for DOWN.
#   lock   tick c    `send(c, :tick)` to one of three clients. What the tick
#                    does depends on the protocol state, so the generator
#                    simulates the protocol (holder, FIFO queue, each
#                    client's phase, deferred ticks) and expands the tick
#                    into the one line sequence the model can follow, plus
#                    the exact list of messages the server will receive:
#                      idle, lock free   run c, run 0, run c       -> c holds
#                      idle, lock held   run c, run 0              -> c queued,
#                                        blocked in the call
#                      waiting           run c: the tick is deferred (model:
#                                        re-enqueued by the await state; BEAM:
#                                        left in the mailbox by the call's
#                                        selective receive)
#                      holding           run c, run 0: release; then the
#                                        cascade: the next queued client n
#                                        gets the reply (run n -> holding);
#                                        if n had a deferred tick, run n x3
#                                        (tick deferred, reply, tick ->
#                                        release), run 0, and so on down
#                                        the queue.
#                    BEAM: the server is traced (`:erlang.trace(lock, true,
#                    [:receive])`); the twin waits for the simulated
#                    messages (`$gen_call acquire` from c, `$gen_cast
#                    release`) to arrive in that order, then
#                    :sys.get_state(lock) (queued behind the last one) and
#                    :sys.get_state(c) for each client the phase leaves
#                    unblocked. Each message in the cascade is causally
#                    after the server handled the previous one, so their
#                    order at the server is not the scheduler's.
#
# Restrictions and why: no phase delivers to two different processes (the
# relative order of their reactions at a shared target would be the
# scheduler's); a waiting client is ticked at most once (a second deferred
# tick would make it re-acquire right after its release, and whether that
# acquire reaches the server before the next holder's release is the
# scheduler's choice); `put 0` is terminal, because after the cache dies the
# model drops sends to pid 0 while `send(Cache, ...)` by registered name
# raises ArgumentError on the BEAM and would kill the reader on its next
# ask (registration is static in the model, a constant pid); no message
# is sent to the cache from outside except put, and to the reader except
# ask, so `values` is exactly what the reader got from the cache. The TTL
# is real time on the BEAM: a run in which the driver stalled for longer
# than half the TTL between two non-expire phases may have expired the
# cache where the script did not, so on a mismatch such a run is retried
# up to three times before it counts (reported as a timing retry).
#
# ## Observables (same text on both sides)
#
#   bank:  bank <balance> / client 1 none|some v|await / client 2 ... /
#          pending <messages left in the three mailboxes>
#   ttl:   cache none|some v|dead / reader <count> /
#          values <each value the reader received, oldest first> /
#          pending <messages left in the two mailboxes>
#   lock:  lock none|<holder> / queue <pids oldest first> /
#          client 1..3 idle|holding|waiting / pending <messages left in
#          the four mailboxes>
#
# On the BEAM the bank observables are :sys.get_state of the three
# GenServers after the final sync; the cache's value is a {:get, self()}
# from the driver (an observation that keeps the value; the model reads
# the state directly); the reader's count and values are the traced
# receives of {:value, _} (the reader's own state, `run(n)`, is not
# observable from outside; the model prints it and the count must agree
# with the mailbox observation); pending is message_queue_len.

Code.require_file("src/bank.ex", __DIR__)
Code.require_file("src/ttl.ex", __DIR__)
# lock.ex also defines a `Client`; load it under its own name.
Code.compiler_options(ignore_module_conflict: true)
{lock_mods, _} = Code.eval_string(
  File.read!(Path.join(__DIR__, "src/lock.ex"))
  |> String.replace("defmodule Client do", "defmodule LockClient do"),
  [], file: "lock.ex")
_ = lock_mods
Code.compiler_options(ignore_module_conflict: false)

defmodule Fuzz do
  @root Path.expand("..", __DIR__)
  @replay Path.join(@root, ".lake/build/bin/replay")
  # ttl.ex: `after 200`. The expire phase sleeps past it.
  @expire_sleep_ms 300
  # a non-expire phase that took longer than this may have expired the cache by itself
  @stall_ms 100

  # ── generators ──────────────────────────────────────────────────────

  def gen(:bank) do
    for _ <- 1..:rand.uniform(8) do
      case :rand.uniform(100) do
        r when r <= 50 -> {:cast, for(_ <- 1..:rand.uniform(3), do: cast_msg())}
        r when r <= 75 -> {:tick, client()}
        r when r <= 90 -> {:audit, client()}
        _ -> {:tick2, client()}
      end
    end
  end

  # `nt` is the number of pending timers in the model: 1 at the start
  # (Ttl.init arms generation 0), +1 per message the cache handles
  # (put, get), unchanged by an expiry (erase one, arm one), -1 per stale
  # firing. The live timer is index nt - 1.
  def gen(:ttl) do
    {phases, _nt} =
      Enum.map_reduce(1..:rand.uniform(8), 1, fn _, nt ->
        r = :rand.uniform(100)

        cond do
          r <= 42 -> {{:put, :rand.uniform(9)}, nt + 1}
          r <= 72 -> {:ask, nt + 1}
          r <= 86 -> {{:expire, nt - 1}, nt}
          nt >= 2 -> {{:stale, :rand.uniform(nt - 1) - 1}, nt - 1}
          true -> {:ask, nt + 1}
        end
      end)

    if :rand.uniform(4) == 1, do: phases ++ [:put0], else: phases
  end

  # Three clients. A tick is expanded through a simulation of the protocol
  # (see the header); a waiting client that already has a deferred tick is
  # never ticked again. Each phase is %{c, lines, lock, sync}: the Lean
  # lines, the messages the server will receive, the clients to sync.
  @lock_clients 3

  def gen(:lock) do
    sim = %{holder: nil, queue: [], phase: Map.new(1..@lock_clients, &{&1, :idle}), deferred: %{}}

    {phases, _sim} =
      Enum.map_reduce(1..(:rand.uniform(8) + 2), sim, fn _, sim ->
        candidates = for c <- 1..@lock_clients, not Map.has_key?(sim.deferred, c), do: c
        lock_tick(sim, Enum.random(candidates))
      end)

    phases
  end

  defp lock_tick(sim, c) do
    base = %{c: c, lines: ["deliver #{c} tick"], lock: [], sync: []}

    case sim.phase[c] do
      :idle when sim.holder == nil ->
        {%{base | lines: base.lines ++ ["run #{c}", "run 0", "run #{c}"], lock: [{:acquire, c}], sync: [c]},
         %{sim | holder: c, phase: Map.put(sim.phase, c, :holding)}}

      :idle ->
        {%{base | lines: base.lines ++ ["run #{c}", "run 0"], lock: [{:acquire, c}]},
         %{sim | queue: sim.queue ++ [c], phase: Map.put(sim.phase, c, :waiting)}}

      :waiting ->
        {%{base | lines: base.lines ++ ["run #{c}"]}, %{sim | deferred: Map.put(sim.deferred, c, true)}}

      :holding ->
        ph = %{base | lines: base.lines ++ ["run #{c}", "run 0"], lock: [{:release, c}], sync: [c]}
        lock_grant(ph, %{sim | holder: nil, phase: Map.put(sim.phase, c, :idle)})
    end
  end

  # The server just handled a release: hand the lock down the queue.
  defp lock_grant(ph, %{queue: []} = sim), do: {ph, sim}

  defp lock_grant(ph, %{queue: [n | rest]} = sim) do
    sim = %{sim | holder: n, queue: rest}

    if Map.has_key?(sim.deferred, n) do
      ph = %{
        ph
        | lines: ph.lines ++ ["run #{n}", "run #{n}", "run #{n}", "run 0"],
          lock: ph.lock ++ [{:release, n}],
          sync: ph.sync ++ [n]
      }

      lock_grant(ph, %{sim | holder: nil, phase: Map.put(sim.phase, n, :idle), deferred: Map.delete(sim.deferred, n)})
    else
      {%{ph | lines: ph.lines ++ ["run #{n}"], sync: ph.sync ++ [n]}, %{sim | phase: Map.put(sim.phase, n, :holding)}}
    end
  end

  defp cast_msg do
    if :rand.uniform(2) == 1,
      do: {:deposit, :rand.uniform(21) - 1},
      else: {:withdraw, :rand.uniform(31) - 1}
  end

  defp client, do: :rand.uniform(2)

  # ── the Lean rendering of a phase list ───────────────────────────────

  def script(example, phases) do
    lines = ["example #{example}" | Enum.flat_map(phases, &lines/1)]
    Enum.join(lines, "\n") <> "\nend\n"
  end

  defp lines({:cast, msgs}) do
    Enum.map(msgs, fn {tag, n} -> "deliver 0 #{tag} #{n}" end) ++
      List.duplicate("run 0", length(msgs))
  end

  defp lines({:tick, c}), do: ["deliver #{c} tick", "run #{c}", "run 0", "run #{c}"]

  defp lines({:tick2, c}),
    do: [
      "deliver #{c} tick",
      "deliver #{c} tick",
      "run #{c}",
      "run 0",
      "run #{c}",
      "run #{c}",
      "run #{c}",
      "run 0",
      "run #{c}"
    ]

  defp lines({:audit, c}),
    do: ["deliver #{c} audit", "run #{c}", "run 0", "run #{c}", "run 0", "run #{c}"]

  defp lines({:put, x}), do: ["deliver 0 put #{x}", "run 0"]
  defp lines(:ask), do: ["deliver 1 ask", "run 1", "run 0", "run 1"]
  defp lines({:expire, i}), do: ["timer #{i}", "run 0"]
  defp lines({:stale, i}), do: ["timer #{i}", "run 0"]
  defp lines(:put0), do: ["deliver 0 put 0", "run 0"]
  defp lines(%{lines: l}), do: l

  # ── Lean: the replay executable with the script on stdin ────────────

  def lean(script) do
    port =
      Port.open({:spawn_executable, @replay}, [:binary, :exit_status, :stderr_to_stdout, :use_stdio])

    Port.command(port, script)
    collect(port, "")
  end

  defp collect(port, acc) do
    receive do
      {^port, {:data, d}} -> collect(port, acc <> d)
      {^port, {:exit_status, s}} -> {s, acc}
    after
      5000 ->
        Port.close(port)
        {:timeout, acc}
    end
  end

  # ── BEAM twins ──────────────────────────────────────────────────────

  # Returns {output, max_stall_ms}.
  def beam(:bank, phases) do
    {:ok, bank} = Bank.start_link(10)
    {:ok, c1} = Client.start_link()
    {:ok, c2} = Client.start_link()
    pid = fn 1 -> c1; 2 -> c2 end

    Enum.each(phases, fn
      {:cast, msgs} ->
        Enum.each(msgs, &GenServer.cast(bank, &1))
        :sys.get_state(bank)

      {:tick, c} ->
        send(pid.(c), :tick)
        :sys.get_state(pid.(c))

      {:tick2, c} ->
        send(pid.(c), :tick)
        send(pid.(c), :tick)
        :sys.get_state(pid.(c))

      {:audit, c} ->
        send(pid.(c), :audit)
        :sys.get_state(pid.(c))
    end)

    b = :sys.get_state(bank)
    s1 = :sys.get_state(c1)
    s2 = :sys.get_state(c2)
    pending = Enum.sum(for p <- [bank, c1, c2], do: queue_len(p))
    out = "bank #{b}\nclient 1 #{fmt_seen(s1)}\nclient 2 #{fmt_seen(s2)}\npending #{pending}\n"

    GenServer.stop(c1)
    GenServer.stop(c2)
    GenServer.stop(bank)
    {out, 0}
  end

  def beam(:ttl, phases) do
    cache = Cache.start()
    reader = spawn(Reader, :run, [0])
    :erlang.trace(reader, true, [:receive])
    ref = Process.monitor(cache)

    {values, dead?, stall} =
      Enum.reduce(phases, {[], false, 0}, fn phase, {vals, dead?, stall} ->
        t0 = System.monotonic_time(:millisecond)

        {vals, dead?} =
          case phase do
            {:put, x} ->
              send(cache, {:put, x})
              {vals, dead?}

            :ask ->
              send(reader, :ask)

              v =
                receive do
                  {:trace, ^reader, :receive, {:value, v}} -> v
                after
                  1000 -> raise "ttl: the reader got no value within 1s"
                end

              {vals ++ [v], dead?}

            {:expire, _} ->
              Process.sleep(@expire_sleep_ms)
              {vals, dead?}

            {:stale, _} ->
              {vals, dead?}

            :put0 ->
              send(cache, {:put, 0})

              receive do
                {:DOWN, ^ref, :process, ^cache, _} -> :ok
              after
                1000 -> raise "ttl: the cache did not die on put 0"
              end

              {vals, true}
          end

        took = System.monotonic_time(:millisecond) - t0
        stall = if match?({:expire, _}, phase), do: stall, else: max(stall, took)
        {vals, dead?, stall}
      end)

    cache_line =
      if dead? do
        "cache dead"
      else
        send(cache, {:get, self()})

        receive do
          {:value, v} -> "cache #{fmt_seen(v)}"
        after
          1000 -> raise "ttl: no reply to the final get"
        end
      end

    wait_drained(reader, 200)
    pending = (if dead?, do: 0, else: queue_len(cache)) + queue_len(reader)

    out =
      "#{cache_line}\nreader #{length(values)}\n" <>
        Enum.join(["values" | Enum.map(values, &fmt_value/1)], " ") <> "\npending #{pending}\n"

    :erlang.trace(reader, false, [:receive])
    Process.exit(reader, :kill)

    unless dead? do
      Process.exit(cache, :kill)

      receive do
        {:DOWN, ^ref, :process, ^cache, _} -> :ok
      after
        1000 -> raise "ttl: the cache did not die on kill"
      end
    end

    wait_unregistered(Cache, 200)
    flush()
    {out, stall}
  end

  def beam(:lock, phases) do
    {:ok, lock} = Lock.start_link()
    clients = for _ <- 1..@lock_clients, do: (fn -> {:ok, c} = LockClient.start_link(); c end).()
    pid = fn i -> Enum.at(clients, i - 1) end
    num = fn p -> Enum.find_index(clients, &(&1 == p)) + 1 end
    :erlang.trace(lock, true, [:receive])

    Enum.each(phases, fn %{c: c, lock: msgs, sync: sync} ->
      send(pid.(c), :tick)
      await_lock(lock, Enum.map(msgs, fn {tag, i} -> {tag, pid.(i)} end))
      :sys.get_state(lock)
      Enum.each(sync, &:sys.get_state(pid.(&1)))
    end)

    {holder, queue} = :sys.get_state(lock)
    holder = if holder, do: num.(elem(holder, 0))
    queue = Enum.map(queue, &num.(elem(&1, 0)))

    client_lines =
      for i <- 1..@lock_clients do
        st = if i in queue, do: :waiting, else: :sys.get_state(pid.(i))
        "client #{i} #{st}"
      end

    pending = Enum.sum(for p <- [lock | clients], do: queue_len(p))

    out =
      Enum.join(
        ["lock #{holder || "none"}", Enum.join(["queue" | Enum.map(queue, &Integer.to_string/1)], " ")] ++
          client_lines ++ ["pending #{pending}"],
        "\n"
      ) <> "\n"

    :erlang.trace(lock, false, [:receive])
    # a queued client is blocked in its call and cannot be stopped; unlink, then kill
    Enum.each(clients, fn c ->
      Process.unlink(c)
      Process.exit(c, :kill)
    end)

    GenServer.stop(lock)
    wait_unregistered(Lock, 200)
    flush()
    {out, 0}
  end

  # Wait for the server to receive exactly these messages, in order. Its
  # own :sys traffic (the driver's get_state) is skipped; anything else
  # arriving out of turn is a protocol mismatch.
  defp await_lock(_lock, []), do: :ok

  defp await_lock(lock, [{tag, from} | rest] = expected) do
    receive do
      {:trace, ^lock, :receive, {:system, _, _}} ->
        await_lock(lock, expected)

      {:trace, ^lock, :receive, {:"$gen_call", {^from, _}, :acquire}} when tag == :acquire ->
        await_lock(lock, rest)

      {:trace, ^lock, :receive, {:"$gen_cast", {:release, ^from}}} when tag == :release ->
        await_lock(lock, rest)

      {:trace, ^lock, :receive, other} ->
        raise "lock: the server received #{inspect(other)} while #{inspect(tag)} from #{inspect(from)} was expected"
    after
      1000 -> raise "lock: the server did not receive #{inspect(tag)} from #{inspect(from)} within 1s"
    end
  end

  defp fmt_seen(nil), do: "none"
  defp fmt_seen(v), do: "some #{v}"
  defp fmt_value(nil), do: "none"
  defp fmt_value(v), do: Integer.to_string(v)

  defp queue_len(p) do
    case Process.info(p, :message_queue_len) do
      {:message_queue_len, n} -> n
      nil -> 0
    end
  end

  defp wait_drained(_p, 0), do: :ok

  defp wait_drained(p, n) do
    if queue_len(p) == 0 do
      :ok
    else
      Process.sleep(1)
      wait_drained(p, n - 1)
    end
  end

  defp wait_unregistered(name, 0), do: raise("#{inspect(name)} is still registered")

  defp wait_unregistered(name, n) do
    if Process.whereis(name) == nil do
      :ok
    else
      Process.sleep(1)
      wait_unregistered(name, n - 1)
    end
  end

  defp flush do
    receive do
      _ -> flush()
    after
      0 -> :ok
    end
  end

  # ── driver ──────────────────────────────────────────────────────────

  def main(argv) do
    {opts, _, _} =
      OptionParser.parse(argv,
        switches: [seed: :integer, runs: :integer, example: :string, only: :integer, verbose: :boolean]
      )

    seed = Keyword.get(opts, :seed, 1)
    runs = Keyword.get(opts, :runs, 200)
    only = Keyword.get(opts, :only)
    verbose? = Keyword.get(opts, :verbose, false) or only != nil

    fixed =
      case Keyword.get(opts, :example) do
        nil -> nil
        "bank" -> :bank
        "ttl" -> :ttl
        "lock" -> :lock
        other -> die("unknown example #{other} (bank, ttl or lock)")
      end

    unless File.exists?(@replay) do
      die("#{@replay} not found; run `lake build replay` first")
    end

    # the cache's `raise` on put 0 would otherwise log a crash report per run
    Logger.configure(level: :none)

    ids = if only, do: [only], else: Enum.to_list(0..(runs - 1)//1)
    IO.puts("fuzz: seed #{seed}, #{length(ids)} runs, replay = #{Path.relative_to(@replay, @root)}")
    t0 = System.monotonic_time(:millisecond)

    stats =
      Enum.reduce(ids, %{bank: 0, ttl: 0, lock: 0, phases: 0, expiries: 0, crashes: 0, retries: 0}, fn i, st ->
        example = fixed || Enum.at([:bank, :ttl, :lock], rem(i, 3))
        :rand.seed(:exsss, {seed, i, 7})
        phases = gen(example)
        script = script(example, phases)
        {status, lean_out} = lean(script)

        if status != 0 do
          report(seed, i, example, script, lean_out, "(replay exited with #{inspect(status)})", 0)
        end

        retries = run_beam(seed, i, example, phases, script, lean_out, 0)

        if verbose? do
          IO.puts("--- run #{i} (#{example}), #{length(phases)} phases#{retry_note(retries)}")
          IO.write(script)
          IO.puts("--- observables (Lean = BEAM)")
          IO.write(lean_out)
        end

        %{
          st
          | example => st[example] + 1,
            phases: st.phases + length(phases),
            expiries: st.expiries + Enum.count(phases, &match?({:expire, _}, &1)),
            crashes: st.crashes + Enum.count(phases, &(&1 == :put0)),
            retries: st.retries + retries
        }
      end)

    secs = Float.round((System.monotonic_time(:millisecond) - t0) / 1000, 1)

    IO.puts(
      "fuzz OK: seed #{seed}, #{length(ids)} scripts (#{stats.bank} bank, #{stats.ttl} ttl, #{stats.lock} lock), " <>
        "#{stats.phases} phases, #{stats.expiries} expiries, #{stats.crashes} crashes, " <>
        "#{stats.retries} timing retries, Lean and BEAM agree, #{secs}s"
    )
  end

  # Runs the BEAM twin and compares. Returns the number of timing retries
  # it took; halts on a real mismatch.
  defp run_beam(seed, i, example, phases, script, lean_out, attempt) do
    {beam_out, stall} =
      try do
        beam(example, phases)
      rescue
        e -> {"(BEAM twin failed: #{Exception.message(e)})\n", 0}
      end

    cond do
      beam_out == lean_out ->
        attempt

      example == :ttl and stall > @stall_ms and attempt < 3 ->
        IO.puts("run #{i}: mismatch after a #{stall}ms stall between phases (TTL 200ms); retrying")
        run_beam(seed, i, example, phases, script, lean_out, attempt + 1)

      true ->
        report(seed, i, example, script, lean_out, beam_out, attempt)
    end
  end

  defp retry_note(0), do: ""
  defp retry_note(n), do: ", #{n} timing retries"

  defp report(seed, i, example, script, lean_out, beam_out, retries) do
    IO.puts("MISMATCH: seed #{seed} run #{i} (#{example})#{retry_note(retries)}")
    IO.puts("reproduce: elixir elixir/fuzz.exs --seed #{seed} --only #{i}")
    IO.puts("--- script (stdin of #{Path.relative_to(@replay, @root)})")
    IO.write(script)
    IO.puts("--- Lean")
    IO.write(lean_out)
    IO.puts("--- BEAM")
    IO.write(beam_out)
    System.halt(1)
  end

  defp die(msg) do
    IO.puts(:stderr, "fuzz: " <> msg)
    System.halt(1)
  end
end

Fuzz.main(System.argv())
