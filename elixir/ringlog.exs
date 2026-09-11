# Elixir twin of Leanactors/Examples/Ringlog.lean.
# Run: elixir elixir/ringlog.exs
#
# Lean checks that the buffer's `count` is the length of its queue and never
# exceeds `max_entries`, in every interleaving of the store, the reader and
# the environment, and proves it for every reachable configuration. Here the
# same modules run on the BEAM: entries are pushed into a buffer of three, the
# fourth drops the oldest, the reader asks for all entries and then only the
# errors through blocking calls, and a {:log, level} message makes the reader
# push an entry of its own. Matches `Ringlog.filled` and `Ringlog.read` in
# Lean (which use a cap of two, so the numbers there are one smaller).
#
# `%Entry{..}` literals are built with `struct/2`: a script is expanded before
# `Code.require_file` has run, so the struct syntax is not available here (the
# source itself uses it, and that is what the translator reads).

Code.require_file("src/ringlog.ex", __DIR__)

{:ok, log} = Ringlog.start_link(3)
{:ok, reader} = GenServer.start(Reader, 0)

# the invariant Lean proves, checked here against the real state
inv = fn ->
  st = :sys.get_state(Ringlog)
  true = st.count == length(:queue.to_list(st.entries))
  true = st.count <= st.max_entries
  st
end

entries = fn -> :queue.to_list(:sys.get_state(Ringlog).entries) end
msgs = fn -> Enum.map(entries.(), & &1.msg) end
push = fn level, msg -> GenServer.cast(Ringlog, {:push, struct(Entry, level: level, msg: msg)}) end

push.(:info, 1)
push.(:error, 2)
push.(:info, 3)
%{count: 3, max_entries: 3} = inv.()
[1, 2, 3] = msgs.()

# the fourth push drops the oldest entry and leaves the count at the cap
push.(:error, 4)
%{count: 3} = inv.()
[2, 3, 4] = msgs.()

# the calls: every entry, then only the ones of a level
[2, 3, 4] = Enum.map(GenServer.call(Ringlog, :get_entries), & &1.msg)
[2, 4] = Enum.map(GenServer.call(Ringlog, {:by_level, :error}), & &1.msg)
[3] = Enum.map(GenServer.call(Ringlog, {:by_level, :info}), & &1.msg)
[] = GenServer.call(Ringlog, {:by_level, :debug})

# the reader's blocking calls: it remembers how many entries came back
send(reader, :ask_all)
3 = :sys.get_state(reader)
send(reader, :ask_errors)
2 = :sys.get_state(reader)

# the reader pushes an entry carrying that count; the oldest is dropped again
send(reader, {:log, :warn})
2 = :sys.get_state(reader)
%{count: 3} = inv.()
[3, 4, 2] = msgs.()
[:info, :error, :warn] = Enum.map(entries.(), & &1.level)

# the defstruct defaults, which the Lean `structure` carries as field defaults
%{level: :info, msg: 0} = struct(Entry)

IO.puts("store alive = #{Process.alive?(log)}, final = #{inspect(inv.())}")
IO.puts("RINGLOG OK: count tracks the queue, the cap holds, oldest dropped, filtered calls agree")
