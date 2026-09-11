# Elixir twin of Leanactors/Examples/Feed.lean.
# Run: elixir elixir/feed.exs
#
# The publisher broadcasts {:post, n} on "feed" through the local PubSub
# twin (src/pubsub.ex, the same function shapes as Phoenix.PubSub); two
# subscribers subscribe in init/1 and count posts, one leaves. Matches
# `Feed.script` in Lean: publisher 5, subscriber a {3, false}, subscriber
# b {5, true}, only b still subscribed.

Code.require_file("src/pubsub.ex", __DIR__)
Code.require_file("src/feed.ex", __DIR__)

{:ok, _bus} = PubSub.start_link()
{:ok, pub} = Publisher.start_link()

send(pub, :start)
# queued behind :start, so both subscribers exist (start_link is synchronous,
# so a subscribed before b was spawned)
0 = :sys.get_state(pub)
[a, b] = PubSub.subscribers(PubSub, "feed")

for _ <- 1..3, do: send(pub, :tick)
# each broadcast is a call to PubSub that returns after the sends, so the
# three posts are in the subscribers' mailboxes before get_state is queued
3 = :sys.get_state(pub)
{3, true} = :sys.get_state(a)
{3, true} = :sys.get_state(b)

send(a, :leave)
{3, false} = :sys.get_state(a)
[^b] = PubSub.subscribers(PubSub, "feed")

for _ <- 1..2, do: send(pub, :tick)
5 = :sys.get_state(pub)
{3, false} = :sys.get_state(a)
{5, true} = :sys.get_state(b)

IO.puts("publisher = 5, a = #{inspect(:sys.get_state(a))}, b = #{inspect(:sys.get_state(b))}, subscribers = [b]")
IO.puts("FEED OK: every subscriber saw a prefix of the posts; leaving stops the feed")
