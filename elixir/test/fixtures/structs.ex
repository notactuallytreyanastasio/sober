# expect: ok
# lean: check
# Structs. `defstruct f: d, ..` with `@type t :: %__MODULE__{f: T, ..}` is a
# Lean `structure` whose fields carry the defstruct defaults; `%Mod{f: e}` is
# `({ f := e } : Mod)` (the other fields default), `x.f` is the projection and
# a pattern `%Mod{f: p}` the anonymous constructor `⟨.., p, ..⟩`, with `_` for
# every field not named and `%Mod{..} = v` binding the whole value as `v@⟨..⟩`.
# A GenServer whose `@type state` is its own struct has it flattened into the
# St constructor, one field per defstruct field: `state.f` is the part the
# clause's pattern bound to f and `%{state | f: e}` rebuilds the constructor
# with the named parts replaced.
defmodule Point do
  @type t :: %__MODULE__{x: non_neg_integer(), y: non_neg_integer(), tag: tag()}
  @type tag :: :origin | :other
  defstruct x: 0, y: 0, tag: :origin
end

defmodule Board do
  use GenServer

  @width 4

  @type t :: %__MODULE__{cur: Point.t(), moves: non_neg_integer(), width: non_neg_integer()}
  defstruct cur: %Point{}, moves: 0, width: @width

  @type cast :: {:move, Point.t()} | :home
  @type call :: :pos | :count
  @type reply :: {:at, Point.t()} | {:moves, non_neg_integer()}
  @type state :: t()

  def init(w), do: {:ok, %__MODULE__{width: w}}

  # a struct pattern in the message, with the whole value named
  def handle_cast({:move, %Point{x: 0} = p}, state) do
    {:noreply, %{state | cur: p, moves: state.moves + 1}}
  end

  def handle_cast({:move, %Point{x: x, y: y}}, state) when x < 3 do
    {:noreply, %{state | cur: %Point{x: x, y: y, tag: :other}, moves: state.moves + 1}}
  end

  # a struct pattern that names no field at all matches every Point
  def handle_cast({:move, %Point{}}, state) do
    {:noreply, %{state | moves: state.moves + 1}}
  end

  def handle_cast(:home, state), do: {:noreply, %{state | cur: %Point{}}}

  # the state pattern is itself a struct pattern
  def handle_call(:pos, _from, %__MODULE__{cur: c} = state) do
    {:reply, {:at, c}, state}
  end

  def handle_call(:count, _from, state) do
    {:reply, {:moves, state.moves + state.width}, state}
  end
end
