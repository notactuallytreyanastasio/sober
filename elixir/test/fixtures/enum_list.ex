# expect: ok
# lean: check
# Enum over lists. A `[T]` state or field is a Lean `List T` and the Enum
# functions are the List ones: filter/reject are `List.filter` (reject of the
# negated predicate), map `List.map`, count `List.length` (of the filtered
# list with a predicate), any?/all? `List.any`/`List.all`, member? `∈`,
# reverse/take/drop the same names, at `l[i]?` (an Option), empty?
# `List.isEmpty`, `length` `List.length`, `hd` `List.headD` at the element
# type's default (hd raises on the BEAM, which an expression cannot),
# `tl` `List.tail` and `++` `++`. The predicate is a literal `fn x -> e end`
# or a capture `&(&1..)`, whose argument is the Lean binder `x1`. A
# comprehension `for x <- l, c, do: e` is List.map over the filtered list.
defmodule Item do
  @type t :: %__MODULE__{kind: kind(), size: non_neg_integer()}
  @type kind :: :small | :big
  defstruct kind: :small, size: 0
end

defmodule Shelf do
  use GenServer

  @type cast :: {:add, Item.t()} | :drop_first | :flip
  @type call :: {:of_kind, Item.kind()} | :sizes | :biggest | :summary | :third
  @type reply :: {:items, [Item.t()]} | {:sizes, [non_neg_integer()]} | {:n, non_neg_integer()} | {:one, Item.t()} | :none
  @type state :: [Item.t()]

  def init(l), do: {:ok, l}

  def handle_cast({:add, it}, l), do: {:noreply, l ++ [it]}
  def handle_cast(:drop_first, l), do: {:noreply, tl(l)}
  def handle_cast(:flip, l), do: {:noreply, Enum.reverse(l)}

  def handle_call({:of_kind, k}, _from, l) do
    {:reply, {:items, Enum.filter(l, &(&1.kind == k))}, l}
  end

  def handle_call(:sizes, _from, l) do
    {:reply, {:sizes, Enum.map(l, fn it -> it.size end)}, l}
  end

  # a comprehension, a reject, a count with a predicate and the boolean folds
  def handle_call(:summary, _from, l) do
    big = for it <- l, it.size > 2, do: it.size
    small = Enum.reject(l, &(&1.size > 2))
    n = Enum.count(l, fn it -> it.kind == :big end)
    if Enum.any?(l, &(&1.size > 5)) and Enum.all?(small, &(&1.size <= 2)) do
      {:reply, {:sizes, big ++ Enum.take(big, 1)}, l}
    else
      {:reply, {:n, n + length(small) + Enum.count(l)}, l}
    end
  end

  def handle_call(:biggest, _from, l) do
    if Enum.empty?(l) or Enum.member?(l, %Item{}) do
      {:reply, :none, l}
    else
      {:reply, {:one, hd(Enum.drop(l, 1))}, l}
    end
  end

  # Enum.at/2 is an Option, matched with a nil arm
  def handle_call(:third, _from, l) do
    case Enum.at(l, 2) do
      nil -> {:reply, :none, l}
      it -> {:reply, {:one, it}, l}
    end
  end
end
