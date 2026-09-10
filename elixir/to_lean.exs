# Translate typespec-annotated GenServer modules into a Lean actor model.
#
#   elixir elixir/to_lean.exs SRC.ex NAMESPACE [--pid Module=const ...] > OUT.lean
#
# Supported subset (anything else is a hard error):
#   @type msg   :: union of atoms and tagged tuples {:tag, T...}
#   @type state :: T, where T is pid(), integer(), non_neg_integer(),
#                  [T], T | nil, a union of atoms, a tuple, or a local type()
#   @type call  :: (optional) union like msg; each becomes a Msg constructor
#                  with a leading `from : Pid` (the caller)
#   @type cast  :: (optional) union like msg, declaring the module's cast tags
#   @type info  :: (optional) union like msg, declaring the module's info tags
#                  (msg may be omitted when cast, info or call is declared)
#   @type reply :: (optional) the reply type; becomes Msg constructor `reply`
#   handle_cast/2, handle_info/2, handle_call/3 clauses, optional `when`
#   guard, body = zero or more send/2 or GenServer.cast/2 calls followed by
#   {:noreply, e} or (handle_call only) {:reply, r, e}; `if`/`case` are
#   allowed around whole bodies.
#   init/1: `def init(p), do: {:ok, e}` (or the block form whose other
#   statements are all `Process.flag(:trap_exit, true)`), where p is a
#   variable or a tuple of variables and e is a pure expression of p. At
#   `{:ok, pid} = GenServer.start[_link](Mod, arg)` the child's state is e
#   with p bound to arg (positionally when p is a tuple and arg a tuple
#   literal). A module without init/1 gets the `use GenServer` default,
#   the identity.
#   A statement `v = GenServer.call(Mod, m)` splits the clause: everything
#   before it runs, the request is sent, and the actor enters a generated
#   await state <mod>_await<i> (capturing the variables the rest needs).
#   A second clause resumes on `reply v`. Any other message that arrives
#   while awaiting is re-enqueued to self, encoding selective receive.
#   Raw processes: instead of callbacks a module may define exactly one loop
#   `def run(state) do receive do pat [when g] -> body ... end end` (any
#   name). Each receive clause is a handle_info clause with the parameter as
#   the state pattern; a body ending in `run(e)` continues with state e,
#   `exit(r)` exits with the current state, any other last expression means
#   the loop returns (exit :normal). If the receive has no catch-all clause
#   a defer clause re-enqueues unmatched messages to self: selective receive.
#   `pid = spawn(Mod, :run, [a])`, `pid = spawn_link(Mod, :run, [a])` and
#   `{pid, _ref} = spawn_monitor(Mod, :run, [a])` map to spawn/spawnLink/
#   spawnMonitor with Mod's state constructor applied to a.
#   `receive do ... after t -> body end` (one after clause, t ignored): the
#   BEAM starts the timeout when the receive is entered and a processed
#   message cancels it, so the model keeps a generation counter. The
#   module's St constructor gets a hidden trailing field `(gen : Nat)`, the
#   module gets a model-only Msg constructor `after_<loop> (a0 : Nat)`
#   carrying a generation, and `gen` is the generation of the timer armed
#   by the current receive: a spawn of the module starts the child at
#   generation 0 and arms `.sendAfter child (.after_<loop> 0)`; every
#   clause that re-enters the receive (a `loop(e)` tail, the defer clause,
#   a failed guard, the after body itself) moves to `gen + 1` and arms
#   `.sendAfter me (.after_<loop> (gen + 1))`; exit/raise/throw keep the
#   state, gen included. The after body is the clause for
#   `.after_<loop> gen'` with the loop parameter as its state, guarded by
#   `if gen' = gen then <body> else (<state>, [])` (Lean has no non-linear
#   patterns): a message of the current generation runs the after body, a
#   stale one (an older generation, cancelled on the BEAM) is consumed and
#   ignored, never deferred. Timers are still untimed (any pending timer
#   may fire at any step), but a fired timer only acts if no message has
#   been processed since it was armed, which is exactly the BEAM's rule.
#   `gen` is reserved in such a module (a source variable of that name is
#   an error) and a blocking call inside such a loop is not supported.
#   A body whose last statement is `raise ...` or `throw ...` (any
#   arguments) exits the process with reason error, keeping the current
#   state, like `exit/1`; a raise or throw anywhere else is an error.
#   Exit reasons (`{:stop, r, s}`, `exit(r)`, `Process.exit(p, r)`): :normal
#   is `.normal`, :kill is `.kill` (untrappable: `Process.exit(p, :kill)`
#   kills p even if it traps, and p's links see error), anything else is
#   `.error`.
#
# Registered names: `send(Mod, m)`, `GenServer.cast(Mod, m)` and
#   `GenServer.call(Mod, m)` need a constant pid for Mod. With `--pid`
#   flags the map is exactly those flags. Without any, it is derived from
#   the source: `GenServer.start_link/start(_, _, name: N)` and
#   `Process.register(_, N)` anywhere in a module register N (__MODULE__,
#   an alias or an atom) as the constant N lowercased (Cache -> cache).
#   Atom names may be used as send/cast targets (`send(:cache, m)`).
#
# Output shape: every file becomes one `def beh : EBehavior St Msg` over
#   `Leanactors.Sys`, whose clauses are `| me, fresh, <state>, <msg> => (state,
#   [effects])` (`me` and `fresh` are `_` when unused) and whose sends are
#   `.send to msg` effects, plus a `def sig : Signals St Msg` record: `traps`
#   is true exactly for the modules that call `Process.flag(:trap_exit, true)`,
#   `exitMsg` is `.EXIT p r` when some module declares `{:EXIT, pid(), term()}`
#   and otherwise a total placeholder (the first nullary Msg constructor, or
#   the first constructor applied to default arguments) that is never used
#   because nobody traps, and `downMsg` is present when some module declares
#   `{:DOWN, ...}`. A source that only sends is thus a message-only
#   `EBehavior`; the hand models keep a plain `Behavior` and prove
#   `Gen.X.beh = lift beh` (see `lift` and `runE_lift` in Leanactors/Sys.lean).
#
# Unhandled messages: a GenServer with no matching handle_cast/handle_call
#   clause dies with FunctionClauseError, so for every cast or call tag of a
#   module whose clauses do not cover it exhaustively a crash clause
#   `| _, _, .<mod> s_0 .., .<tag> _ .. => (state, [.exit .error])` is
#   emitted; a guarded cast/call clause whose guard fails with nothing to
#   fall through to crashes the same way. Coverage is a usefulness check
#   over the rendered Lean patterns (a pid-narrowed variable renders as
#   `(some w)` and leaves `none` uncovered; `true`/`false`, `none`/`some`,
#   `[]`/`::` and the alternatives of a generated enum together cover a
#   field; integer literals never do), and a module all of whose tags are
#   covered or crash gets no defer clause and does not need the global
#   catch-all, which Lean would reject as redundant. Unmatched handle_info messages are
#   ignored, as on the BEAM. Message kinds: a tag declared under @type call
#   is a call tag, under @type cast a cast tag and under @type info an info
#   tag, whether or not any clause mentions it, so a cast or call tag with
#   no clause at all gets a crash clause and an info tag with no clause is
#   ignored; a tag under @type msg is a cast or an info tag, decided by the
#   callback that handles it (a msg tag no clause mentions is not classified
#   and gets no crash clause). A tag declared in two of msg/cast/info/call,
#   a clause whose callback kind differs from the tag's declared kind (a
#   handle_cast clause for an info tag), a msg tag handled by two kinds, and
#   @type cast or call in a raw process are errors. Clauses are emitted per
#   module in source order except
#   that handle_info clauses come after the handle_cast/handle_call clauses
#   and the crash clauses, so an info catch-all does not shadow a crash.
#
# The @type declarations are the type oracle: they decide when a pattern
# variable at an `Option` position needs `some`, when `nil` is `none`, and
# what the Lean inductives look like. This is the point where Elixir's
# gradual types and Lean's dependent types meet.

defmodule ToLean do
  defmodule Ctx do
    defstruct types: %{}, msg_ctors: [], st_ctors: [], pids: %{}, enums: %{}, ns: "Gen", warnings: [],
              extra: [], awaits: %{}, reply_type: nil, traps: %{}, pid_vars: [],
              covered: [], inits: %{}, mods: [], kinds: %{}, loops: %{}, defers: [], afters: %{}
  end

  # ---------- entry ----------

  def main([src, ns | rest]) do
    pids =
      rest
      |> Enum.chunk_every(2)
      |> Enum.flat_map(fn
        ["--pid", kv] -> [kv |> String.split("=") |> List.to_tuple()]
        _ -> []
      end)
      |> Map.new()

    {:ok, ast} = src |> File.read!() |> Code.string_to_quoted(columns: false)
    mods = for {:defmodule, _, [{:__aliases__, _, [name]}, [do: body]]} <- top(ast), do: {name, stmts(body)}
    # registered names: the --pid flags if any are given, else derived from
    # the source (name: __MODULE__ in start_link/start, Process.register/2)
    pids = if map_size(pids) == 0, do: register_names(mods), else: pids
    ctx = %Ctx{ns: ns, pids: pids}
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_types(c, name, body) end)
    clauses = for {name, body} <- mods, cl <- ordered(clauses(name, body)), do: cl
    traps = for {name, body} <- mods, traps?(body), into: %{}, do: {name, true}
    inits = for {name, body} <- mods, init = init_of(name, body), init != nil, into: %{}, do: {name, init}
    # raw receive loops: module -> loop function; those without a catch-all
    # clause defer (re-enqueue) unmatched messages; those with an `after`
    # clause arm a self-timer for the message after_<loop>
    loops = for {name, body} <- mods, {fname, _, _, _} <- [loop_of(body)], into: %{}, do: {name, fname}
    afters = for {name, body} <- mods, {fname, _, _, ab} <- [loop_of(body)], ab != nil, into: %{}, do: {name, after_tag(fname)}
    defers =
      for {name, _} <- loops,
          not Enum.any?(clauses, fn cl -> cl.mod == name and cl.guard == nil and bare?(cl.mpat) end),
          do: name
    ctx = %{ctx | traps: traps, inits: inits, mods: Enum.map(mods, &elem(&1, 0)),
                  loops: loops, defers: defers, afters: afters}
    # a raw process has no handle_cast/handle_call: its messages are all info
    for {name, _} <- loops, kt <- [:cast, :call], Map.has_key?(ctx.types, {name, kt}),
        do: fail("#{name} is a raw process (receive loop) and cannot declare @type #{kt}")
    ctx = %{ctx | kinds: classify(ctx, clauses)}
    if map_size(traps) > 0 and not List.keymember?(ctx.msg_ctors, :EXIT, 0),
      do: fail("a trapping module must declare {:EXIT, pid(), term()} in @type msg")
    {out, ctx} = render(ctx, clauses)
    IO.puts(out)
    Enum.each(ctx.warnings, &IO.puts(:stderr, "warning: " <> &1))
  end

  def main(_), do: IO.puts(:stderr, "usage: to_lean.exs SRC.ex NAMESPACE [--pid Mod=const]")

  # BEAM dispatch keys on the callback, not the tag: handle_cast, handle_call
  # and handle_info are separate functions. The Lean match is one function,
  # so a module's handle_info clauses go after its cast/call clauses (and
  # after the crash clauses inserted between them), each group in source order.
  defp ordered(clauses) do
    {ci, info} = Enum.split_with(clauses, &(&1.kind != :handle_info))
    ci ++ info
  end

  # the @type unions that declare message tags, with the callback kind each fixes
  @kind_decls [msg: nil, cast: :handle_cast, info: :handle_info, call: :handle_call]

  # Which callback handles each tag, keyed {module, tag}. The declarations
  # come first: every @type call alternative is a call tag, @type cast a cast
  # tag and @type info an info tag, whether or not a clause mentions it (a
  # tag under two of msg/cast/info/call is an error). @type msg tags are
  # cast-or-info, decided by the clauses. Then the clauses: a tag whose
  # declared kind differs from the clause's callback is an error, and so is
  # a msg tag handled by two kinds in one module, which would need two Lean
  # clauses for one Msg constructor.
  defp classify(ctx, clauses) do
    declared =
      for mod <- ctx.mods, {name, kind} <- @kind_decls, {:ok, t} <- [Map.fetch(ctx.types, {mod, name})],
          alt <- union(t), reduce: %{} do
        acc ->
          key = {mod, tag_of(alt)}
          case Map.fetch(acc, key) do
            {:ok, {other, _}} -> fail("message tag #{tag_of(alt)} in #{mod} is declared under both @type #{other} and @type #{name}")
            :error -> Map.put(acc, key, {name, kind})
          end
      end
    from_decls = for {key, {_, kind}} <- declared, kind != nil, into: %{}, do: {key, kind}
    from_clauses =
      for cl <- clauses, not bare?(cl.mpat), do: {{cl.mod, elem(msg_shape(cl.mpat), 0)}, cl.kind}
    Enum.reduce(from_clauses, from_decls, fn {{mod, tag} = key, kind}, acc ->
      case Map.fetch(acc, key) do
        {:ok, ^kind} -> acc
        {:ok, other} ->
          case Map.get(declared, key) do
            {name, ^other} -> fail("message tag #{tag} in #{mod} is declared under @type #{name} but handled by #{kind}")
            _ -> fail("message tag #{tag} in #{mod} is handled by both #{other} and #{kind}")
          end
        :error -> Map.put(acc, key, kind)
      end
    end)
  end

  defp traps?(body) do
    {_, found} = Macro.prewalk({:__block__, [], body}, false, fn
      {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  # Registered names derived from the source (used when no --pid flag is
  # given): `GenServer.start_link/start(_, _, name: N)` and
  # `Process.register(_, N)` anywhere in a module, where N is __MODULE__
  # (that module), an alias or an atom. The Lean constant is N lowercased.
  defp register_names(mods) do
    for {mod, body} <- mods, name <- registered_in(mod, body), into: %{}, do: {name, String.downcase(name)}
  end

  defp registered_in(mod, body) do
    {_, names} = Macro.prewalk({:__block__, [], body}, [], fn
      {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [_, _, opts]} = n, acc when f in [:start_link, :start] and is_list(opts) ->
        case List.keyfind(opts, :name, 0) do
          {:name, x} -> {n, [reg_name(mod, x) | acc]}
          nil -> {n, acc}
        end
      {{:., _, [{:__aliases__, _, [:Process]}, :register]}, _, [_, x]} = n, acc -> {n, [reg_name(mod, x) | acc]}
      n, acc -> {n, acc}
    end)
    Enum.reverse(names)
  end

  defp reg_name(mod, {:__MODULE__, _, _}), do: Atom.to_string(mod)
  defp reg_name(_mod, {:__aliases__, _, [m]}), do: Atom.to_string(m)
  defp reg_name(_mod, a) when is_atom(a) and a not in [nil, true, false], do: Atom.to_string(a)
  defp reg_name(mod, x), do: fail("#{mod}: unsupported registered name #{Macro.to_string(x)}")

  # the Lean constant for a registered name (an alias `Mod` or an atom `:name`)
  defp pid_const(ctx, name) do
    Map.get(ctx.pids, Atom.to_string(name)) ||
      fail("no registered name for #{name}: start it with name: __MODULE__, Process.register/2 it, or pass --pid #{name}=const")
  end

  # the model-only message a receive loop with `after` sends itself
  defp after_tag(fname), do: :"after_#{fname}"

  # `init/1` as a pure state expression of its parameter: {param_pattern, expr}.
  # Accepted: `def init(p), do: {:ok, e}` or a block whose only other
  # statements are `Process.flag(:trap_exit, true)`. nil when undefined
  # (the `use GenServer` default init is the identity).
  defp init_of(mod, body) do
    case for {:def, _, [{:init, _, [p]}, [do: b]]} <- body, do: {p, b} do
      [] -> nil
      [{p, b}] ->
        {flags, [last]} = Enum.split(stmts(b), -1)
        Enum.each(flags, fn
          {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} -> :ok
          other -> fail("#{mod}.init/1: unsupported statement #{Macro.to_string(other)}")
        end)
        e = case last do
          {:ok, e} -> e
          other -> fail("#{mod}.init/1 must end in {:ok, state}, got #{Macro.to_string(other)}")
        end
        params = init_params(mod, p)
        Enum.each(free_vars(e), fn v ->
          v in params || fail("#{mod}.init/1: state expression uses #{v}, which is not a parameter")
        end)
        {_, selfs} = Macro.prewalk(e, false, fn {:self, _, []} = n, _ -> {n, true}; n, a -> {n, a} end)
        selfs && fail("#{mod}.init/1: self() in the initial state is not supported")
        {p, e}
      _ -> fail("#{mod}.init/1 must have exactly one clause")
    end
  end

  # the variables bound by an init parameter pattern (a variable or a tuple of variables)
  defp init_params(_mod, {v, _, nil}) when is_atom(v), do: [Atom.to_string(v)]
  defp init_params(mod, {a, b}), do: init_params(mod, {:{}, [], [a, b]})
  defp init_params(mod, {:{}, _, xs}), do: Enum.flat_map(xs, fn
    {v, _, nil} when is_atom(v) -> [Atom.to_string(v)]
    other -> fail("#{mod}.init/1: unsupported parameter pattern #{Macro.to_string(other)}")
  end)
  defp init_params(mod, p), do: fail("#{mod}.init/1: unsupported parameter pattern #{Macro.to_string(p)}")

  # The child's initial state at a spawn site: Mod.init's state expression
  # with the parameter bound to the spawn argument, rendered in the parent's
  # environment. A variable parameter is bound to the whole argument; a tuple
  # parameter to the parts of a tuple literal, positionally.
  defp child_state(ctx, env, child, arg, cctor, cfields) do
    case Map.get(ctx.inits, child) do
      nil -> state_expr(env, arg, cctor, cfields)
      {param, e} ->
        binds =
          case {param, arg} do
            {{v, _, nil}, _} when is_atom(v) -> [{param, arg}]
            {{a, b}, {x, y}} -> [{a, x}, {b, y}]
            {{:{}, _, ps}, {:{}, _, xs}} when length(ps) == length(xs) -> Enum.zip(ps, xs)
            {{:{}, _, ps}, {x, y}} when length(ps) == 2 -> Enum.zip(ps, [x, y])
            {{a, b}, {:{}, _, [x, y]}} -> [{a, x}, {b, y}]
            _ -> fail("#{child}.init/1 parameter #{Macro.to_string(param)} cannot be bound to spawn argument #{Macro.to_string(arg)}")
          end
          |> Enum.flat_map(fn
            {{v, _, nil}, x} when is_atom(v) -> [{v, x}]
            {p, _} -> fail("#{child}.init/1: unsupported parameter pattern #{Macro.to_string(p)}")
          end)
          |> Map.new()
        bound = Macro.postwalk(e, fn
          {v, _, nil} = n when is_atom(v) -> Map.get(binds, v, n)
          n -> n
        end)
        state_expr(env, bound, cctor, cfields)
    end
  end

  defp top({:__block__, _, xs}), do: xs
  defp top(x), do: [x]
  defp stmts({:__block__, _, xs}), do: xs
  defp stmts(x), do: [x]

  # ---------- types ----------

  # Local @type declarations, keyed {module, name}
  defp collect_types(ctx, mod, body) do
    Enum.reduce(body, ctx, fn
      {:@, _, [{:type, _, [{:"::", _, [{tname, _, _}, t]}]}]}, c ->
        put_in(c.types[{mod, tname}], t)
      _, c -> c
    end)
    |> then(fn c ->
      # the msg, cast and info unions contribute constructors (msg may be
      # omitted when another of them, or call, is declared); state
      # contributes one St constructor
      alts = for name <- [:msg, :cast, :info], {:ok, t} <- [Map.fetch(c.types, {mod, name})], alt <- union(t), do: alt
      if alts == [] and not Map.has_key?(c.types, {mod, :call}),
        do: fail("#{mod} declares no messages: add @type msg (or @type cast, info, call)")
      c = Enum.reduce(alts, c, fn alt, cc -> add_msg_ctor(cc, mod, alt) end)
      # a receive loop with `after` gets a model-only self-timer message
      # carrying a generation, and a hidden trailing `gen` field on its state
      {after?, c} =
        case loop_of(body) do
          {fname, _, _, ab} when ab != nil ->
            {true, add_msg_ctor(c, mod, {after_tag(fname), {:non_neg_integer, [], []}})}
          _ -> {false, c}
        end
      c =
        case Map.fetch(c.types, {mod, :call}) do
          {:ok, call} -> Enum.reduce(union(call), c, fn alt, cc -> add_msg_ctor(cc, mod, alt, [{"from", "Pid"}]) end)
          :error -> c
        end
      c =
        case Map.fetch(c.types, {mod, :reply}) do
          {:ok, rt} ->
            lt = lean_type(c, mod, rt)
            if c.reply_type != nil and c.reply_type != lt, do: fail("modules declare different @type reply")
            %{c | reply_type: lt} |> add_msg_ctor(mod, {:reply, rt})
          :error -> c
        end
      st = Map.fetch!(c.types, {mod, :state})
      fields = state_fields(c, mod, st) ++ if(after?, do: [{"gen", "Nat"}], else: [])
      %{c | st_ctors: c.st_ctors ++ [{ctor_name(mod), fields}]}
    end)
  end

  defp tag_of(a) when is_atom(a), do: a
  defp tag_of({a, _}) when is_atom(a), do: a
  defp tag_of({:{}, _, [a | _]}) when is_atom(a), do: a
  defp tag_of(_), do: nil

  defp union({:|, _, [a, b]}), do: union(a) ++ union(b)
  defp union(t), do: [t]

  defp add_msg_ctor(ctx, mod, alt, lead \\ []) do
    {tag, args} =
      case alt do
        a when is_atom(a) -> {a, []}
        {:{}, _, [a | rest]} when is_atom(a) -> {a, rest}
        {a, b} when is_atom(a) -> {a, [b]}
        other -> fail("unsupported message alternative: #{Macro.to_string(other)}")
      end
    ltypes =
      cond do
        tag == :EXIT -> ["Pid", "Reason"]
        tag == :DOWN -> ["Pid", "Reason"]
        true -> Enum.map(lead, &elem(&1, 1)) ++ Enum.map(args, &lean_type(ctx, mod, &1))
      end
    case List.keyfind(ctx.msg_ctors, tag, 0) do
      nil -> %{ctx | msg_ctors: ctx.msg_ctors ++ [{tag, ltypes}]}
      {^tag, ^ltypes} -> ctx
      {^tag, other} -> fail("message tag #{tag} declared with shapes #{inspect(other)} and #{inspect(ltypes)}")
    end
  end

  # A state type becomes one constructor of St with positional fields.
  defp state_fields(ctx, mod, {:{}, _, ts}), do: ts |> Enum.with_index() |> Enum.map(fn {t, i} -> {"f#{i}", lean_type(ctx, mod, t)} end)
  defp state_fields(ctx, mod, {a, b}), do: state_fields(ctx, mod, {:{}, [], [a, b]})
  defp state_fields(ctx, mod, t), do: [{"s", lean_type(ctx, mod, t)}]

  # Elixir type AST -> Lean type (string)
  defp lean_type(_ctx, _mod, {:pid, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:GenServer]}, :from]}, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {:integer, _, []}), do: "Int"
  defp lean_type(_ctx, _mod, {:non_neg_integer, _, []}), do: "Nat"
  defp lean_type(_ctx, _mod, {:boolean, _, []}), do: "Bool"
  defp lean_type(ctx, mod, a) when is_atom(a) and a not in [nil, true, false], do: enum_name(ctx, mod, [a])
  defp lean_type(ctx, mod, [t]), do: "List " <> paren(lean_type(ctx, mod, t))
  defp lean_type(ctx, mod, {:|, _, _} = u) do
    alts = union(u)
    cond do
      Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil) ->
        enum_name(ctx, mod, alts)
      Enum.member?(alts, nil) ->
        case List.delete(alts, nil) do
          [t] -> "Option " <> paren(lean_type(ctx, mod, t))
          _ -> fail("only `T | nil` unions are supported, got #{Macro.to_string(u)}")
        end
      true -> fail("unsupported union #{Macro.to_string(u)}")
    end
  end
  defp lean_type(ctx, mod, {name, _, []}) when is_atom(name) do
    case Map.fetch(ctx.types, {mod, name}) do
      {:ok, t} -> named_type(ctx, mod, name, t)
      :error -> fail("unknown type #{name}() in #{mod}")
    end
  end
  defp lean_type(_ctx, _mod, t), do: fail("unsupported type #{Macro.to_string(t)}")

  # A named local type that is a union of atoms becomes a Lean enum with the
  # capitalised name; anything else is inlined.
  defp named_type(ctx, mod, name, t) do
    alts = union(t)
    if Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil),
      do: name |> Atom.to_string() |> String.capitalize(),
      else: lean_type(ctx, mod, t)
  end

  defp enum_name(ctx, mod, alts) do
    # find the @type whose union is exactly these atoms (not a message union)
    case Enum.find(ctx.types, fn {{m, n}, t} -> m == mod and n not in [:msg, :cast, :info, :call] and union(t) == alts end) do
      {{_, name}, _} -> name |> Atom.to_string() |> String.capitalize()
      nil -> fail("anonymous atom union #{inspect(alts)}; give it a @type name")
    end
  end

  defp paren(s), do: if(String.contains?(s, " "), do: "(#{s})", else: s)

  @lean_keywords ~w(from at in fun do then else if match with have show by let end where deriving open
    def theorem instance structure class inductive mutual namespace section variable universe import
    export private protected partial noncomputable abbrev macro syntax notation calc suffices obtain
    exact intro cases induction rfl)
  # Elixir variable -> Lean identifier (avoid Lean keywords)
  defp lean_ident(name), do: if(name in @lean_keywords, do: name <> "_", else: name)
  defp ctor_name(mod), do: mod |> Atom.to_string() |> String.downcase()

  # ---------- clauses ----------

  # A module is either a GenServer (handle_* callbacks) or a raw process:
  # one `def loop(state) do receive do ... end end`, whose receive clauses
  # are handle_info clauses with the parameter as the state pattern.
  defp clauses(mod, body) do
    case loop_of(body) do
      nil ->
        for {:def, _, [head, [do: b]]} <- body,
            {fname, args, guard} = head_parts(head),
            fname in [:handle_cast, :handle_info, :handle_call],
            cl = clause_of(mod, fname, args, guard, b),
            cl != nil do
          cl
        end
      {fname, param, arms, after_body} ->
        atag = if after_body, do: after_tag(fname), else: nil
        arms =
          for {:->, _, [[lhs], b]} <- arms do
            {mpat, guard} =
              case lhs do
                {:when, _, [p, g]} -> {p, g}
                p -> {p, nil}
              end
            body = loop_tail(fname, atag, b)
            %{mod: mod, kind: :handle_info, mpat: mpat, spat: prune_param(param, body, guard), guard: guard, body: body, from: nil}
          end
        # `after t -> body` is a clause for the self-timer message
        # `after_<loop> gen'`, guarded by `gen' = gen` at render time (a
        # stale generation is ignored); the parameter is kept whole because
        # the ignore branch rebuilds the state from it
        after_cl =
          if after_body do
            body = loop_tail(fname, atag, after_body)
            [%{mod: mod, kind: :handle_info, mpat: {atag, {:"gen'", [], nil}}, spat: prune_param(param, body, :after),
               guard: nil, body: body, from: nil, after: true}]
          else
            []
          end
        arms ++ after_cl
    end
  end

  # The loop parameter is the state pattern of every arm. A variable of it
  # that an unguarded arm does not use is renamed `_x` (Lean warns on unused
  # pattern variables). Guarded arms keep it: a failed guard falls through
  # to a later arm whose variables are aliased to this arm's pattern parts.
  # exit/raise/throw rebuild the whole state from the parts, so they keep it too.
  defp prune_param(param, _body, guard) when guard != nil, do: param
  defp prune_param(param, body, _guard) do
    if needs_state?(body) do
      param
    else
      used = free_vars(body)
      Macro.postwalk(param, fn
        {v, m, nil} = n when is_atom(v) ->
          s = Atom.to_string(v)
          if s in used or String.starts_with?(s, "_"), do: n, else: {:"_#{s}", m, nil}
        n -> n
      end)
    end
  end

  defp needs_state?(body) do
    {_, found} = Macro.prewalk(body, false, fn
      {:exit, _, [_]} = n, _ -> {n, true}
      {f, _, args} = n, _ when f in [:raise, :throw] and is_list(args) -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  # {loop name, state parameter, receive arms, after body | nil} of a raw
  # process module, or nil
  defp loop_of(body) do
    loops = for {:def, _, [head, [do: {:receive, _, [opts]}]]} <- body, do: {head_parts(head), opts}
    handlers =
      for {:def, _, [head, _]} <- body, {f, _, _} = head_parts(head), f in [:handle_cast, :handle_info, :handle_call], do: f
    case loops do
      [] -> nil
      [_ | _] when handlers != [] -> fail("a module cannot mix GenServer callbacks with a receive loop")
      [{{fname, [param], nil}, [do: arms]}] -> {fname, param, arms, nil}
      [{{fname, [param], nil}, [do: arms, after: [{:->, _, [[_t], ab]}]]}] -> {fname, param, arms, ab}
      [{{fname, _, _}, _}] -> fail("receive loop #{fname} must take one argument and have no guard; `after` takes one clause")
      _ -> fail("more than one receive loop in a module")
    end
  end

  # Rewrite the tail of a receive-clause body: `loop(e)` continues with state
  # e (re-arming the after-timer if the loop has one), `exit(r)`, `raise`
  # and `throw` stay, a statement is kept and the loop returns after it,
  # any other value means the loop returns normally.
  defp loop_tail(fname, atag, {:if, m, [c, [do: a, else: b]]}),
    do: {:if, m, [c, [do: loop_tail(fname, atag, a), else: loop_tail(fname, atag, b)]]}
  defp loop_tail(fname, atag, {:case, m, [s, [do: arms]]}),
    do: {:case, m, [s, [do: for({:->, am, [p, b]} <- arms, do: {:->, am, [p, loop_tail(fname, atag, b)]})]]}
  defp loop_tail(fname, atag, b) do
    {init, [last]} = Enum.split(stmts(b), -1)
    tail =
      case last do
        {^fname, _, [e]} -> arm_after(atag) ++ [{:noreply, e}]
        {:exit, _, [_]} -> [last]
        {f, _, args} when f in [:raise, :throw] and is_list(args) -> [last]
        _ -> if(value?(last), do: [], else: [last]) ++ [{:exit, [], [:normal]}]
      end
    {:__block__, [], init ++ tail}
  end

  # `Process.send_after(self(), {:after_<loop>, gen + 1}, _)`: entering the
  # receive again arms the after-timer for the next generation (the state
  # moves to `gen + 1` at the same time, see `plain_body`), which makes any
  # earlier timer stale
  defp arm_after(nil), do: []
  defp arm_after(atag),
    do: [{{:., [], [{:__aliases__, [], [:Process]}, :send_after]}, [],
          [{:self, [], []}, {atag, {:+, [], [{:gen, [], nil}, 1]}}, 0]}]

  defp value?(x) when is_atom(x) or is_integer(x) or is_list(x), do: true
  defp value?({v, _, nil}) when is_atom(v), do: true
  defp value?({:{}, _, _}), do: true
  defp value?({_, _}), do: true
  defp value?(_), do: false

  defp clause_of(mod, :handle_call, [mpat, fpat, spat], guard, b),
    do: %{mod: mod, kind: :handle_call, mpat: mpat, spat: spat, guard: guard, body: b, from: fpat}
  defp clause_of(mod, kind, [mpat, spat], guard, b),
    do: %{mod: mod, kind: kind, mpat: mpat, spat: spat, guard: guard, body: b, from: nil}
  defp clause_of(_, _, _, _, _) do
    nil
  end

  defp head_parts({:when, _, [{f, _, args}, g]}), do: {f, args, g}
  defp head_parts({f, _, args}), do: {f, args, nil}

  # ---------- rendering ----------

  defp render(ctx, clauses) do
    enums =
      for {{mod, name}, t} <- ctx.types,
          alts = union(t),
          Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil),
          name not in [:msg, :cast, :info, :call] do
        _ = mod
        ename = name |> Atom.to_string() |> String.capitalize()
        "inductive #{ename}\n" <> Enum.map_join(alts, "\n", &"  | #{&1}") <> "\n  deriving Repr, DecidableEq\n"
      end
      |> Enum.uniq()

    msg =
      "inductive Msg\n" <>
        Enum.map_join(ctx.msg_ctors, "\n", fn {tag, ts} ->
          call? = Enum.any?(ctx.types, fn {{_, n}, t} -> n == :call and tag in Enum.map(union(t), &tag_of/1) end)
          fields =
            ts |> Enum.with_index()
            |> Enum.map_join(" ", fn {t, i} -> if(call? and i == 0, do: "(caller : Pid)", else: "(a#{i} : #{t})") end)
          "  | #{tag}" <> if(fields == "", do: "", else: " " <> fields)
        end) <> "\n  deriving Repr, DecidableEq\n"

    pids =
      ctx.pids
      |> Enum.with_index()
      |> Enum.map_join("", fn {{mod, const}, i} -> "/-- Registered name `#{mod}`. -/\ndef #{const} : Pid := #{i}\n" end)

    {beh_clauses, ctx} = render_clauses(ctx, clauses)

    trap_arms =
      Enum.map_join(ctx.st_ctors, "\n", fn {name, fields} ->
        mod = Enum.find(ctx.pids |> Map.keys() |> Enum.concat(Enum.map(ctx.types, fn {{m, _}, _} -> Atom.to_string(m) end)) |> Enum.uniq(),
                        fn m -> String.starts_with?(name, ctor_name(String.to_atom(m))) end)
        traps = mod != nil and Map.get(ctx.traps, String.to_atom(mod), false)
        wild = Enum.map_join(fields, "", fn _ -> " _" end)
        "    | .#{name}#{wild} => #{traps}"
      end)
    down = if List.keymember?(ctx.msg_ctors, :DOWN, 0), do: "  downMsg := some fun p r => .DOWN p r\n", else: ""
    exit_line =
      if List.keymember?(ctx.msg_ctors, :EXIT, 0),
        do: "  exitMsg := fun p r => .EXIT p r\n",
        else: "  -- no module declares {:EXIT, ...}; nobody traps, so this codec is never used\n  exitMsg := #{placeholder_exit(ctx)}\n"
    sig =
      "/-- Who traps exits (from `Process.flag(:trap_exit, true)`), the EXIT message, the DOWN message. -/\n" <>
        "def sig : Signals St Msg where\n  traps := fun\n#{trap_arms}\n" <> exit_line <> down <> "\n"

    st =
      "inductive St\n" <>
        Enum.map_join(ctx.st_ctors, "\n", fn {name, fields} ->
          String.trim_trailing("  | #{name} " <> Enum.map_join(fields, " ", fn {f, t} -> "(#{f} : #{t})" end))
        end) <> "\n  deriving Repr, DecidableEq\n"

    all_covered = Enum.all?(ctx.st_ctors, fn {name, _} -> name in ctx.covered end)
    catch_all =
      if all_covered do
        "\n"
      else
        "\n  -- Unmatched message: GenServer would crash (cast) or ignore (info). Modelled as ignore.\n" <>
          "  | _, _, s, _ => (s, [])\n"
      end
    beh =
      "def beh : EBehavior St Msg\n" <>
        Enum.join(beh_clauses ++ ctx.extra, "\n") <> catch_all


    """
    -- GENERATED by elixir/to_lean.exs. Do not edit.
    import Leanactors.Sys

    namespace #{ctx.ns}

    open Leanactors

    #{Enum.join(enums, "\n")}
    #{msg}
    #{st}
    #{pids}
    #{sig}#{beh}
    end #{ctx.ns}
    """
    |> then(&{&1, ctx})
  end

  # A total `exitMsg` for a file in which nobody traps (so the codec is never
  # applied): the first nullary Msg constructor, else the first constructor
  # applied to default arguments (`p`, `r`, 0, false, [], none, first enum alt).
  defp placeholder_exit(ctx) do
    {tag, ts} =
      Enum.find(ctx.msg_ctors, fn {_, ts} -> ts == [] end) ||
        List.first(ctx.msg_ctors) || fail("@type msg is empty")
    args = Enum.map(ts, &default_of(ctx, &1))
    binder = fn v -> if(v in args, do: v, else: "_") end
    "fun #{binder.("p")} #{binder.("r")} => .#{tag}" <> Enum.map_join(args, "", &(" " <> paren_or(&1)))
  end

  defp default_of(_ctx, "Pid"), do: "p"
  defp default_of(_ctx, "Reason"), do: "r"
  defp default_of(_ctx, t) when t in ["Nat", "Int"], do: "0"
  defp default_of(_ctx, "Bool"), do: "false"
  defp default_of(_ctx, "List " <> _), do: "[]"
  defp default_of(_ctx, "Option " <> _), do: "none"
  defp default_of(ctx, t) do
    case Enum.find(ctx.types, fn {{_, n}, _} -> n |> Atom.to_string() |> String.capitalize() == t end) do
      {_, u} -> ".#{List.first(union(u))}"
      nil -> fail("no default value of type #{t} for the exitMsg placeholder")
    end
  end

  defp render_clauses(ctx, clauses) do
    indexed = Enum.with_index(clauses)
    # A clause subsumed by an earlier clause of the same module is unreachable
    # (Elixir warns "this clause cannot match"; with a guard we already inlined it).
    # Across kinds it is not unreachable on the BEAM (separate callbacks) but
    # would be in the single Lean match, so that is an error.
    indexed = Enum.reject(indexed, fn {cl, j} ->
      Enum.any?(indexed, fn {e, i} ->
        sub = i < j and e.mod == cl.mod and general?(e.mpat, cl.mpat) and general?(e.spat, cl.spat)
        if sub and e.kind != cl.kind,
          do: fail("a #{cl.kind} clause of #{cl.mod} is shadowed by a bare #{e.kind} pattern; use a tag")
        sub
      end)
    end)
    {rendered, ctx} = Enum.map_reduce(indexed, ctx, fn {cl, i}, c ->
      {env, mp, sp, guards} = patterns(c, cl)
      env = if uses_self?(cl), do: Map.put(env, :__self__, true), else: env
      env = if spawns?(cl), do: Map.put(env, :__fresh__, 0), else: env
      env = if cl.from, do: Map.put(env, :__from__, from_name(cl.from)), else: env
      guard_str = Enum.map(guards, &guard_to_lean(env, &1)) ++ if(cl.guard, do: [guard_to_lean(env, cl.guard)], else: [])
      {body_str, c} = body(c, cl.mod, env, cl.body)
      {rhs, c, deferred} =
        cond do
          # the after body runs only for the current generation; a stale
          # after-message was cancelled on the BEAM, so it is consumed and
          # ignored (state unchanged, no re-entry), not deferred
          cl[:after] -> {"if gen' = gen then #{body_str} else (#{sp}, [])", c, false}
          guard_str == [] -> {body_str, c, false}
          true ->
            {fallback, c, deferred} = fallthrough(c, clauses, i, env, sp)
            {"if #{Enum.join(guard_str, " ∧ ")} then #{body_str} else #{fallback}", c, deferred}
        end
      c =
        if cl.guard == nil and bare?(cl.mpat) and bare?(cl.spat),
          do: %{c | covered: [ctor_name(cl.mod) | c.covered]},
          else: c
      # a deferring fallback re-enqueues the whole message: name the pattern
      {me, mp} = if deferred, do: {"me", "#{msg_name(env)}@(#{mp})"}, else: {self_name(env), mp}
      header = "  | #{me}, #{fresh_name(env)}, #{sp}, #{mp}"
      {{cl, {env[:__sparts__] || [], env[:__mparts__] || []}, "#{header} => #{rhs}"}, c}
    end)
    {strs, ctx} = insert_crashes(ctx, rendered)
    # selective receive: a raw process without a catch-all clause re-enqueues
    # any other message to itself (its defer clause is its last clause, see
    # insert_crashes), so the global catch-all must not cover it
    ctx = %{ctx | covered: Enum.map(ctx.defers, &ctor_name/1) ++ ctx.covered}
    {strs, ctx}
  end

  # Which message tags the given rendered clauses cover exhaustively, judged
  # on the Lean pattern parts (not the Elixir ones, because a pid-narrowed
  # variable renders as `(some w)` and leaves the `none` case to a later
  # clause): a tag is covered when the rows of its clauses, plus the rows of
  # any bare-message clause widened to the tag's arity, are exhaustive over
  # the state fields and message arguments. `:all` when the bare-message
  # clauses alone cover every state.
  defp covered_tags(ctx, mod, entries) do
    {_, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    ftypes = Enum.map(fields, &elem(&1, 1))
    bare = for {cl, {sp, _}, _} <- entries, bare?(cl.mpat), do: sp
    tagged = for {cl, {sp, mp}, _} <- entries, not bare?(cl.mpat), do: {elem(msg_shape(cl.mpat), 0), sp ++ mp}
    tags =
      for {tag, ts} <- ctx.msg_ctors,
          rows = for({^tag, row} <- tagged, do: row) ++ for(sp <- bare, do: sp ++ List.duplicate("_", length(ts))),
          rows != [] and exhaustive?(ctx, rows, ftypes ++ ts),
          do: tag
    if bare != [] and exhaustive?(ctx, bare, ftypes), do: [:all | tags], else: tags
  end

  # Usefulness check: do the rows (lists of Lean pattern parts, one per
  # column of the given types) cover every value? Bool, Option, List and
  # generated enum columns have a complete signature; a literal or anything
  # unrecognised is an opaque constructor that never completes one, so the
  # answer errs towards "not exhaustive" (an extra crash clause that Lean
  # then rejects as redundant) and never towards a silently ignored case.
  defp exhaustive?(_ctx, [], _types), do: false
  defp exhaustive?(_ctx, _rows, []), do: true
  defp exhaustive?(ctx, rows, [t | ts]) do
    heads = Enum.map(rows, &head_of(hd(&1)))
    sig = signature(ctx, t)
    cond do
      Enum.all?(heads, &(&1 == :var)) ->
        exhaustive?(ctx, Enum.map(rows, &tl/1), ts)
      sig != nil and Enum.all?(sig, fn {c, _} -> c in heads end) ->
        Enum.all?(sig, fn {c, subts} ->
          spec =
            for [h | rest] <- rows, head_of(h) in [:var, c],
                do: if(head_of(h) == :var, do: List.duplicate("_", length(subts)), else: sub_parts(h, c)) ++ rest
          exhaustive?(ctx, spec, subts ++ ts)
        end)
      true ->
        exhaustive?(ctx, for([h | rest] <- rows, head_of(h) == :var, do: rest), ts)
    end
  end

  defp head_of("true"), do: :true
  defp head_of("false"), do: :false
  defp head_of("none"), do: :none
  defp head_of("(some " <> _), do: :some
  defp head_of("[]"), do: :nil
  defp head_of("." <> name), do: {:enum, name}
  defp head_of("(" <> _ = p), do: if(length(split_cons(p)) == 2, do: :cons, else: {:opaque, p})
  defp head_of(p), do: if(plain?(p) or p == "_", do: :var, else: {:opaque, p})

  defp signature(_ctx, "Bool"), do: [{:true, []}, {:false, []}]
  defp signature(_ctx, "Option " <> inner), do: [{:none, []}, {:some, [unparen(inner)]}]
  defp signature(_ctx, "List " <> inner = t), do: [{:nil, []}, {:cons, [unparen(inner), t]}]
  defp signature(ctx, t) do
    case Enum.find(ctx.types, fn {{_, n}, _} -> n |> Atom.to_string() |> String.capitalize() == t end) do
      {_, u} -> if(enum_type?(t), do: for(a <- union(u), do: {{:enum, Atom.to_string(a)}, []}), else: nil)
      nil -> nil
    end
  end

  defp sub_parts("(some " <> rest, :some), do: [String.replace_suffix(rest, ")", "")]
  defp sub_parts(p, :cons), do: split_cons(p)
  defp sub_parts(_, _), do: []

  # `(h :: t)` -> ["h", "t"], splitting at the top-level `::` only
  defp split_cons("(" <> rest), do: rest |> String.replace_suffix(")", "") |> split_top(0, "")
  defp split_top("", _, acc), do: [acc]
  defp split_top(" :: " <> rest, 0, acc), do: [acc | split_top(rest, 0, "")]
  defp split_top("(" <> rest, d, acc), do: split_top(rest, d + 1, acc <> "(")
  defp split_top(")" <> rest, d, acc), do: split_top(rest, d - 1, acc <> ")")
  defp split_top(<<c::utf8, rest::binary>>, d, acc), do: split_top(rest, d, acc <> <<c::utf8>>)

  defp plain?(part), do: part =~ ~r/^[A-Za-z_][A-Za-z0-9_']*$/ and part not in ["none", "true", "false"]

  # Per module: cast/call clauses, then one crash clause for each cast or
  # call tag (by clause or by @type cast/call) the module's clauses do not
  # cover exhaustively, then info
  # clauses, then (raw process without a catch-all, unless its arms are
  # already exhaustive) the defer clause. A bare message variable in a
  # cast/call clause covers every tag. A receive loop has only info-kind
  # clauses, so it never gets crash clauses.
  defp insert_crashes(ctx, rendered) do
    Enum.map_reduce(ctx.mods, ctx, fn mod, c ->
      chunk = Enum.filter(rendered, fn {cl, _, _} -> cl.mod == mod end)
      {ci, info} = Enum.split_with(chunk, fn {cl, _, _} -> cl.kind != :handle_info end)
      covered = covered_tags(c, mod, ci)
      needed =
        if :all in covered do
          []
        else
          for {tag, _} <- c.msg_ctors,
              Map.get(c.kinds, {mod, tag}) in [:handle_cast, :handle_call],
              tag not in covered,
              do: tag
        end
      crash = Enum.map(needed, &crash_clause(c, mod, &1))
      # Every tag is covered (or gets a crash clause): the module's arms are
      # exhaustive, so a trailing defer clause or the global catch-all would
      # be a redundant alternative, which Lean rejects.
      total = covered_tags(c, mod, chunk)
      exhaustive = :all in total or Enum.all?(c.msg_ctors, fn {tag, _} -> tag in total or tag in needed end)
      c = if exhaustive, do: %{c | covered: [ctor_name(mod) | c.covered]}, else: c
      defer = if mod in c.defers and not exhaustive, do: [defer_clause(c, mod)], else: []
      strs = fn xs -> Enum.map(xs, &elem(&1, 2)) end
      {strs.(ci) ++ crash ++ strs.(info) ++ defer, c}
    end)
    |> then(fn {groups, c} -> {List.flatten(groups), c} end)
  end

  # `| _, _, .<mod> s_0 .., .<tag> _ .. => (.<mod> s_0 .., [.exit .error])`:
  # no clause matched, FunctionClauseError, links and monitors are notified.
  defp crash_clause(ctx, mod, tag) do
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    {^tag, ts} = List.keyfind(ctx.msg_ctors, tag, 0)
    st = ".#{ctor}" <> (fields |> Enum.with_index() |> Enum.map_join("", fn {_, i} -> " s_#{i}" end))
    mp = ".#{tag}" <> Enum.map_join(ts, "", fn _ -> " _" end)
    "  | _, _, #{st}, #{mp} => (#{st}, [.exit .error])"
  end

  # `| me, _, .mod s_0 s_1 .., m => (.mod s_0 s_1 .., [.send me m])`
  # (with an after-timer: `.mod s_0 .. gen` re-enters as `.mod s_0 .. (gen + 1)`
  # and arms the new generation)
  defp defer_clause(ctx, mod) do
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    parts = visible_fields(ctx, mod, fields) |> Enum.with_index() |> Enum.map(fn {_, i} -> "s_#{i}" end)
    gen = if Map.has_key?(ctx.afters, mod), do: ["gen"], else: []
    sp = state_str(ctor, parts ++ gen)
    sp2 = state_str(ctor, parts ++ Enum.map(gen, fn _ -> "(gen + 1)" end))
    "  | me, _, #{sp}, m => (#{sp2}, [#{Enum.join([send_str(ctx, "me", "m") | after_arm(ctx, mod, "me", "(gen + 1)")], ", ")}])"
  end

  # the effect that arms a loop's after-timer for generation `g` at pid `p`,
  # if the module has one
  defp after_arm(ctx, mod, p, g) do
    case Map.get(ctx.afters, mod) do
      nil -> []
      tag -> [".sendAfter #{paren_or(p)} (.#{tag} #{g})"]
    end
  end

  # the state fields a source pattern or expression sees: the hidden `gen`
  # of a loop with `after` is appended separately (`patterns`, `plain_body`,
  # the spawn site)
  defp visible_fields(ctx, mod, fields),
    do: if(Map.has_key?(ctx.afters, mod), do: Enum.drop(fields, -1), else: fields)

  # the generation a re-entered state and the child of a spawn carry
  defp gen_suffix(ctx, mod), do: if(Map.has_key?(ctx.afters, mod), do: " (gen + 1)", else: "")
  defp spawn_gen(ctx, mod), do: if(Map.has_key?(ctx.afters, mod), do: " 0", else: "")

  defp state_str(ctor, []), do: ".#{ctor}"
  defp state_str(ctor, parts), do: ".#{ctor} " <> Enum.join(parts, " ")

  # the clause's state pattern re-entered: the visible parts unchanged, gen bumped
  defp reenter_state(ctx, mod, env) do
    {ctor, _} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    state_str(ctor, env[:__vparts__]) <> gen_suffix(ctx, mod)
  end

  # the name for a whole message in a deferring clause (avoid the clause's own `m`)
  defp msg_name(env), do: if(Map.has_key?(env, "m"), do: "m'", else: "m")

  defp bare?({v, _, nil}) when is_atom(v), do: true
  defp bare?(_), do: false

  defp self_name(env), do: if(Map.has_key?(env, :__self__), do: "me", else: "_")
  defp fresh_name(env), do: if(Map.has_key?(env, :__fresh__), do: "fresh", else: "_")

  # a clause needs `fresh` if it spawns
  defp spawns?(cl) do
    {_, found} = Macro.prewalk(cl.body, false, fn
      {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, _} = n, _ when f in [:start_link, :start] -> {n, true}
      {f, _, [_, _, _]} = n, _ when f in [:spawn, :spawn_link, :spawn_monitor] -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  # `me` is needed if the body calls self() or contains a blocking call
  # (the request carries the caller pid).
  defp uses_self?(cl) do
    {_, found} = Macro.prewalk(cl.body, false, fn
      {:self, _, []} = n, _ -> {n, true}
      {:{}, _, [:noreply, _, _]} = n, _ -> {n, true}
      n, acc -> {n, acc || blocking_call?(n)}
    end)
    found
  end

  # A guarded clause that fails its guard falls through to the next clause of
  # the same module and callback kind whose patterns are at least as general.
  # That clause's variables are aliased to the current clause's Lean pattern
  # parts. In a raw process without a catch-all the message is deferred
  # instead (third component true); a cast/call crashes.
  defp fallthrough(ctx, clauses, i, env, sp) do
    cl = Enum.at(clauses, i)
    later = clauses |> Enum.with_index() |> Enum.filter(fn {c, j} -> j > i and c.mod == cl.mod and c.kind == cl.kind end)
    case Enum.find(later, fn {c, _} -> general?(c.mpat, cl.mpat) and general?(c.spat, cl.spat) end) do
      nil ->
        cond do
          # a receive arm whose guard fails does not consume the message;
          # re-entering the receive bumps the after-timer generation
          cl.mod in ctx.defers ->
            effs = [send_str(ctx, "me", msg_name(env)) | after_arm(ctx, cl.mod, "me", "(gen + 1)")]
            {"(#{reenter_state(ctx, cl.mod, env)}, [#{Enum.join(effs, ", ")}])", ctx, true}
          # no cast/call clause matches: FunctionClauseError
          cl.kind != :handle_info ->
            {"(#{sp}, [.exit .error])", ctx, false}
          true ->
            ctx = %{ctx | warnings: ctx.warnings ++ ["clause #{i} guard has no fallthrough; Elixir would crash, modelled as no-op"]}
            {"(#{sp}, [])", ctx, false}
        end
      {c, _} ->
        env2 = aliases(c.mpat, cl.mpat, env, %{__msg_parts__: env[:__mparts__]})
        {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(cl.mod), 0)
        env2 = whole_alias(c.spat, state_str(ctor, env[:__vparts__]), visible_fields(ctx, cl.mod, fields), env2)
        env2 = if uses_self?(c), do: Map.put(env2, :__self__, true), else: env2
        {b, ctx} = body(ctx, c.mod, env2, c.body)
        if c.guard, do: fail("chained guards are not supported (clause #{i})")
        {b, ctx, false}
    end
  end

  # is `general` at least as general as `specific`? (var/_ or identical; a
  # tuple whose parts are all variables matches everything a variable does)
  defp general?({v, _, nil}, _) when is_atom(v), do: true
  defp general?(a, a), do: true
  defp general?({:{}, _, xs}, {v, _, nil}) when is_atom(v), do: Enum.all?(xs, &bare?/1)
  defp general?({a, b}, {v, _, nil}) when is_atom(v), do: bare?(a) and bare?(b)
  defp general?({:{}, _, xs}, {:{}, _, ys}) when length(xs) == length(ys), do: Enum.zip(xs, ys) |> Enum.all?(fn {x, y} -> general?(x, y) end)
  defp general?({a, b}, {c, d}), do: general?(a, c) and general?(b, d)
  defp general?(_, _), do: false

  # alias top-level message variables of the general clause to the specific
  # clause's Lean parts (only whole-argument variables are supported)
  defp aliases({v, _, nil}, _spec, env, _) when is_atom(v) do
    name = Atom.to_string(v)
    if String.starts_with?(name, "_"), do: env, else: Map.put(env, {:alias, name}, env[:__mp__])
  end
  defp aliases(gen, spec, env, _) do
    {_, gargs} = msg_shape(gen)
    {_, sargs} = msg_shape(spec)
    Enum.zip(gargs, sargs)
    |> Enum.reduce(env, fn
      {{v, _, nil}, {w, _, nil}}, e when is_atom(v) and is_atom(w) ->
        Map.put(e, {:alias, Atom.to_string(v)}, Atom.to_string(w))
      {{v, _, nil}, other}, _e when is_atom(v) -> fail("cannot alias #{v} to structured pattern #{Macro.to_string(other)}")
      _, e -> e
    end)
  end

  # alias the general clause's state variables to the specific clause's Lean
  # state parts: a whole-state variable to the single part (typed as the
  # field, so an `Option` part such as `(some p')` is used as is) or to the
  # rebuilt constructor; a tuple of variables field by field
  defp whole_alias({v, _, nil}, sp, fields, env) when is_atom(v) do
    case {env[:__vparts__], fields} do
      {[single], [{_, t}]} -> env |> Map.put({:alias, Atom.to_string(v)}, single) |> Map.put(lean_ident(Atom.to_string(v)), t)
      _ -> Map.put(env, {:alias, Atom.to_string(v)}, sp)
    end
  end
  defp whole_alias({a, b}, sp, fields, env), do: whole_alias({:{}, [], [a, b]}, sp, fields, env)
  defp whole_alias({:{}, _, xs}, _sp, fields, env) when length(xs) == length(fields) do
    Enum.zip([xs, env[:__vparts__] || [], fields])
    |> Enum.reduce(env, fn
      {{v, _, nil}, part, {_, t}}, e when is_atom(v) ->
        name = Atom.to_string(v)
        if String.starts_with?(name, "_"), do: e, else: e |> Map.put({:alias, name}, part) |> Map.put(lean_ident(name), t)
      _, e -> e
    end)
  end
  defp whole_alias(_, _, _, env), do: env

  # Variables the body uses where a pid is required.
  defp pid_uses(body) do
    {_, vs} = Macro.prewalk(body, [], fn
      {:send, _, [{v, _, nil}, _]} = n, acc when is_atom(v) -> {n, [v | acc]}
      {{:., _, [{:__aliases__, _, [:Process]}, f]}, _, [{v, _, nil} | _]} = n, acc when is_atom(v) and f in [:exit, :send_after, :monitor] -> {n, [v | acc]}
      {{:., _, [{:__aliases__, _, [:GenServer]}, :reply]}, _, [{v, _, nil}, _]} = n, acc when is_atom(v) -> {n, [v | acc]}
      n, acc -> {n, acc}
    end)
    Enum.uniq(vs)
  end

  # Translate both patterns. Returns {env, msg_pat, state_pat, equality_guards}.
  defp patterns(ctx, cl) do
    ctx = %{ctx | pid_vars: pid_uses(cl.body)}
    {mp, env, gs} =
      case cl.mpat do
        {v, _, nil} when is_atom(v) ->
          name = Atom.to_string(v)
          if String.starts_with?(name, "_"), do: {"_", %{}, []}, else: {name, %{name => "Msg"}, []}
        _ ->
          {tag, args} = msg_shape(cl.mpat)
          {^tag, arg_types} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("message tag #{inspect(tag)} not in @type msg, cast, info or call")
          {args, env0} =
            if cl.from do
              length(args) + 1 == length(arg_types) || fail("arity mismatch for call #{tag}")
              fname = from_name(cl.from)
              {[{String.to_atom(fname), [], nil} | args], %{}}
            else
              length(args) == length(arg_types) || fail("arity mismatch for #{tag}")
              {args, %{}}
            end
          {parts, env, gs} = pat_list(ctx, args, arg_types, env0, [])
          {if(parts == [], do: ".#{tag}", else: ".#{tag} " <> Enum.join(parts, " ")), Map.put(env, :__mparts__, parts), gs}
      end
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(cl.mod), 0)
    vfields = visible_fields(ctx, cl.mod, fields)
    sub = state_subpats(cl.spat, length(vfields))
    {vparts, env, gs} = pat_list(ctx, sub, Enum.map(vfields, &elem(&1, 1)), env, gs)
    # a loop with `after`: the hidden generation field is the pattern variable `gen`
    {sparts, env} =
      if Map.has_key?(ctx.afters, cl.mod) do
        if Map.has_key?(env, "gen"), do: fail("#{cl.mod}: `gen` is reserved for the after-timer generation")
        {vparts ++ ["gen"], Map.put(env, "gen", "Nat")}
      else
        {vparts, env}
      end
    sp = state_str(ctor, sparts)
    env = env |> Map.put(:__mp__, mp) |> Map.put(:__sparts__, sparts) |> Map.put(:__vparts__, vparts)
    {env, mp, sp, gs}
  end

  # the `from` argument of handle_call: a variable (possibly _-prefixed) or {pid, _ref}
  defp from_name({v, _, nil}) when is_atom(v), do: v |> Atom.to_string() |> String.trim_leading("_") |> then(&if(&1 == "", do: "caller", else: &1)) |> lean_ident()
  defp from_name({{v, _, nil}, _}) when is_atom(v), do: from_name({v, [], nil})
  defp from_name(p), do: fail("unsupported from pattern #{Macro.to_string(p)}")

  # {:DOWN, ref, :process, pid, reason}: keep pid and reason
  defp msg_shape({:{}, _, [:DOWN, _ref, :process, pid, reason]}), do: {:DOWN, [pid, reason]}
  defp msg_shape(a) when is_atom(a), do: {a, []}
  defp msg_shape({a, b}) when is_atom(a), do: {a, [b]}
  defp msg_shape({:{}, _, [a | rest]}) when is_atom(a), do: {a, rest}
  defp msg_shape(p), do: fail("unsupported message pattern #{Macro.to_string(p)}")

  # A state pattern against an n-field constructor: tuple -> its parts;
  # a variable/underscore against a multi-field state -> that many wildcards
  # is NOT allowed (we need the fields); so we bind whole-state variables
  # by reconstructing. Single-field states take the pattern directly.
  defp state_subpats(p, 1), do: [p]
  defp state_subpats({:{}, _, xs}, n) when length(xs) == n, do: xs
  defp state_subpats({a, b}, 2), do: [a, b]
  defp state_subpats({v, _, nil}, n) when is_atom(v), do: List.duplicate({:"__whole__#{v}", [], nil}, n)
  defp state_subpats(p, n), do: fail("state pattern #{Macro.to_string(p)} does not fit #{n} fields")

  defp pat_list(ctx, pats, types, env, gs) do
    {parts, {env, gs}} =
      Enum.zip(pats, types)
      |> Enum.map_reduce({env, gs}, fn {p, t}, {e, g} ->
        {s, e, g} = pat(ctx, p, t, e, g)
        {s, {e, g}}
      end)
    {parts, env, gs}
  end

  # pattern -> {lean_pattern, env, guards}; type-directed
  defp pat(_ctx, {:_, _, nil}, _t, env, gs) do
    i = Map.get(env, :__wild__, 0)
    {"_w#{i}", Map.put(env, :__wild__, i + 1), gs}
  end
  # a GenServer.from() value {pid, ref} matched at a Pid position: keep the pid
  defp pat(ctx, {x, {r, _, nil}}, t, env, gs) when t in ["Pid", "Option Pid"] and is_atom(r) do
    String.starts_with?(Atom.to_string(r), "_") || fail("ref in from-pattern must be a wildcard")
    pat(ctx, x, t, env, gs)
  end
  defp pat(_ctx, nil, "Option " <> _, env, gs), do: {"none", env, gs}
  defp pat(_ctx, [], "List " <> _, env, gs), do: {"[]", env, gs}
  defp pat(ctx, [{:|, _, [h, t]}], "List " <> inner = lt, env, gs) do
    {hs, env, gs} = pat(ctx, h, unparen(inner), env, gs)
    {ts, env, gs} = pat(ctx, t, lt, env, gs)
    {"(#{hs} :: #{ts})", env, gs}
  end
  defp pat(_ctx, b, "Bool", env, gs) when is_boolean(b), do: {"#{b}", env, gs}
  defp pat(_ctx, a, t, env, gs) when is_atom(a) and a not in [nil, true, false] do
    if enum_type?(t), do: {".#{a}", env, gs}, else: fail("atom #{a} at non-enum position #{t}")
  end
  defp pat(_ctx, n, t, env, gs) when is_integer(n) and t in ["Int", "Nat"], do: {"#{n}", env, gs}
  defp pat(ctx, {v, _, nil}, t, env, gs) when is_atom(v) do
    {name, whole?} =
      case Atom.to_string(v) do
        "__whole__" <> rest -> {lean_ident(rest), true}
        s -> {lean_ident(s), false}
      end
    cond do
      whole? ->
        # a whole-state variable: bind field-wise as name_i and remember to rebuild
        i = map_size(Map.filter(env, fn {k, _} -> is_binary(k) and String.starts_with?(k, name <> "_") end))
        fname = "#{name}_#{i}"
        env = Map.put(env, fname, t) |> Map.update("__whole__" <> name, [fname], &(&1 ++ [fname]))
        {fname, env, gs}
      String.starts_with?(name, "_") -> {"_", env, gs}
      Map.has_key?(env, name) ->
        # non-linear: fresh name + equality guard, possibly through Option
        bound_t = env[name]
        fresh = name <> "'"
        cond do
          bound_t == t -> {fresh, Map.put(env, fresh, t), gs ++ [{:eq, name, fresh}]}
          t == "Option " <> paren_or(bound_t) -> {"(some #{fresh})", Map.put(env, fresh, bound_t), gs ++ [{:eq, name, fresh}]}
          true -> fail("variable #{name} bound at #{bound_t} reused at #{t}")
        end
      t == "Option Pid" and v in ctx.pid_vars ->
        # the body sends to it, so the clause only makes sense when it is a pid
        {"(some #{name})", Map.put(env, name, "Pid"), gs}
      true ->
        {name, Map.put(env, name, t), gs}
    end
  end
  defp pat(_ctx, p, t, _env, _gs), do: fail("unsupported pattern #{Macro.to_string(p)} at type #{t}")

  defp paren_or(t) do
    cond do
      not String.contains?(t, " ") -> t
      String.starts_with?(t, "(") and String.ends_with?(t, ")") -> t
      String.starts_with?(t, "[") and String.ends_with?(t, "]") -> t
      true -> "(#{t})"
    end
  end
  defp unparen("(" <> rest), do: String.trim_trailing(rest, ")")
  defp unparen(t), do: t
  defp enum_type?(t), do: t =~ ~r/^[A-Z][a-z]*$/ and t not in ["Pid", "Int", "Nat", "Bool", "Reason"]

  defp guard_to_lean(_env, {:eq, a, b}), do: "#{a} = #{b}"
  defp guard_to_lean(env, g), do: expr(env, g, nil)

  # ---------- bodies ----------

  # body -> "(state, [sends])" string; may be an if/case over whole bodies
  defp body(ctx, mod, env, {:if, _, [c, [do: a, else: b]]}) do
    {sa, ctx} = body(ctx, mod, env, a)
    {sb, ctx} = body(ctx, mod, env, b)
    {"if #{expr(env, c, nil)} then #{sa} else #{sb}", ctx}
  end
  defp body(ctx, mod, env, {:case, _, [scrut, [do: arms]]}) do
    {arm_strs, ctx} =
      Enum.map_reduce(arms, ctx, fn {:->, _, [[p], b]}, c ->
        {pstr, env2, []} = pat(c, p, guess_type(env, scrut), env, [])
        {bs, c} = body(c, mod, env2, b)
        {"| #{pstr} => #{bs}", c}
      end)
    {"(match #{expr(env, scrut, nil)} with " <> Enum.join(arm_strs, " ") <> ")", ctx}
  end
  defp body(ctx, mod, env, b), do: body_stmts(ctx, mod, env, stmts(b))

  defp body_stmts(ctx, mod, env, stmts) do
    case Enum.split_while(stmts, fn s -> not blocking_call?(s) end) do
      {before, [call | rest]} when rest != [] -> cps_split(ctx, mod, env, before, call, rest)
      {_, [_]} -> fail("a blocking call must be followed by the rest of the body")
      _ -> plain_body(ctx, mod, env, stmts)
    end
  end

  # `lhs = GenServer.call(Mod, m[, timeout])` where lhs is a variable or a pattern
  defp blocking_call?({:=, _, [_lhs, {{:., _, [{:__aliases__, _, [:GenServer]}, :call]}, _, [_, _ | _]}]}), do: true
  defp blocking_call?(_), do: false

  # v = GenServer.call(Target, m); rest   ==>
  #   this clause: sends-so-far ++ [.send target (m me)], state := <mod>_await<i> captured
  #   extra:       | _, _, .<mod>_await<i> captured, .reply v => rest
  #                | me, _, .<mod>_await<i> captured, m => (.<mod>_await<i> captured, [.send me m])
  defp cps_split(ctx, mod, env, before, {:=, _, [lhs, {_, _, [{:__aliases__, _, [target]}, m | _timeout]}]}, rest) do
    ctx.reply_type || fail("GenServer.call used but no module declares @type reply")
    Map.has_key?(ctx.afters, mod) && fail("#{mod}: a blocking call inside a receive loop with `after` is not supported")
    const = pid_const(ctx, target)
    i = Map.get(ctx.awaits, mod, 0)
    ctx = %{ctx | awaits: Map.put(ctx.awaits, mod, i + 1)}
    await = "#{ctor_name(mod)}_await#{i}"
    # variables the continuation needs, with their types
    {lhs_pat, lhs_var} =
      case lhs do
        {v, _, nil} when is_atom(v) -> {lean_ident(Atom.to_string(v)), lean_ident(Atom.to_string(v))}
        p -> {elem(pat(ctx, p, ctx.reply_type, %{}, []), 0), nil}
      end
    rest_vars = free_vars({:__block__, [], rest}) |> Enum.reject(&(&1 == lhs_var))
    captured = Enum.filter(rest_vars, &Map.has_key?(env, &1)) |> Enum.map(&{&1, env[&1]})
    ctx = %{ctx | st_ctors: ctx.st_ctors ++ [{await, captured}], covered: [await | ctx.covered]}
    cap_str = Enum.map_join(captured, "", fn {n, _} -> " " <> n end)
    # the request: a call message with `me` as the from field
    {tag, args} = msg_shape(m)
    {^tag, [_ | ts]} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("call #{tag} not declared in @type call")
    parts = Enum.zip(args, ts) |> Enum.map(fn {a, t} -> paren_or(expr(env, a, t)) end)
    req = send_str(ctx, const, ".#{tag} me" <> Enum.map_join(parts, "", &(" " <> &1)))
    {send_strs, ctx, _} = sends(ctx, env, before)
    this = "(.#{await}#{cap_str}, [#{Enum.join(send_strs ++ [req], ", ")}])"
    # the continuation, in an environment with the captured vars, v : reply, and me
    env2 = Map.new(captured) |> Map.put(:__self__, true)
    env2 = if lhs_var, do: Map.put(env2, lhs_var, ctx.reply_type), else: env2
    # the continuation may itself block: recurse through the splitter
    {cont, ctx} = body_stmts(ctx, mod, env2, rest)
    cont_self = if uses_self?(%{body: {:__block__, [], rest}}), do: "me", else: "_"
    extra = [
      "  | #{cont_self}, _, .#{await}#{cap_str}, .reply #{lhs_pat} => #{cont}",
      "  | me, _, .#{await}#{cap_str}, m => (.#{await}#{cap_str}, [#{send_str(ctx, "me", "m")}])"
    ]
    {this, %{ctx | extra: ctx.extra ++ extra}}
  end

  defp free_vars(ast) do
    {_, vs} = Macro.prewalk(ast, [], fn
      {v, _, nil} = n, acc when is_atom(v) -> {n, [Atom.to_string(v) | acc]}
      n, acc -> {n, acc}
    end)
    Enum.uniq(vs)
  end

  # a send, rendered as an effect
  defp send_str(_ctx, to, m), do: ".send #{paren_or(to)} #{paren_or(m)}"

  # Statements before the final tuple. Returns {strings, ctx, env}: spawns
  # bind their pid variable to `fresh`, `fresh + 1`, ...
  defp sends(ctx, env, stmts) do
    {strs, {c, e}} =
      Enum.map_reduce(stmts, {ctx, env}, fn s, {c, e} ->
        case s do
          {:send, _, [{:__aliases__, _, [target]}, m]} ->
            {send_str(c, pid_const(c, target), msg_expr(c, e, m)), {c, e}}
          {:send, _, [target, m]} when is_atom(target) and target not in [nil, true, false] ->
            {send_str(c, pid_const(c, target), msg_expr(c, e, m)), {c, e}}
          {:send, _, [to, m]} -> {send_str(c, expr(e, to, "Pid"), msg_expr(c, e, m)), {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :send_after]}, _, [to, m, _t]} ->
            {".sendAfter #{paren_or(expr(e, to, "Pid"))} #{paren_or(msg_expr(c, e, m))}", {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :exit]}, _, [to, r]} ->
            {".signal #{paren_or(expr(e, to, "Pid"))} #{reason_str(r)}", {c, e}}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [{:__aliases__, _, [target]}, m]} ->
            {send_str(c, pid_const(c, target), msg_expr(c, e, m)), {c, e}}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [target, m]} when is_atom(target) and target not in [nil, true, false] ->
            {send_str(c, pid_const(c, target), msg_expr(c, e, m)), {c, e}}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :reply]}, _, [to, r]} ->
            c.reply_type || fail("GenServer.reply used but no @type reply")
            {send_str(c, expr(e, to, "Pid"), ".reply #{paren_or(expr(e, r, c.reply_type))}"), {c, e}}
          {:=, _, [{:ok, {v, _, nil}}, {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [{:__aliases__, _, [child]}, arg]}]} when is_atom(v) and f in [:start_link, :start] ->
            {cctor, cfields} = List.keyfind(c.st_ctors, ctor_name(child), 0) || fail("unknown child module #{child}")
            init = child_state(c, e, child, arg, cctor, cfields)
            {if(f == :start_link, do: ".spawnLink (#{init})", else: ".spawn (#{init})"), {c, bind_fresh(e, v)}}
          {:=, _, [lhs, {f, _, [{:__aliases__, _, [child]}, fname, [arg]]}]} when f in [:spawn, :spawn_link, :spawn_monitor] ->
            v =
              case {f, lhs} do
                {:spawn_monitor, {{v, _, nil}, {ref, _, nil}}} when is_atom(v) and is_atom(ref) -> v
                {_, {v, _, nil}} when f != :spawn_monitor and is_atom(v) -> v
                _ -> fail("unsupported spawn binding #{Macro.to_string(s)}")
              end
            Map.get(c.loops, child) == fname || fail("#{child}.#{fname} is not the receive loop of #{child}")
            {cctor, cfields} = List.keyfind(c.st_ctors, ctor_name(child), 0) || fail("unknown module #{child}")
            init = state_expr(e, arg, cctor, visible_fields(c, child, cfields)) <> spawn_gen(c, child)
            eff = %{spawn: ".spawn", spawn_link: ".spawnLink", spawn_monitor: ".spawnMonitor"}[f]
            e = bind_fresh(e, v)
            # the child's first receive arms its after-timer, if it has one:
            # the child starts at generation 0 and the timer carries 0
            arm = after_arm(c, child, e[{:alias, Atom.to_string(v)}], "0")
            {Enum.join(["#{eff} (#{init})" | arm], ", "), {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [target]} ->
            {".monitor #{paren_or(expr(e, target, "Pid"))}", {c, e}}
          {:=, _, [{_ref, _, nil}, {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [target]}]} ->
            {".monitor #{paren_or(expr(e, target, "Pid"))}", {c, e}}
          {f, _, args} when f in [:raise, :throw] and is_list(args) ->
            fail("#{f} is only supported as the last statement of a body (it exits the process): #{Macro.to_string(s)}")
          other -> fail("unsupported statement #{Macro.to_string(other)}")
        end
      end)
    {strs, c, e}
  end

  # bind the pid variable of a spawn to `fresh`, `fresh + 1`, ...
  defp bind_fresh(env, v) do
    k = Map.get(env, :__fresh__, 0)
    pid = if k == 0, do: "fresh", else: "(fresh + #{k})"
    env |> Map.put(:__fresh__, k + 1) |> Map.put({:alias, Atom.to_string(v)}, pid) |> Map.put(lean_ident(Atom.to_string(v)), "Pid")
  end

  # exit reasons: :normal and :kill are their own constructors (a kill signal
  # is untrappable in the model too), anything else is error
  defp reason_str(:normal), do: ".normal"
  defp reason_str(:kill), do: ".kill"
  defp reason_str(_), do: ".error"

  defp plain_body(ctx, mod, env, stmts) do
    {sends, [last]} = Enum.split(stmts, -1)
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    {send_strs, ctx, env} = sends(ctx, env, sends)
    # a continuing state of a loop with `after` re-enters the receive at the
    # next generation (an exit, raise or throw keeps the whole state instead)
    next_state = fn e -> state_expr(env, e, ctor, visible_fields(ctx, mod, fields)) <> gen_suffix(ctx, mod) end
    {state, tail} =
      case last do
        {:noreply, e} -> {next_state.(e), []}
        {:{}, _, [:reply, r, e]} ->
          from = env[:__from__] || fail("{:reply, ...} outside handle_call")
          {next_state.(e), [send_str(ctx, from, ".reply #{paren_or(expr(env, r, ctx.reply_type))}")]}
        {:{}, _, [:noreply, e, _t]} ->
          List.keymember?(ctx.msg_ctors, :timeout, 0) || fail("GenServer timeout used but :timeout not in @type msg")
          {next_state.(e), [".sendAfter me .timeout"]}
        {:{}, _, [:stop, r, e]} ->
          {next_state.(e), [".exit #{reason_str(r)}"]}
        {:exit, _, [r]} ->
          st = env[{:alias, "__state__"}] || whole_state(env, ctor, fields)
          {st, [".exit #{reason_str(r)}"]}
        # an uncaught raise or throw kills the process with an error reason
        # (the exception, or {:nocatch, v}); the arguments do not matter
        {f, _, args} when f in [:raise, :throw] and is_list(args) ->
          st = env[{:alias, "__state__"}] || whole_state(env, ctor, fields)
          {st, [".exit .error"]}
        other -> fail("last statement must be {:noreply, state}, {:reply, r, state}, {:stop, r, state}, exit/1, raise or throw, got #{Macro.to_string(other)}")
      end
    {"(#{state}, [#{Enum.join(send_strs ++ tail, ", ")}])", ctx}
  end

  # the current state rebuilt from the clause's state pattern (for exit/1, raise, throw)
  defp whole_state(env, ctor, _fields) do
    case env[:__sparts__] do
      nil -> fail("exit/raise/throw needs the state bound by the pattern")
      parts -> if parts == [], do: ".#{ctor}", else: ".#{ctor} " <> Enum.join(parts, " ")
    end
  end

  defp guess_type(env, {v, _, nil}) when is_atom(v), do: Map.get(env, Atom.to_string(v)) || fail("untyped scrutinee #{v}")
  defp guess_type(_env, e), do: fail("case scrutinee must be a variable, got #{Macro.to_string(e)}")

  # rebuild the state constructor from an expression of the state type
  defp state_expr(env, {:{}, _, xs}, ctor, fields) when length(xs) == length(fields),
    do: ".#{ctor} " <> Enum.map_join(Enum.zip(xs, fields), " ", fn {x, {_, t}} -> paren_or(expr(env, x, t)) end)
  defp state_expr(env, {a, b}, ctor, [_, _] = fields), do: state_expr(env, {:{}, [], [a, b]}, ctor, fields)
  defp state_expr(env, {v, _, nil}, ctor, fields) when is_atom(v) and length(fields) > 1 do
    # whole-state variable: an alias from a fallthrough, or rebuilt from its pattern parts
    case Map.get(env, {:alias, Atom.to_string(v)}) do
      nil ->
        parts = Map.get(env, "__whole__" <> Atom.to_string(v)) || fail("whole-state variable #{v} not bound by a pattern")
        ".#{ctor} " <> Enum.join(parts, " ")
      s -> s
    end
  end
  defp state_expr(env, e, ctor, [{_, t}]), do: ".#{ctor} " <> paren_or(expr(env, e, t))
  defp state_expr(_env, e, _ctor, _fields), do: fail("state expression #{Macro.to_string(e)} does not fit the state type")

  defp msg_expr(ctx, env, m) do
    {tag, args} = msg_shape(m)
    {^tag, ts} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("message #{tag} not declared")
    parts = Enum.zip(args, ts) |> Enum.map(fn {a, t} -> paren_or(expr(env, a, t)) end)
    if parts == [], do: ".#{tag}", else: ".#{tag} " <> Enum.join(parts, " ")
  end

  # expression -> Lean, with an expected type used only to insert some/none
  defp expr(_env, nil, "Option " <> _), do: "none"
  defp expr(env, e, "Option " <> inner) do
    case e do
      {v, _, nil} when is_atom(v) ->
        name = lean_ident(Atom.to_string(v))
        case env[name] do
          "Option " <> _ -> Map.get(env, {:alias, Atom.to_string(v)}, name)
          _ -> "some #{expr(env, e, unparen(inner))}"
        end
      _ -> "some " <> paren_or(expr(env, e, unparen(inner)))
    end
  end
  defp expr(_env, {:self, _, []}, _t), do: "me"
  defp expr(_env, b, _t) when is_boolean(b), do: "#{b}"
  defp expr(_env, a, _t) when is_atom(a) and a not in [nil, true, false], do: ".#{a}"
  defp expr(_env, n, _t) when is_integer(n), do: "#{n}"
  defp expr(_env, [], _t), do: "[]"
  defp expr(env, xs, t) when is_list(xs), do: "[" <> Enum.map_join(xs, ", ", &expr(env, &1, elem_type(t))) <> "]"
  defp expr(env, {v, _, nil}, _t) when is_atom(v), do: Map.get(env, {:alias, Atom.to_string(v)}, lean_ident(Atom.to_string(v)))
  defp expr(env, {op, _, [a, b]}, t) when op in [:+, :-, :++, :<=, :>=, :<, :>, :==, :!=, :and, :or] do
    lop = %{+: "+", -: "-", ++: "++", <=: "≤", >=: "≥", <: "<", >: ">", ==: "=", !=: "≠", and: "∧", or: "∨"}[op]
    at = if op in [:++], do: t, else: nil
    "(#{expr(env, a, at)} #{lop} #{expr(env, b, at)})"
  end
  defp expr(_env, e, _t), do: fail("unsupported expression #{Macro.to_string(e)}")

  defp elem_type("List " <> inner), do: unparen(inner)
  defp elem_type(_), do: nil

  defp fail(msg) do
    IO.puts(:stderr, "error: " <> msg)
    System.halt(2)
  end
end

ToLean.main(System.argv())
