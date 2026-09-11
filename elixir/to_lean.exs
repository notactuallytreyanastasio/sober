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
#   allowed around whole bodies. The other GenServer return forms:
#   {:noreply, e, t} and {:reply, r, e, t} with a timeout t arm the
#   self-timer for :timeout after the reply (t = :hibernate is no timeout);
#   {:stop, reason, e} exits; {:stop, reason, r, e} (handle_call) sends the
#   reply and then exits.
#   handle_continue/2: `{:noreply, e, {:continue, x}}` and `{:reply, r, e,
#   {:continue, x}}` run `handle_continue(x, e)` before any queued message
#   is looked at, so a continue is not a message. The clause is rewritten
#   before translation: the first handle_continue clause whose argument
#   pattern matches x (decided from the source: x is an atom or a tagged
#   tuple, the pattern's literals are compared and its variables bound) is
#   inlined after the clause's own statements and reply, with its argument
#   and state pattern variables substituted by the parts of x and e (a
#   state pattern is a variable, bound to e; or a tuple of variables, bound
#   positionally to a tuple literal e or to the fields of the clause's
#   whole-state variable); the inlined body's tail is then the clause's
#   tail (it may time out, stop, or continue again, up to three continues
#   deep; a deeper chain is an error). Effects keep the BEAM order: the
#   clause's sends, the reply, the continue body's sends. Guards on
#   handle_continue, a literal in its pattern against a non-literal in x,
#   and a continue body variable that shadows a clause variable are errors.
#   Pattern variables the inlined body no longer uses are renamed `_v`. An
#   optional `@type continue` is accepted and ignored (no Msg constructor
#   is generated: the continue never enters a mailbox).
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
#   Maps: a type `%{K => V}` (exactly one pair) is the association list
#   `List (K × V)` of Leanactors/AssocList.lean (imported when a map type
#   occurs). `%{}` is `[]` and a literal `%{k => v, ..}` a list of pairs.
#   Map.get(m, k) and Map.fetch(m, k) are `AssocList.get? m k`, an Option:
#   use them as a `case` scrutinee with `nil`/variable arms or with
#   `{:ok, v}`/`:error` arms, or at an Option position. Map.get(m, k, d) is
#   `(get? m k).getD d`, Map.put `insert` (replace the first pair at k or
#   append), Map.delete `erase`, Map.has_key?/is_map_key `hasKey`, map_size
#   `size`, Map.keys/Map.values `keys`/`values`, and Map.filter/Map.reject
#   with a literal `fn {k, v} -> e end` are `filter`/`reject`. The map's
#   type is the expected type (put, delete, filter, reject) or the type of
#   the map variable, so with no expected type the map argument must be a
#   pattern-bound variable. A map pattern `%{k => p, ..}`, optionally
#   `= m` to name the whole map, needs literal keys (atoms or integers; a
#   variable key is an error) and renders as a variable plus guards: `_`
#   is `hasKey m k`, a literal or an already-bound variable is
#   `get? m k = some v`, and a fresh variable p is bound by
#   `match get? m k with | some p => .. | none => <fallthrough>` around
#   the body, so a failing key falls through to the next clause like a
#   failing guard. `%{}` alone matches any map.
#   Tagged unions: a named @type whose alternatives are atoms and tagged
#   tuples `{:tag, T..}` (at least one tuple; all atoms is an enum, `T |
#   nil` is Option) is an inductive with the capitalised name, e.g.
#   `@type reply :: :ok | {:error, err()} | {:found, pid()} | :not_found`
#   is `inductive Reply`; a tagged tuple at that type, in a pattern or an
#   expression, is the constructor applied to its fields.
#   After a blocking call the rest of the body may be a single if/case.
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
              covered: [], inits: %{}, mods: [], kinds: %{}, loops: %{}, defers: [], afters: %{},
              structs: %{}, struct_states: %{}, struct_order: []
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
    mods = for {:defmodule, _, [{:__aliases__, _, [name]}, [do: body]]} <- top(ast), do: {name, subst_attrs(stmts(body))}
    # registered names: the --pid flags if any are given, else derived from
    # the source (name: __MODULE__ in start_link/start, Process.register/2)
    pids = if map_size(pids) == 0, do: register_names(mods), else: pids
    ctx = %Ctx{ns: ns, pids: pids}
    # every module's @type declarations and defstruct first (a struct or a
    # remote type `Mod.t()` may be used before the module that declares it),
    # then the message and state constructors of the GenServer modules
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_raw_types(c, name, body) end)
    ctx = collect_structs(ctx)
    # a module with a defstruct and no callbacks or receive loop only
    # declares a struct: it has no state and no clauses
    mods = Enum.reject(mods, fn {name, body} -> struct_only?(ctx, name, body) end)
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_types(c, name, body) end)
    # the tagged unions and structs by Lean name, for the expression and
    # pattern renderers (which do not carry the context)
    Process.put(:to_lean_unions, tagged_unions(ctx))
    Process.put(:to_lean_structs, ctx.structs)
    Process.put(:to_lean_struct_states, ctx.struct_states)
    # the first alternative of every enum, the only default value `hd/1` has
    Process.put(:to_lean_firsts, first_ctors(ctx))
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

  # Module attributes used as constants: `@name literal` is substituted for
  # every later read `@name` in the module body (a defstruct default, a
  # guard, a state expression). Only literal values are substituted; the
  # attributes with a meaning to the compiler (@type, @spec, @impl, @doc,
  # ...) are left alone.
  @compiler_attrs [:type, :typep, :opaque, :spec, :impl, :doc, :moduledoc, :typedoc, :behaviour,
                   :derive, :enforce_keys, :callback, :macrocallback, :optional_callbacks, :dialyzer,
                   :external_resource, :on_load, :before_compile, :after_compile, :compile, :deprecated]
  defp subst_attrs(body) do
    {rev, _} =
      Enum.reduce(body, {[], %{}}, fn
        {:@, _, [{name, _, [value]}]} = s, {acc, attrs} when name not in @compiler_attrs ->
          if literal?(value), do: {acc, Map.put(attrs, name, value)}, else: {[s | acc], attrs}
        s, {acc, attrs} ->
          s2 =
            Macro.prewalk(s, fn
              {:@, _, [{name, _, nil}]} = n when is_atom(name) ->
                case Map.fetch(attrs, name) do
                  {:ok, v} -> v
                  :error -> n
                end
              n -> n
            end)
          {[s2 | acc], attrs}
      end)
    Enum.reverse(rev)
  end

  defp literal?(x) when is_atom(x) or is_integer(x) or is_binary(x), do: true
  defp literal?(xs) when is_list(xs), do: Enum.all?(xs, &literal?/1)
  defp literal?({a, b}), do: literal?(a) and literal?(b)
  defp literal?({:{}, _, xs}), do: Enum.all?(xs, &literal?/1)
  defp literal?(_), do: false

  # ---------- types ----------

  # Local @type declarations, keyed {module, name}, and the module's
  # defstruct (field, default) pairs
  defp collect_raw_types(ctx, mod, body) do
    Enum.reduce(body, ctx, fn
      {:@, _, [{:type, _, [{:"::", _, [{tname, _, _}, t]}]}]}, c ->
        put_in(c.types[{mod, tname}], t)
      {:defstruct, _, [fields]}, c ->
        Map.has_key?(c.structs, mod) && fail("#{mod}: more than one defstruct")
        pairs =
          Enum.map(fields, fn
            {f, d} when is_atom(f) -> {f, d}
            f when is_atom(f) -> {f, nil}
            other -> fail("#{mod}: unsupported defstruct field #{Macro.to_string(other)}")
          end)
        %{c | structs: Map.put(c.structs, mod, pairs), struct_order: c.struct_order ++ [mod]}
      _, c -> c
    end)
  end

  # The Lean fields of every struct: [{name, lean type, default AST}] in
  # defstruct order, keyed by the Lean name (the module name). A field's type
  # comes from `@type t :: %__MODULE__{f: T, ..}`; without one it is read
  # off the default (an integer is Nat or Int, a boolean Bool), and
  # anything else needs the declaration.
  defp collect_structs(ctx) do
    structs =
      for {mod, pairs} <- ctx.structs, into: %{} do
        declared =
          case Map.fetch(ctx.types, {mod, :t}) do
            {:ok, {:%, _, [{:__MODULE__, _, _}, {:%{}, _, kvs}]}} -> Map.new(kvs)
            {:ok, other} -> fail("#{mod}: @type t must be %__MODULE__{field: type, ..}, got #{Macro.to_string(other)}")
            :error -> %{}
          end
        Enum.each(Map.keys(declared), fn f ->
          List.keymember?(pairs, f, 0) || fail("#{mod}: @type t mentions #{f}, which is not a defstruct field")
        end)
        fields =
          for {f, d} <- pairs do
            t =
              case Map.fetch(declared, f) do
                {:ok, t} -> lean_type(ctx, mod, t)
                :error ->
                  cond do
                    is_integer(d) and d >= 0 -> "Nat"
                    is_integer(d) -> "Int"
                    is_boolean(d) -> "Bool"
                    true -> fail("#{mod}: declare the type of struct field #{f} in @type t :: %__MODULE__{#{f}: ..}")
                  end
              end
            {Atom.to_string(f), t, d}
          end
        {struct_name(mod), fields}
      end
    %{ctx | structs: structs}
  end

  defp struct_name(mod), do: Atom.to_string(mod)

  # a module that declares a struct and neither callbacks nor a receive loop
  defp struct_only?(ctx, mod, body) do
    Map.has_key?(ctx.structs, struct_name(mod)) and loop_of(body) == nil and
      not Enum.any?(body, fn
        {:def, _, [head, _]} -> elem(head_parts(head), 0) in [:handle_cast, :handle_info, :handle_call, :handle_continue]
        _ -> false
      end)
  end

  # the fields [{name, type, default}] of a Lean struct type, or nil
  defp struct_fields(nil), do: nil
  defp struct_fields(t), do: Map.get(Process.get(:to_lean_structs, %{}), t)

  # the struct a state constructor flattens, or nil
  defp struct_state_of(ctor), do: Map.get(Process.get(:to_lean_struct_states, %{}), ctor)

  # The message and state constructors of a GenServer module
  defp collect_types(ctx, mod, body) do
    ctx
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
      {fields, c} = state_fields(c, mod, st)
      fields = fields ++ if(after?, do: [{"gen", "Nat"}], else: [])
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

  # A state type becomes one constructor of St with positional fields; a
  # state that is a struct (the module's own `t()` or `%__MODULE__{}`, or
  # another module's) is flattened into one field per struct field, in
  # defstruct order and under the struct's field names.
  defp state_fields(ctx, mod, {:{}, _, ts}), do: {ts |> Enum.with_index() |> Enum.map(fn {t, i} -> {"f#{i}", lean_type(ctx, mod, t)} end), ctx}
  defp state_fields(ctx, mod, {a, b}), do: state_fields(ctx, mod, {:{}, [], [a, b]})
  defp state_fields(ctx, mod, t) do
    lt = lean_type(ctx, mod, t)
    case Map.get(ctx.structs, lt) do
      nil -> {[{"s", lt}], ctx}
      fields -> {Enum.map(fields, fn {f, ft, _} -> {f, ft} end), %{ctx | struct_states: Map.put(ctx.struct_states, ctor_name(mod), lt)}}
    end
  end

  # Elixir type AST -> Lean type (string)
  defp lean_type(_ctx, _mod, {:pid, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:GenServer]}, :from]}, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {:integer, _, []}), do: "Int"
  defp lean_type(_ctx, _mod, {:non_neg_integer, _, []}), do: "Nat"
  defp lean_type(_ctx, _mod, {:boolean, _, []}), do: "Bool"
  # a struct type: the module's own `%__MODULE__{}`, or `%Mod{}` (the fields
  # in the type, if any, are checked by collect_structs for `@type t`)
  defp lean_type(ctx, mod, {:%, _, [{:__MODULE__, _, _}, {:%{}, _, _}]}), do: struct_type(ctx, mod)
  defp lean_type(ctx, _mod, {:%, _, [{:__aliases__, _, [m]}, {:%{}, _, _}]}), do: struct_type(ctx, m)
  # a remote type `Mod.name()`
  defp lean_type(ctx, _mod, {{:., _, [{:__aliases__, _, [m]}, name]}, _, []}) when is_atom(name) do
    case Map.fetch(ctx.types, {m, name}) do
      {:ok, t} -> named_type(ctx, m, name, t)
      :error -> fail("unknown type #{m}.#{name}()")
    end
  end
  # `:queue.queue(T)` is a list, oldest first (see the :queue calls in `expr`)
  defp lean_type(ctx, mod, {{:., _, [:queue, :queue]}, _, [t]}), do: "List " <> paren(lean_type(ctx, mod, t))
  defp lean_type(_ctx, _mod, {{:., _, [:queue, :queue]}, _, []} = t), do: fail("#{Macro.to_string(t)} needs an element type: :queue.queue(T)")
  defp lean_type(ctx, mod, a) when is_atom(a) and a not in [nil, true, false], do: enum_name(ctx, mod, [a])
  defp lean_type(ctx, mod, [t]), do: "List " <> paren(lean_type(ctx, mod, t))
  # a map %{K => V} is an association list; see Leanactors/AssocList.lean
  defp lean_type(ctx, mod, {:%{}, _, [{k, v}]}),
    do: "List (" <> lean_type(ctx, mod, k) <> " × " <> lean_type(ctx, mod, v) <> ")"
  defp lean_type(_ctx, _mod, {:%{}, _, _} = t), do: fail("a map type needs exactly one `K => V` pair: #{Macro.to_string(t)}")
  defp lean_type(ctx, mod, {:|, _, _} = u) do
    alts = union(u)
    cond do
      Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil) ->
        enum_name(ctx, mod, alts)
      tagged_union?(alts) ->
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

  defp struct_type(ctx, mod) do
    name = struct_name(mod)
    Map.has_key?(ctx.structs, mod) or Map.has_key?(ctx.structs, name) ||
      fail("#{mod} declares no defstruct")
    name
  end

  # A named local type that is a union of atoms becomes a Lean enum with the
  # capitalised name, a tagged union a Lean inductive with the same name;
  # anything else is inlined.
  defp named_type(ctx, mod, name, t) do
    alts = union(t)
    if (Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil)) or tagged_union?(alts),
      do: name |> Atom.to_string() |> String.capitalize(),
      else: lean_type(ctx, mod, t)
  end

  # A tagged union: alternatives are atoms and tagged tuples `{:tag, T...}`,
  # at least one of them a tuple (all atoms is an enum, `T | nil` is Option).
  defp tagged_union?(alts) do
    Enum.any?(alts, &tagged_tuple?/1) and
      Enum.all?(alts, fn a -> tagged_tuple?(a) or (is_atom(a) and a not in [nil, true, false]) end)
  end

  defp tagged_tuple?({a, _}) when is_atom(a) and a not in [nil, true, false], do: true
  defp tagged_tuple?({:{}, _, [a | _]}) when is_atom(a) and a not in [nil, true, false], do: true
  defp tagged_tuple?(_), do: false

  # the @type names that are never rendered as enums: the message unions and
  # the continue union (a continue never enters a mailbox, see handle_continue)
  @not_enums [:msg, :cast, :info, :call, :continue]

  # Lean name -> [{tag, [field types]}] for every named tagged union of the
  # source (a message union is never one: it becomes Msg)
  defp tagged_unions(ctx) do
    for {{mod, name}, t} <- ctx.types, name not in @not_enums, alts = union(t), tagged_union?(alts), into: %{} do
      ctors =
        for alt <- alts do
          {tag, args} = tuple_tag(alt)
          {tag, Enum.map(args, &lean_type(ctx, mod, &1))}
        end
      {name |> Atom.to_string() |> String.capitalize(), ctors}
    end
  end

  defp tuple_tag(a) when is_atom(a), do: {a, []}
  defp tuple_tag({a, b}), do: {a, [b]}
  defp tuple_tag({:{}, _, [a | rest]}), do: {a, rest}

  # the constructors of a Lean tagged union type, or nil
  defp union_ctors(nil), do: nil
  defp union_ctors(t), do: Map.get(Process.get(:to_lean_unions, %{}), t)

  # `List (K × V)` -> {K, V}, or nil for any other type
  defp map_type(nil), do: nil
  defp map_type("List (" <> rest) do
    case rest |> String.replace_suffix(")", "") |> split_top(0, "", " × ") do
      [k, v] -> {k, v}
      _ -> nil
    end
  end
  defp map_type(_), do: nil

  # `K × V` -> {K, V}, or nil
  defp prod_type(nil), do: nil
  defp prod_type(t) do
    case split_top(t, 0, "", " × ") do
      [k, v] -> {k, v}
      _ -> nil
    end
  end

  # enum name -> its first alternative, the default `hd/1` falls back to
  defp first_ctors(ctx) do
    for {{_mod, name}, t} <- ctx.types,
        name not in @not_enums,
        alts = union(t),
        alts != [] and Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil),
        into: %{},
        do: {name |> Atom.to_string() |> String.capitalize(), ".#{hd(alts)}"}
  end

  defp enum_name(ctx, mod, alts) do
    # find the @type whose union is exactly these atoms (not a message union)
    case Enum.find(ctx.types, fn {{m, n}, t} -> m == mod and n not in @not_enums and union(t) == alts end) do
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
        conts = continues_of(mod, body)
        for {:def, _, [head, [do: b]]} <- body,
            {fname, args, guard} = head_parts(head),
            fname in [:handle_cast, :handle_info, :handle_call],
            cl = clause_of(mod, fname, args, guard, b),
            cl != nil do
          inline_continues(mod, conts, cl)
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
      for {:def, _, [head, _]} <- body, {f, _, _} = head_parts(head), f in [:handle_cast, :handle_info, :handle_call, :handle_continue], do: f
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

  # ---------- handle_continue ----------

  # `handle_continue/2` clauses of a GenServer module, in source order:
  # {argument pattern, state pattern, body}. Guards are not supported.
  defp continues_of(mod, body) do
    for {:def, _, [head, [do: b]]} <- body,
        {fname, args, guard} = head_parts(head),
        fname == :handle_continue do
      guard == nil || fail("#{mod}: a guard on handle_continue is not supported")
      case args do
        [xpat, spat] -> {xpat, spat, b}
        _ -> fail("#{mod}: handle_continue must take two arguments")
      end
    end
  end

  @continue_depth 3

  # On the BEAM `{:noreply, e, {:continue, x}}` and `{:reply, r, e,
  # {:continue, x}}` run `handle_continue(x, e)` before any queued message
  # is looked at, so the continue is not a message and a self-send would be
  # wrong (it would queue behind the mailbox). The clause body is rewritten
  # instead: the matching handle_continue body follows the clause's own
  # statements (and its reply, kept as the marker statement `__reply__(r)`
  # that `sends` renders), with x and e substituted for the continue
  # clause's patterns. The continue body's tail may continue again, up to
  # @continue_depth deep. Pattern variables the rewritten body no longer
  # uses are renamed `_v`.
  defp inline_continues(mod, conts, cl) do
    {body, cl} = inline_tail(mod, conts, cl, cl.body, 0)
    cl = %{cl | body: body}
    case cl[:whole_parts] do
      nil -> cl
      {v, n} ->
        # the continue destructured the clause's whole-state variable into
        # the Lean parts v_0 .. v_{n-1}; when the rewritten body no longer
        # uses the variable itself, the state pattern becomes that tuple
        name = lean_ident(Atom.to_string(v))
        if Atom.to_string(v) in free_vars(body),
          do: prune_clause(cl),
          else: prune_clause(%{cl | spat: {:{}, [], for(i <- 0..(n - 1), do: {:"#{name}_#{i}", [], nil})}})
    end
  end

  # {rewritten body, clause}: the clause comes back marked `inlined` and,
  # when a continue destructured its whole-state variable, with `whole_parts`
  defp inline_tail(mod, conts, cl, {:if, m, [c, [do: a, else: b]]}, d) do
    {a, cl} = inline_tail(mod, conts, cl, a, d)
    {b, cl} = inline_tail(mod, conts, cl, b, d)
    {{:if, m, [c, [do: a, else: b]]}, cl}
  end
  defp inline_tail(mod, conts, cl, {:case, m, [s, [do: arms]]}, d) do
    {arms, cl} =
      Enum.map_reduce(arms, cl, fn {:->, am, [p, b]}, c ->
        {b, c} = inline_tail(mod, conts, c, b, d)
        {{:->, am, [p, b]}, c}
      end)
    {{:case, m, [s, [do: arms]]}, cl}
  end
  defp inline_tail(mod, conts, cl, b, d) do
    {init, [last]} = Enum.split(stmts(b), -1)
    case last do
      {:{}, _, [:noreply, e, {:continue, x}]} -> continue_into(mod, conts, cl, init, e, x, d)
      {:{}, _, [:reply, r, e, {:continue, x}]} -> continue_into(mod, conts, cl, init ++ [{:__reply__, [], [r]}], e, x, d)
      _ -> {b, cl}
    end
  end

  defp continue_into(mod, conts, cl, pre, e, x, d) do
    d < @continue_depth || fail("#{mod}: handle_continue nesting deeper than #{@continue_depth} (a continue loop?)")
    {xpat, spat, cbody} =
      Enum.find(conts, fn {xp, _, _} -> static_match?(mod, xp, x) end) ||
        fail("#{mod}: no handle_continue clause matches {:continue, #{Macro.to_string(x)}}")
    {sbinds, cl} = bind_continue_state(mod, cl, spat, e)
    binds = Map.merge(bind_pat(xpat, x), sbinds)
    # the continue body is inlined in the clause's scope: its own variables
    # (case arms) must not shadow the clause's
    outer = all_vars([cl.mpat, cl.spat, cl.from]) |> Enum.map(&Atom.to_string/1)
    locals = free_vars(cbody) -- Enum.map(Map.keys(binds), &Atom.to_string/1)
    case Enum.filter(locals, &(&1 in outer and not String.starts_with?(&1, "_"))) do
      [] -> :ok
      [v | _] -> fail("#{mod}: handle_continue body variable #{v} shadows a variable of the clause; rename it")
    end
    subst =
      Macro.postwalk(cbody, fn
        {v, _, nil} = n when is_atom(v) -> Map.get(binds, v, n)
        n -> n
      end)
    {cont, cl} = inline_tail(mod, conts, Map.put(cl, :inlined, true), subst, d + 1)
    {prepend_stmts(pre, cont), cl}
  end

  # does the handle_continue argument pattern match the continue value x?
  # Decided from the source: a variable matches anything, a literal is
  # compared with a literal, tuples positionally; a literal against a
  # non-literal cannot be decided and is an error rather than a guess.
  defp static_match?(_mod, {v, _, nil}, _x) when is_atom(v), do: true
  defp static_match?(mod, p, {v, _, nil} = x) when is_atom(v),
    do: fail("#{mod}: cannot decide from the source whether handle_continue pattern #{Macro.to_string(p)} matches #{Macro.to_string(x)}")
  defp static_match?(mod, {:{}, _, ps}, {:{}, _, xs}) when length(ps) == length(xs),
    do: Enum.zip(ps, xs) |> Enum.all?(fn {p, x} -> static_match?(mod, p, x) end)
  defp static_match?(mod, {a, b}, {c, d}), do: static_match?(mod, a, c) and static_match?(mod, b, d)
  defp static_match?(_mod, p, x) when is_atom(p) or is_integer(p), do: p == x
  # tuples of different shapes
  defp static_match?(_mod, {:{}, _, _}, _x), do: false
  defp static_match?(_mod, {_, _}, _x), do: false
  defp static_match?(mod, p, _x), do: fail("#{mod}: unsupported handle_continue pattern #{Macro.to_string(p)}")

  # variable -> expression bindings of a pattern against a value of the same shape
  defp bind_pat({:_, _, nil}, _x), do: %{}
  defp bind_pat({v, _, nil}, x) when is_atom(v), do: %{v => x}
  defp bind_pat({:{}, _, ps}, {:{}, _, xs}), do: Enum.zip(ps, xs) |> Enum.reduce(%{}, fn {p, x}, acc -> Map.merge(acc, bind_pat(p, x)) end)
  defp bind_pat({a, b}, {c, d}), do: Map.merge(bind_pat(a, c), bind_pat(b, d))
  defp bind_pat(_lit, _x), do: %{}

  # The continue's state pattern against the new state e: a variable is
  # bound to e; a tuple of variables to the parts of a tuple literal e, or,
  # when e is the clause's own whole-state variable, to that state's fields,
  # which are the Lean parts `s_0, s_1, ..` the whole-state pattern binds
  # (see `pat`; `inline_continues` turns the pattern into that tuple when
  # the variable itself is no longer used).
  defp bind_continue_state(_mod, cl, {v, _, nil} = p, e) when is_atom(v), do: {bind_pat(p, e), cl}
  defp bind_continue_state(mod, cl, spat, e) do
    ps = tuple_parts(spat) || fail("#{mod}: unsupported handle_continue state pattern #{Macro.to_string(spat)}")
    Enum.each(ps, fn
      {v, _, nil} when is_atom(v) -> :ok
      p -> fail("#{mod}: handle_continue state pattern must be a variable or a tuple of variables, got #{Macro.to_string(p)}")
    end)
    case {tuple_parts(e), e, cl.spat} do
      {xs, _, _} when is_list(xs) and length(xs) == length(ps) ->
        {bind_pat(spat, e), cl}
      {nil, {v, _, nil}, {v, _, nil}} when is_atom(v) ->
        name = lean_ident(Atom.to_string(v))
        binds = ps |> Enum.with_index() |> Enum.reduce(%{}, fn {p, i}, acc -> Map.merge(acc, bind_pat(p, {:"#{name}_#{i}", [], nil})) end)
        {binds, Map.put(cl, :whole_parts, {v, length(ps)})}
      _ -> fail("#{mod}: handle_continue state pattern #{Macro.to_string(spat)} cannot be bound to #{Macro.to_string(e)}")
    end
  end

  defp tuple_parts({:{}, _, xs}), do: xs
  defp tuple_parts({a, b}), do: [a, b]
  defp tuple_parts(_), do: nil

  # every variable occurrence (not deduplicated), as atoms
  defp all_vars(ast) do
    {_, vs} = Macro.prewalk(ast, [], fn
      {v, _, nil} = n, acc when is_atom(v) and v != :__MODULE__ -> {n, [v | acc]}
      n, acc -> {n, acc}
    end)
    Enum.reverse(vs)
  end

  # the statements before a continue go in front of the inlined body, into
  # every branch when that body is an `if` or `case`
  defp prepend_stmts([], body), do: body
  defp prepend_stmts(pre, {:if, m, [c, [do: a, else: b]]}),
    do: {:if, m, [c, [do: prepend_stmts(pre, a), else: prepend_stmts(pre, b)]]}
  defp prepend_stmts(pre, {:case, m, [s, [do: arms]]}),
    do: {:case, m, [s, [do: for({:->, am, [p, b]} <- arms, do: {:->, am, [p, prepend_stmts(pre, b)]})]]}
  defp prepend_stmts(pre, b), do: {:__block__, [], pre ++ stmts(b)}

  # Pattern variables the rewritten body does not use are renamed `_v`
  # (Lean warns on unused pattern variables; on the BEAM they were used by
  # the state the continue received). A variable that occurs twice in the
  # patterns (an equality guard), and a clause with a guard or an
  # exit/raise/throw (they rebuild the state from the parts) keep them.
  defp prune_clause(%{guard: nil, inlined: true} = cl) do
    if needs_state?(cl.body) do
      cl
    else
      used = free_vars(cl.body)
      counts = all_vars([cl.mpat, cl.spat, cl.from]) |> Enum.frequencies()
      rename = fn pat ->
        Macro.postwalk(pat, fn
          {v, m, nil} = n when is_atom(v) ->
            s = Atom.to_string(v)
            if s in used or String.starts_with?(s, "_") or counts[v] > 1, do: n, else: {:"_#{s}", m, nil}
          n -> n
        end)
      end
      %{cl | mpat: rename.(cl.mpat), spat: rename.(cl.spat)}
    end
  end
  defp prune_clause(cl), do: cl

  defp head_parts({:when, _, [{f, _, args}, g]}), do: {f, args, g}
  defp head_parts({f, _, args}), do: {f, args, nil}

  # ---------- rendering ----------

  defp render(ctx, clauses) do
    enums =
      for {{mod, name}, t} <- ctx.types,
          alts = union(t),
          Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil),
          name not in @not_enums do
        _ = mod
        ename = name |> Atom.to_string() |> String.capitalize()
        "inductive #{ename}\n" <> Enum.map_join(alts, "\n", &"  | #{&1}") <> "\n  deriving Repr, DecidableEq\n"
      end
      |> Enum.uniq()

    # tagged unions, after the enums their fields may mention
    unions =
      for {name, ctors} <- Process.get(:to_lean_unions, %{}) |> Enum.sort() do
        "inductive #{name}\n" <>
          Enum.map_join(ctors, "\n", fn {tag, ts} ->
            String.trim_trailing("  | #{tag} " <> (ts |> Enum.with_index() |> Enum.map_join(" ", fn {t, i} -> "(a#{i} : #{t})" end)))
          end) <> "\n  deriving Repr, DecidableEq\n"
      end
    # structs, in source order, when some message, state field, union or
    # other struct mentions them as a value type (a struct that is only
    # the flattened state of its module is not emitted)
    struct_names = Enum.map(ctx.struct_order, &struct_name/1)
    base_types =
      Enum.flat_map(ctx.msg_ctors, &elem(&1, 1)) ++
        Enum.flat_map(ctx.st_ctors, fn {_, fields} -> Enum.map(fields, &elem(&1, 1)) end) ++
        Enum.flat_map(Map.values(Process.get(:to_lean_unions, %{})), fn ctors -> Enum.flat_map(ctors, &elem(&1, 1)) end)
    mentioned = fn types, name -> Enum.any?(types, &Regex.match?(~r/\b#{name}\b/, &1)) end
    used_structs =
      Enum.reduce(struct_names, [], fn _, acc ->
        for name <- struct_names, name not in acc,
            mentioned.(base_types ++ Enum.flat_map(acc, fn n -> Enum.map(ctx.structs[n], &elem(&1, 1)) end), name),
            reduce: acc do
          a -> a ++ [name]
        end
      end)
    used_structs = Enum.filter(struct_names, &(&1 in used_structs))
    structs =
      for name <- used_structs do
        "structure #{name} where\n" <>
          Enum.map_join(ctx.structs[name], "\n", fn {f, t, d} -> "  #{f} : #{t} := #{expr(%{}, d, t)}" end) <>
          "\n  deriving Repr, DecidableEq\n"
      end
    enums = enums ++ unions ++ structs

    # a map anywhere in the types needs the association-list helpers
    all_types = base_types ++ Enum.flat_map(used_structs, fn n -> Enum.map(ctx.structs[n], &elem(&1, 1)) end)
    maps_import = if Enum.any?(all_types, &String.contains?(&1, " × ")), do: "import Leanactors.AssocList\n", else: ""

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
    #{maps_import}
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

  defp default_of(ctx, t) when is_map_key(ctx.structs, t), do: "({} : #{t})"
  defp default_of(_ctx, "Pid"), do: "p"
  defp default_of(_ctx, "Reason"), do: "r"
  defp default_of(_ctx, t) when t in ["Nat", "Int"], do: "0"
  defp default_of(_ctx, "Bool"), do: "false"
  defp default_of(_ctx, "List " <> _), do: "[]"
  defp default_of(_ctx, "Option " <> _), do: "none"
  defp default_of(ctx, t) do
    case Enum.find(ctx.types, fn {{_, n}, _} -> n |> Atom.to_string() |> String.capitalize() == t end) do
      {_, u} ->
        case tuple_tag(List.first(union(u))) do
          {tag, []} -> ".#{tag}"
          {tag, _} ->
            {^tag, ts} = List.keyfind(union_ctors(t), tag, 0)
            "(.#{tag} " <> Enum.map_join(ts, " ", &paren_or(default_of(ctx, &1))) <> ")"
        end
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
      binds = env[:__mapbinds__] || []
      {rhs, c, deferred} =
        cond do
          # the after body runs only for the current generation; a stale
          # after-message was cancelled on the BEAM, so it is consumed and
          # ignored (state unchanged, no re-entry), not deferred
          cl[:after] -> {"if gen' = gen then #{body_str} else (#{sp}, [])", c, false}
          guard_str == [] and binds == [] -> {body_str, c, false}
          true ->
            {fallback, c, deferred} = fallthrough(c, clauses, i, env, sp)
            inner = if guard_str == [], do: body_str, else: "if #{Enum.join(guard_str, " ∧ ")} then #{body_str} else #{fallback}"
            # a map pattern's fresh value variables are bound outside the
            # guards, innermost last, so the guards may mention them
            rhs =
              Enum.reduce(Enum.reverse(binds), inner, fn {m, k, v}, acc ->
                "(match AssocList.get? #{m} #{paren_or(k)} with | some #{v} => #{acc} | none => #{fallback})"
              end)
            {rhs, c, deferred}
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
  # a struct pattern `⟨..⟩`, possibly named `e@⟨..⟩`: the one constructor
  defp head_of("⟨" <> _), do: {:ctor, "mk"}
  defp head_of("." <> name), do: {:ctor, name}
  defp head_of("(." <> _ = p), do: {:ctor, p |> String.slice(2..-1//1) |> String.split(" ", parts: 2) |> hd() |> String.trim_trailing(")")}
  defp head_of("(" <> _ = p), do: if(length(split_cons(p)) == 2, do: :cons, else: {:opaque, p})
  defp head_of(p) do
    cond do
      plain?(p) or p == "_" -> :var
      String.contains?(p, "@⟨") -> {:ctor, "mk"}
      true -> {:opaque, p}
    end
  end

  # `e@⟨a, b⟩` -> `⟨a, b⟩`
  defp strip_at(p) do
    case String.split(p, "@", parts: 2) do
      [name, rest] -> if plain?(name), do: rest, else: p
      _ -> p
    end
  end

  defp signature(_ctx, "Bool"), do: [{:true, []}, {:false, []}]
  defp signature(_ctx, "Option " <> inner), do: [{:none, []}, {:some, [unparen(inner)]}]
  defp signature(_ctx, "List " <> inner = t), do: [{:nil, []}, {:cons, [unparen(inner), t]}]
  defp signature(ctx, t) do
    case {struct_fields(t), union_ctors(t)} do
      {fields, _} when fields != nil -> [{{:ctor, "mk"}, Enum.map(fields, &elem(&1, 1))}]
      {_, nil} ->
        case Enum.find(ctx.types, fn {{_, n}, _} -> n |> Atom.to_string() |> String.capitalize() == t end) do
          {_, u} ->
            if(enum_type?(t) and Enum.all?(union(u), &is_atom/1),
              do: for(a <- union(u), do: {{:ctor, Atom.to_string(a)}, []}),
              else: nil)
          nil -> nil
        end
      {_, ctors} -> for {tag, ts} <- ctors, do: {{:ctor, Atom.to_string(tag)}, ts}
    end
  end

  defp sub_parts("(some " <> rest, :some), do: [String.replace_suffix(rest, ")", "")]
  defp sub_parts(p, :cons), do: split_cons(p)
  defp sub_parts("(." <> _ = p, {:ctor, _}), do: split_ctor_args(p)
  defp sub_parts(p, {:ctor, "mk"}) do
    case strip_at(p) do
      "⟨" <> rest -> rest |> String.replace_suffix("⟩", "") |> split_top(0, "", ", ")
      _ -> []
    end
  end
  defp sub_parts(_, _), do: []

  # `(h :: t)` -> ["h", "t"], splitting at the top-level `::` only
  defp split_cons("(" <> rest), do: rest |> String.replace_suffix(")", "") |> split_top(0, "", " :: ")
  # `(.tag a (some b))` -> ["a", "(some b)"]: the constructor's arguments
  defp split_ctor_args("(" <> rest), do: rest |> String.replace_suffix(")", "") |> split_top(0, "", " ") |> tl()
  # split a string at the top-level (outside parentheses) occurrences of `sep`
  defp split_top("", _, acc, _sep), do: [acc]
  defp split_top(s, 0, acc, sep) when binary_part(s, 0, byte_size(sep)) == sep and byte_size(s) >= byte_size(sep),
    do: [acc | split_top(binary_part(s, byte_size(sep), byte_size(s) - byte_size(sep)), 0, "", sep)]
  defp split_top("(" <> rest, d, acc, sep), do: split_top(rest, d + 1, acc <> "(", sep)
  defp split_top(")" <> rest, d, acc, sep), do: split_top(rest, d - 1, acc <> ")", sep)
  defp split_top("⟨" <> rest, d, acc, sep), do: split_top(rest, d + 1, acc <> "⟨", sep)
  defp split_top("⟩" <> rest, d, acc, sep), do: split_top(rest, d - 1, acc <> "⟩", sep)
  defp split_top(<<c::utf8, rest::binary>>, d, acc, sep), do: split_top(rest, d, acc <> <<c::utf8>>, sep)

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
  # a map pattern renders as a variable (its keys become guards), so it is
  # as bare as one for coverage and fallthrough; a struct pattern whose
  # fields are all variables matches every value of the struct
  defp bare?({:%{}, _, _}), do: true
  defp bare?({:=, _, [{:%{}, _, _}, {v, _, nil}]}) when is_atom(v), do: true
  defp bare?({:%, _, [_, {:%{}, _, kvs}]}), do: Enum.all?(kvs, fn {_, p} -> bare?(p) end)
  defp bare?({:=, _, [{:%, _, _} = p, {v, _, nil}]}) when is_atom(v), do: bare?(p)
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
      {:{}, _, [:noreply, _, t]} = n, _ when t != :hibernate -> {n, true}
      {:{}, _, [:reply, _, _, t]} = n, _ when t != :hibernate -> {n, true}
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
        env2 = if c.from, do: Map.put(env2, {:alias, from_var(c.from)}, env[:__from__]), else: env2
        env2 = if uses_self?(c), do: Map.put(env2, :__self__, true), else: env2
        {b, ctx} = body(ctx, c.mod, env2, c.body)
        if c.guard, do: fail("chained guards are not supported (clause #{i})")
        {b, ctx, false}
    end
  end

  # is `general` at least as general as `specific`? (var/_ or identical; a
  # tuple whose parts are all variables matches everything a variable does)
  defp general?({v, _, nil}, _) when is_atom(v), do: true
  # a map pattern is a variable in Lean (its keys are inlined guards)
  defp general?({:%{}, _, _}, _), do: true
  defp general?({:=, _, [{:%{}, _, _}, {v, _, nil}]}, _) when is_atom(v), do: true
  defp general?({:%, _, _} = p, _), do: bare?(p)
  defp general?({:=, _, [{:%, _, _} = p, {v, _, nil}]}, _) when is_atom(v), do: bare?(p)
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
      # a struct state: the general clause's `v.f` and `%{v | ..}` see the parts
      _ -> env |> Map.put({:alias, Atom.to_string(v)}, sp) |> Map.put("__whole__" <> Atom.to_string(v), env[:__vparts__])
    end
  end
  # the general clause names the struct state `%__MODULE__{} = v` or `%{} = v`
  defp whole_alias({:=, _, [{:%, _, [_, {:%{}, _, []}]}, {v, _, nil}]}, sp, fields, env) when is_atom(v),
    do: whole_alias({v, [], nil}, sp, fields, env)
  defp whole_alias({:=, _, [{:%{}, _, []}, {v, _, nil}]}, sp, fields, env) when is_atom(v),
    do: whole_alias({v, [], nil}, sp, fields, env)
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
    struct = Map.get(ctx.struct_states, ctor_name(cl.mod))
    {sub, whole} = state_subpats(cl.spat, length(vfields), struct, vfields)
    {vparts, env, gs} = pat_list(ctx, sub, Enum.map(vfields, &elem(&1, 1)), env, gs)
    # a struct state pattern `%__MODULE__{f: p} = v`: the whole variable
    # names all the parts, the named fields included
    env = if whole, do: Map.put(env, "__whole__" <> whole, vparts), else: env
    env = if struct, do: Map.put(env, :__struct_state__, struct), else: env
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

  # the source variable of a from pattern (for aliasing in a fallthrough)
  defp from_var({v, _, nil}) when is_atom(v), do: Atom.to_string(v)
  defp from_var({{v, _, nil}, _}) when is_atom(v), do: Atom.to_string(v)

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
  #
  # A struct state (`@type state :: t()`) takes a struct pattern
  # `%__MODULE__{f: p, ..}`, `%Mod{..}` or `%{f: p, ..}`, optionally `= v`:
  # the named fields take their patterns, the others are wildcards, or the
  # parts of `v` when the whole struct is named (returned as the second
  # component so `patterns` can bind `v` to every part).
  defp state_subpats({:=, _, [{:%, _, [_, {:%{}, _, kvs}]}, {v, _, nil}]}, _n, struct, fields) when is_atom(v) and struct != nil,
    do: {struct_subpats(struct, fields, kvs, v), Atom.to_string(v)}
  defp state_subpats({:=, _, [{:%{}, _, kvs}, {v, _, nil}]}, n, struct, fields) when is_atom(v) and struct != nil and n > 0,
    do: {struct_subpats(struct, fields, kvs, v), Atom.to_string(v)}
  defp state_subpats({:%, _, [_, {:%{}, _, kvs}]}, _n, struct, fields) when struct != nil,
    do: {struct_subpats(struct, fields, kvs, nil), nil}
  defp state_subpats({:%{}, _, kvs}, _n, struct, fields) when struct != nil and kvs != [],
    do: {struct_subpats(struct, fields, kvs, nil), nil}
  defp state_subpats(p, n, _struct, _fields), do: {state_subpats(p, n), nil}

  defp struct_subpats(struct, fields, kvs, v) do
    Enum.each(kvs, fn
      {k, _} when is_atom(k) -> List.keymember?(fields, Atom.to_string(k), 0) || fail("#{struct} has no field #{k}")
      {k, _} -> fail("struct pattern keys must be atoms, got #{Macro.to_string(k)}")
    end)
    fields
    |> Enum.with_index()
    |> Enum.map(fn {{f, _}, i} ->
      case List.keyfind(kvs, String.to_atom(f), 0) do
        {_, p} -> p
        nil -> if v, do: {:"__whole__#{v}@#{i}", [], nil}, else: {:_, [], nil}
      end
    end)
  end

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
  # `{:ok, p}` and `:error` at an Option position: the result of Map.fetch/2
  defp pat(ctx, {:ok, p}, "Option " <> inner, env, gs) do
    {ps, env, gs} = pat(ctx, p, unparen(inner), env, gs)
    {"(some #{ps})", env, gs}
  end
  defp pat(_ctx, :error, "Option " <> _, env, gs), do: {"none", env, gs}
  # `{:value, p}` and `:empty` at an Option position: the result of :queue.peek/1
  defp pat(ctx, {:value, p}, "Option " <> inner, env, gs) do
    {ps, env, gs} = pat(ctx, p, unparen(inner), env, gs)
    {"(some #{ps})", env, gs}
  end
  defp pat(_ctx, :empty, "Option " <> _, env, gs), do: {"none", env, gs}
  # A struct pattern `%Mod{f: p, ..}` (or `%{f: p, ..}` at a struct type) is
  # the anonymous constructor `⟨p0, p1, ..⟩` with a wildcard for every field
  # not mentioned; `%Mod{..} = v` names the whole value, `v@⟨..⟩`.
  defp pat(ctx, {:=, _, [{:%, _, _} = sp, {v, _, nil}]}, t, env, gs) when is_atom(v),
    do: pat(ctx, sp, t, Map.put(env, :__structalias__, lean_ident(Atom.to_string(v))), gs)
  defp pat(ctx, {:%, _, [m, {:%{}, _, kvs}]} = p, t, env, gs) do
    struct_fields(t) || fail("struct pattern #{Macro.to_string(p)} at non-struct type #{t}")
    case m do
      {:__aliases__, _, [name]} -> Atom.to_string(name) == t || fail("struct pattern #{Macro.to_string(p)} at type #{t}")
      _ -> :ok
    end
    struct_pat(ctx, t, kvs, env, gs)
  end
  # A map pattern. `%{}` matches any map (a wildcard). `%{k => p, ...}` with
  # literal keys binds the whole map to a fresh Lean name `map<i>` and adds
  # guards on it: `_` is `hasKey`, a literal or an already-bound variable is
  # `get? map k = some lit`, and a fresh variable v is bound by a `match
  # get? map k with | some v => .. | none => <fallthrough>` around the clause
  # body (see `render_clauses`). Keys are compared for equality only, so
  # they must be literals.
  defp pat(ctx, {:=, _, [{:%{}, _, _} = mp, {v, _, nil}]}, t, env, gs) when is_atom(v) do
    name = lean_ident(Atom.to_string(v))
    Map.has_key?(env, name) && fail("variable #{name} bound twice (map alias)")
    pat(ctx, mp, t, Map.put(env, :__mapalias__, name), gs)
  end
  # `%{f: p, ..}` at a struct type is a struct pattern, not a map pattern
  defp pat(ctx, {:%{}, _, pairs} = p, t, env, gs) do
    if struct_fields(t) != nil and pairs != [] do
      struct_pat(ctx, t, pairs, env, gs)
    else
      map_pat(ctx, p, t, env, gs)
    end
  end

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
        # a whole-state variable: bind field-wise as name_i and remember to
        # rebuild (`name@i` fixes the index: a struct pattern names some
        # fields itself)
        {name, i} =
          case String.split(name, "@") do
            [n, i] -> {n, String.to_integer(i)}
            [n] -> {n, map_size(Map.filter(env, fn {k, _} -> is_binary(k) and String.starts_with?(k, n <> "_") end))}
          end
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
  # a tagged tuple at a tagged-union type is a constructor; a pair at `K × V`
  # (a map entry) is a pair
  defp pat(ctx, p, t, env, gs) when is_tuple(p) and (tuple_size(p) == 2 or elem(p, 0) == :{}) do
    cond do
      union_ctors(t) != nil and tagged_tuple?(p) ->
        {tag, args} = tuple_tag(p)
        {^tag, ts} = List.keyfind(union_ctors(t), tag, 0) || fail("#{tag} is not an alternative of #{t}")
        length(args) == length(ts) || fail("arity mismatch for #{tag} at #{t}")
        {parts, env, gs} = pat_list(ctx, args, ts, env, gs)
        {"(.#{tag}" <> Enum.map_join(parts, "", &(" " <> &1)) <> ")", env, gs}
      prod_type(t) != nil and tuple_parts(p) != nil and length(tuple_parts(p)) == 2 ->
        {kt, vt} = prod_type(t)
        {parts, env, gs} = pat_list(ctx, tuple_parts(p), [kt, vt], env, gs)
        {"(#{Enum.join(parts, ", ")})", env, gs}
      true -> fail("unsupported pattern #{Macro.to_string(p)} at type #{t}")
    end
  end
  defp pat(_ctx, p, t, _env, _gs), do: fail("unsupported pattern #{Macro.to_string(p)} at type #{t}")

  defp map_pat(ctx, {:%{}, _, pairs} = p, t, env, gs) do
    {kt, vt} = map_type(t) || fail("map pattern #{Macro.to_string(p)} at non-map type #{t}")
    {alias_name, env} = Map.pop(env, :__mapalias__)
    if pairs == [] do
      if alias_name, do: {alias_name, Map.put(env, alias_name, t), gs}, else: pat(ctx, {:_, [], nil}, t, env, gs)
    else
      i = Map.get(env, :__maps__, 0)
      name = alias_name || "map#{i}"
      env = env |> Map.put(:__maps__, i + 1) |> Map.put(name, t)
      {env, gs} =
        Enum.reduce(pairs, {env, gs}, fn {k, vp}, {e, g} ->
          {ks, _, []} =
            if is_atom(k) or is_integer(k),
              do: pat(ctx, k, kt, %{}, []),
              else: fail("map pattern keys must be literals, got #{Macro.to_string(k)}")
          case vp do
            {:_, _, nil} -> {e, g ++ [{:map_has, name, ks}]}
            {v, _, nil} when is_atom(v) ->
              vn = lean_ident(Atom.to_string(v))
              cond do
                String.starts_with?(vn, "_") -> {e, g ++ [{:map_has, name, ks}]}
                Map.has_key?(e, vn) ->
                  e[vn] == vt || fail("variable #{vn} bound at #{e[vn]} reused at #{vt} in a map pattern")
                  {e, g ++ [{:map_eq, name, ks, vn}]}
                true ->
                  e = e |> Map.put(vn, vt) |> Map.update(:__mapbinds__, [{name, ks, vn}], &(&1 ++ [{name, ks, vn}]))
                  {e, g}
              end
            lit ->
              {ls, _, []} = pat(ctx, lit, vt, %{}, [])
              {e, g ++ [{:map_eq, name, ks, ls}]}
          end
        end)
      {name, env, gs}
    end
  end
  # a GenServer.from() value {pid, ref} matched at a Pid position: keep the pid
  # the fields of struct `t` against the pairs of a struct pattern
  defp struct_pat(ctx, t, kvs, env, gs) do
    fields = struct_fields(t)
    {alias_name, env} = Map.pop(env, :__structalias__)
    Enum.each(kvs, fn
      {k, _} when is_atom(k) -> List.keymember?(fields, Atom.to_string(k), 0) || fail("#{t} has no field #{k}")
      {k, _} -> fail("struct pattern keys must be atoms, got #{Macro.to_string(k)}")
    end)
    if alias_name && Map.has_key?(env, alias_name), do: fail("variable #{alias_name} bound twice (struct alias)")
    subs = for {f, ft, _} <- fields, do: {Keyword.get(kvs, String.to_atom(f), {:_, [], nil}), ft}
    {parts, env, gs} = pat_list(ctx, Enum.map(subs, &elem(&1, 0)), Enum.map(subs, &elem(&1, 1)), env, gs)
    cond do
      alias_name && kvs == [] -> {alias_name, Map.put(env, alias_name, t), gs}
      alias_name -> {"#{alias_name}@⟨#{Enum.join(parts, ", ")}⟩", Map.put(env, alias_name, t), gs}
      kvs == [] -> pat(ctx, {:_, [], nil}, t, env, gs)
      true -> {"⟨#{Enum.join(parts, ", ")}⟩", env, gs}
    end
  end

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
  defp guard_to_lean(_env, {:map_has, m, k}), do: "AssocList.hasKey #{m} #{paren_or(k)}"
  defp guard_to_lean(_env, {:map_eq, m, k, v}), do: "AssocList.get? #{m} #{paren_or(k)} = some #{paren_or(v)}"
  defp guard_to_lean(env, g), do: expr(env, g, nil)

  # ---------- bodies ----------

  # body -> "(state, [sends])" string; may be an if/case over whole bodies
  defp body(ctx, mod, env, {:if, _, [c, [do: a, else: b]]}) do
    {sa, ctx} = body(ctx, mod, env, a)
    {sb, ctx} = body(ctx, mod, env, b)
    {"if #{expr(env, c, nil)} then #{sa} else #{sb}", ctx}
  end
  # `case :queue.out(q)`: a match on the list itself, `{{:value, x}, rest}`
  # being `x :: rest` and `{:empty, q'}` being `[]` (with q' aliased to `[]`)
  defp body(ctx, mod, env, {:case, m, [{{:., _, [:queue, :out]}, _, [q]}, [do: arms]]}) do
    arms =
      for {:->, am, [[p], b]} <- arms do
        p2 =
          case p do
            {{:value, x}, rest} -> [{:|, [], [x, rest]}]
            {:empty, {v, _, nil}} when is_atom(v) -> {:__queue_empty__, [], [v]}
            _ -> fail("case :queue.out: arms must be {{:value, x}, rest} and {:empty, q}, got #{Macro.to_string(p)}")
          end
        {:->, am, [[p2], b]}
      end
    body(ctx, mod, env, {:case, m, [q, [do: arms]]})
  end
  defp body(ctx, mod, env, {:case, _, [scrut, [do: arms]]}) do
    st = guess_type(env, scrut)
    {arm_strs, {ctx, _}} =
      Enum.map_reduce(arms, {ctx, false}, fn {:->, _, [[p], b]}, {c, saw_nil} ->
        {pstr, env2, []} =
          case {p, st} do
            {{:__queue_empty__, _, [v]}, "List " <> _} ->
              name = lean_ident(Atom.to_string(v))
              env2 = if String.starts_with?(name, "_"), do: env, else: env |> Map.put(name, st) |> Map.put({:alias, Atom.to_string(v)}, "[]")
              {"[]", env2, []}
            # after a `nil` arm, a variable arm over an Option binds the value itself
            {{v, _, nil}, "Option " <> inner} when is_atom(v) and saw_nil ->
              name = lean_ident(Atom.to_string(v))
              if String.starts_with?(name, "_") or Map.has_key?(env, name),
                do: pat(c, p, st, env, []),
                else: {"(some #{name})", Map.put(env, name, unparen(inner)), []}
            _ -> pat(c, p, st, env, [])
          end
        {bs, c} = body(c, mod, env2, b)
        {"| #{pstr} => #{bs}", {c, saw_nil or p == nil}}
      end)
    {"(match #{expr(env, scrut, nil)} with " <> Enum.join(arm_strs, " ") <> ")", ctx}
  end
  defp body(ctx, mod, env, b), do: body_stmts(ctx, mod, env, stmts(b))

  # the rest of a body after a blocking call may be a single `if`/`case`
  defp body_stmts(ctx, mod, env, [{:if, _, _} = e]), do: body(ctx, mod, env, e)
  defp body_stmts(ctx, mod, env, [{:case, _, _} = e]), do: body(ctx, mod, env, e)
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
    {send_strs, ctx, env_after} = sends(ctx, env, before)
    this = wrap_lets(env_after, "(.#{await}#{cap_str}, [#{Enum.join(send_strs ++ [req], ", ")}])")
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
      {v, _, nil} = n, acc when is_atom(v) and v != :__MODULE__ -> {n, [Atom.to_string(v) | acc]}
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
          # the reply of a `{:reply, r, e, {:continue, x}}` clause, sent
          # before the inlined continue body's effects (see `inline_tail`)
          {:__reply__, _, [r]} -> {reply_str(c, e, r), {c, e}}
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
          # `{_, q} = :queue.out(q0)`: the queue without its oldest element
          # (`:queue.out` of an empty queue gives it back unchanged, as `tail` does)
          {:=, _, [{{:_, _, nil}, {v, _, nil}}, {{:., _, [:queue, :out]}, _, [q]}]} when is_atom(v) ->
            {nil, {c, let_bind(e, v, "List.tail #{paren_or(expr(e, q, type_of(e, q)))}", type_of(e, q))}}
          # a local binding `v = e` is a `let`
          {:=, _, [{v, _, nil}, rhs]} when is_atom(v) ->
            t = type_of(e, rhs)
            struct_state_of_type(t) && fail("#{v} = #{Macro.to_string(rhs)}: a whole state value cannot be bound; bind its fields or return it")
            {nil, {c, let_bind(e, v, expr(e, rhs, t), t)}}
          other -> fail("unsupported statement #{Macro.to_string(other)}")
        end
      end)
    {Enum.reject(strs, &is_nil/1), c, e}
  end

  # record `let v := s` (rendered by `wrap_lets` around the clause result)
  defp let_bind(env, v, s, t) do
    name = lean_ident(Atom.to_string(v))
    Map.has_key?(env, name) && fail("variable #{name} bound twice (let)")
    env
    |> Map.put(name, t)
    |> Map.update(:__lets__, ["let #{name} := #{s}"], &(&1 ++ ["let #{name} := #{s}"]))
  end

  defp wrap_lets(env, s) do
    case env[:__lets__] do
      nil -> s
      [] -> s
      lets -> "(" <> Enum.join(lets, "; ") <> "; " <> s <> ")"
    end
  end

  # is `t` the struct some module's state flattens? (such a value never
  # exists in the model: the state is the constructor)
  defp struct_state_of_type(nil), do: false
  defp struct_state_of_type(t), do: t in Map.values(Process.get(:to_lean_struct_states, %{}))

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
    timeout = fn ->
      List.keymember?(ctx.msg_ctors, :timeout, 0) || fail("GenServer timeout used but :timeout not in @type msg")
      ".sendAfter me .timeout"
    end
    {state, tail} =
      case last do
        {:noreply, e} -> {next_state.(e), []}
        {:{}, _, [:reply, r, e]} -> {next_state.(e), [reply_str(ctx, env, r)]}
        {:{}, _, [:noreply, _e, {:continue, x}]} ->
          fail("#{mod}: {:continue, #{Macro.to_string(x)}} outside a GenServer callback")
        # :hibernate is no timeout (and no effect the model can see)
        {:{}, _, [:noreply, e, :hibernate]} -> {next_state.(e), []}
        {:{}, _, [:noreply, e, _t]} -> {next_state.(e), [timeout.()]}
        {:{}, _, [:reply, r, e, :hibernate]} -> {next_state.(e), [reply_str(ctx, env, r)]}
        # the reply goes out, then the timeout is armed
        {:{}, _, [:reply, r, e, _t]} -> {next_state.(e), [reply_str(ctx, env, r), timeout.()]}
        {:{}, _, [:stop, r, e]} ->
          {next_state.(e), [".exit #{reason_str(r)}"]}
        # the reply goes out, then the process exits
        {:{}, _, [:stop, r, reply, e]} ->
          {next_state.(e), [reply_str(ctx, env, reply), ".exit #{reason_str(r)}"]}
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
    {wrap_lets(env, "(#{state}, [#{Enum.join(send_strs ++ tail, ", ")}])"), ctx}
  end

  # `.send <caller> (.reply r)`: the reply of a handle_call clause
  defp reply_str(ctx, env, r) do
    from = env[:__from__] || fail("{:reply, ...} outside handle_call")
    send_str(ctx, from, ".reply #{paren_or(expr(env, r, ctx.reply_type))}")
  end

  # the current state rebuilt from the clause's state pattern (for exit/1, raise, throw)
  defp whole_state(env, ctor, _fields) do
    case env[:__sparts__] do
      nil -> fail("exit/raise/throw needs the state bound by the pattern")
      parts -> if parts == [], do: ".#{ctor}", else: ".#{ctor} " <> Enum.join(parts, " ")
    end
  end

  defp guess_type(env, {v, _, nil}) when is_atom(v), do: Map.get(env, Atom.to_string(v)) || fail("untyped scrutinee #{v}")
  # `case Map.get(m, k)` / `case Map.fetch(m, k)` is a match on an Option
  defp guess_type(env, {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, [m | _]} = e) when f in [:get, :fetch] do
    {_, vt} = map_type(var_type(env, m)) || fail("case over #{Macro.to_string(e)}: #{Macro.to_string(m)} is not a map variable")
    case e do
      {_, _, [_, _]} -> "Option " <> paren_or(vt)
      _ -> vt
    end
  end
  defp guess_type(env, e),
    do: type_of(env, e) || fail("case scrutinee must be a variable, Map.get/Map.fetch, :queue.out/peek or an Enum call of known type, got #{Macro.to_string(e)}")

  # the Lean type of a variable bound by the patterns, or nil
  defp var_type(env, {v, _, nil}) when is_atom(v), do: Map.get(env, lean_ident(Atom.to_string(v)))
  defp var_type(_env, _), do: nil

  # rebuild the state constructor from an expression of the state type
  defp state_expr(env, e, ctor, fields) do
    case {struct_state_of(ctor), e} do
      {st, {:%, _, [m, {:%{}, _, kvs}]}} when st != nil ->
        case m do
          {:__aliases__, _, [name]} -> struct_name(name) == st || fail("#{Macro.to_string(e)} is not a #{st} (the state)")
          _ -> :ok
        end
        struct_state_expr(env, e, kvs, ctor, fields)
      {st, {:%{}, _, kvs}} when st != nil -> struct_state_expr(env, e, kvs, ctor, fields)
      _ -> state_expr_plain(env, e, ctor, fields)
    end
  end

  defp state_expr_plain(env, {:{}, _, xs}, ctor, fields) when length(xs) == length(fields),
    do: ".#{ctor} " <> Enum.map_join(Enum.zip(xs, fields), " ", fn {x, {_, t}} -> paren_or(expr(env, x, t)) end)
  defp state_expr_plain(env, {a, b}, ctor, [_, _] = fields), do: state_expr_plain(env, {:{}, [], [a, b]}, ctor, fields)
  defp state_expr_plain(env, {v, _, nil}, ctor, fields) when is_atom(v) and length(fields) > 1 do
    # whole-state variable: an alias from a fallthrough, or rebuilt from its pattern parts
    case Map.get(env, {:alias, Atom.to_string(v)}) do
      nil ->
        parts = Map.get(env, "__whole__" <> Atom.to_string(v)) || fail("whole-state variable #{v} not bound by a pattern")
        ".#{ctor} " <> Enum.join(parts, " ")
      s -> s
    end
  end
  defp state_expr_plain(env, e, ctor, [{_, t}]), do: ".#{ctor} " <> paren_or(expr(env, e, t))
  defp state_expr_plain(_env, e, _ctor, _fields), do: fail("state expression #{Macro.to_string(e)} does not fit the state type")

  defp struct_state_expr(env, e, kvs, ctor, fields) do
    sfields = struct_fields(struct_state_of(ctor))
    {base, kvs} =
      case kvs do
        [{:|, _, [b, kvs]}] -> {b, kvs}
        _ -> {nil, kvs}
      end
    Enum.each(kvs, fn
      {k, _} when is_atom(k) -> List.keymember?(sfields, Atom.to_string(k), 0) || fail("#{struct_state_of(ctor)} has no field #{k}")
      _ -> fail("struct fields must be atoms in #{Macro.to_string(e)}")
    end)
    base_parts =
      case base do
        nil -> Enum.map(sfields, fn {_, t, d} -> paren_or(expr(env, d, t)) end)
        {v, _, nil} when is_atom(v) ->
          Map.get(env, "__whole__" <> Atom.to_string(v)) ||
            fail("#{Macro.to_string(e)}: #{v} is not the state bound by the clause's pattern")
        other -> fail("#{Macro.to_string(e)}: the updated value must be the state variable, got #{Macro.to_string(other)}")
      end
    parts =
      Enum.zip([sfields, base_parts, fields])
      |> Enum.map(fn {{f, t, _}, part, _} ->
        case List.keyfind(kvs, String.to_atom(f), 0) do
          {_, x} -> paren_or(expr(env, x, t))
          nil -> part
        end
      end)
    ".#{ctor} " <> Enum.join(parts, " ")
  end

  defp msg_expr(ctx, env, m) do
    {tag, args} = msg_shape(m)
    {^tag, ts} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("message #{tag} not declared")
    parts = Enum.zip(args, ts) |> Enum.map(fn {a, t} -> paren_or(expr(env, a, t)) end)
    if parts == [], do: ".#{tag}", else: ".#{tag} " <> Enum.join(parts, " ")
  end

  # expression -> Lean, with an expected type used only to insert some/none
  defp expr(_env, nil, "Option " <> _), do: "none"
  defp expr(_env, nil, nil), do: "none"
  defp expr(env, e, "Option " <> inner) do
    case e do
      {v, _, nil} when is_atom(v) ->
        name = lean_ident(Atom.to_string(v))
        case env[name] do
          "Option " <> _ -> Map.get(env, {:alias, Atom.to_string(v)}, name)
          _ -> "some #{expr(env, e, unparen(inner))}"
        end
      # Map.get/2, Map.fetch/2, Enum.at/2 and :queue.peek/1 already return one
      {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, [_, _]} when f in [:get, :fetch] -> expr(env, e, nil)
      {{:., _, [{:__aliases__, _, [:Enum]}, :at]}, _, [_, _]} -> expr(env, e, nil)
      {{:., _, [:queue, :peek]}, _, [_]} -> expr(env, e, nil)
      _ -> "some " <> paren_or(expr(env, e, unparen(inner)))
    end
  end
  defp expr(_env, {:self, _, []}, _t), do: "me"
  # ---- maps: Leanactors/AssocList.lean ----
  defp expr(_env, {:%{}, _, []}, t), do: if(struct_fields(t) != nil, do: "({} : #{t})", else: "[]")
  # `%{s | f: e, ..}`: a struct update when the base has a struct type
  defp expr(env, {:%{}, _, [{:|, _, [b, kvs]}]} = e, t) do
    st = t || type_of(env, b) || fail("#{Macro.to_string(e)}: the type of #{Macro.to_string(b)} is not known")
    struct_fields(st) || fail("#{Macro.to_string(e)}: #{st} is not a struct")
    check_fields(st, kvs)
    "{ #{expr(env, b, st)} with " <>
      Enum.map_join(kvs, ", ", fn {f, v} -> "#{f} := #{expr(env, v, field_type(st, f))}" end) <> " }"
  end
  # `%{f: e, ..}` at a struct type is a struct literal, otherwise a map
  defp expr(env, {:%{}, _, pairs} = e, t) do
    if struct_fields(t) != nil, do: struct_lit(env, t, pairs), else: map_lit(env, e, pairs, t)
  end
  defp expr(env, {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, args}, t), do: map_call(env, f, args, t)
  defp expr(env, {:is_map_key, _, [m, k]}, t), do: map_call(env, :has_key?, [m, k], t)
  defp expr(env, {:map_size, _, [m]}, _t), do: "AssocList.size #{paren_or(expr(env, m, nil))}"
  # ---- structs ----
  # `%Mod{f: e, ..}` is the Lean structure instance, the fields not named
  # taking their defstruct defaults; `x.f` is the field. The clause's own
  # state variable is not a value in the model (the state is a constructor
  # of St), so `state.f` is the pattern part that was bound to f.
  defp expr(env, {:%, _, [m, {:%{}, _, kvs}]} = e, t) do
    st =
      case m do
        {:__aliases__, _, [n]} -> Atom.to_string(n)
        _ -> t || fail("#{Macro.to_string(e)}: the struct type is not known")
      end
    struct_fields(st) || fail("#{Macro.to_string(e)}: #{st} is not a struct")
    (t == nil or t == st) || fail("#{Macro.to_string(e)} at type #{t}")
    struct_lit(env, st, kvs)
  end
  defp expr(env, {{:., _, [{v, _, nil}, f]}, _, []} = e, _t) when is_atom(v) and is_atom(f) do
    case state_field(env, v, f) do
      {part, _} -> part
      nil ->
        name = lean_ident(Atom.to_string(v))
        st = Map.get(env, name) || fail("#{Macro.to_string(e)}: the type of #{v} is not known")
        struct_fields(st) || fail("#{Macro.to_string(e)}: #{v} is not a struct (#{st})")
        field_type(st, f)
        "#{name}.#{f}"
    end
  end
  # ---- Enum over lists, and the list builtins ----
  defp expr(env, {{:., _, [{:__aliases__, _, [:Enum]}, f]}, _, args} = e, t), do: enum_call(env, e, f, args, t)
  defp expr(env, {:length, _, [l]}, _t), do: "List.length #{paren_or(expr(env, l, type_of(env, l)))}"
  defp expr(env, {:tl, _, [l]}, t), do: "List.tail #{paren_or(expr(env, l, t || type_of(env, l)))}"
  # `hd/1` raises on an empty list, which an expression cannot do here, so it
  # is `List.headD` at the element type's default value
  defp expr(env, {:hd, _, [l]}, t) do
    lt = type_of(env, l) || (t && "List " <> paren(t))
    et = t || elem_type(lt) || fail("hd/1: the element type of #{Macro.to_string(l)} is not known")
    "List.headD #{paren_or(expr(env, l, lt))} #{paren_or(default_expr(et))}"
  end
  defp expr(env, {:for, _, _} = e, t), do: comprehension(env, e, t)
  # ---- :queue as a list, oldest first ----
  defp expr(_env, {{:., _, [:queue, :new]}, _, []}, _t), do: "[]"
  defp expr(env, {{:., _, [:queue, :in]}, _, [x, q]}, t) do
    qt = t || type_of(env, q)
    "(#{expr(env, q, qt)} ++ [#{expr(env, x, elem_type(qt))}])"
  end
  defp expr(env, {{:., _, [:queue, :to_list]}, _, [q]}, t), do: expr(env, q, t || type_of(env, q))
  defp expr(env, {{:., _, [:queue, :len]}, _, [q]}, _t), do: "List.length #{paren_or(expr(env, q, type_of(env, q)))}"
  defp expr(env, {{:., _, [:queue, :is_empty]}, _, [q]}, _t), do: "List.isEmpty #{paren_or(expr(env, q, type_of(env, q)))}"
  defp expr(env, {{:., _, [:queue, :peek]}, _, [q]}, _t), do: "List.head? #{paren_or(expr(env, q, type_of(env, q)))}"
  defp expr(_env, {{:., _, [:queue, f]}, _, args} = e, _t) when is_list(args),
    do: fail("unsupported :queue function :queue.#{f}/#{length(args)} in #{Macro.to_string(e)}")
  defp expr(env, {:not, _, [a]}, _t), do: "(¬ #{expr(env, a, nil)})"
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
  # a pair at `K × V` (a map entry); a tagged tuple at a tagged-union type
  # (or at an unknown type, e.g. in a comparison) is a constructor
  defp expr(env, e, t) when is_tuple(e) and (tuple_size(e) == 2 or elem(e, 0) == :{}) do
    cond do
      prod_type(t) != nil and tuple_parts(e) != nil and length(tuple_parts(e)) == 2 ->
        {kt, vt} = prod_type(t)
        [a, b] = tuple_parts(e)
        "(#{expr(env, a, kt)}, #{expr(env, b, vt)})"
      tagged_tuple?(e) and (t == nil or union_ctors(t) != nil) ->
        {tag, args} = tuple_tag(e)
        ts =
          case union_ctors(t) do
            nil -> List.duplicate(nil, length(args))
            ctors ->
              {^tag, ts} = List.keyfind(ctors, tag, 0) || fail("#{tag} is not an alternative of #{t}")
              length(args) == length(ts) || fail("arity mismatch for #{tag} at #{t}")
              ts
          end
        "(.#{tag}" <> Enum.map_join(Enum.zip(args, ts), "", fn {a, at} -> " " <> paren_or(expr(env, a, at)) end) <> ")"
      true -> fail("unsupported expression #{Macro.to_string(e)}" <> if(t, do: " at type #{t}", else: ""))
    end
  end
  defp expr(_env, e, _t), do: fail("unsupported expression #{Macro.to_string(e)}")

  defp map_lit(env, e, pairs, t) do
    {kt, vt} = map_type(t) || fail("map literal #{Macro.to_string(e)} at #{t || "an unknown type"}: a map type is needed here")
    "[" <> Enum.map_join(pairs, ", ", fn {k, v} -> "(#{expr(env, k, kt)}, #{expr(env, v, vt)})" end) <> "]"
  end

  # `Map.f(args)` (and `is_map_key`) as the AssocList function. The map's
  # type comes from the expected type when that is the map (put, delete,
  # filter, reject) and from the map variable otherwise; it types the key,
  # the value and the entry of a filter/reject predicate.
  defp map_call(env, f, args, t) do
    m = List.first(args)
    mt = if(f in [:put, :delete, :filter, :reject], do: map_type(t), else: nil) || map_type(var_type(env, m))
    {kt, vt} = mt || {nil, nil}
    ms = paren_or(expr(env, m, if(mt, do: "List (#{kt} × #{vt})", else: nil)))
    key = fn k -> paren_or(expr(env, k, kt)) end
    case {f, args} do
      {f, [_, k]} when f in [:get, :fetch] ->
        (t == nil or match?("Option " <> _, t)) ||
          fail("Map.#{f}/2 returns a value or nil, used at type #{t}; use Map.get/3 or match on Map.fetch/2")
        "AssocList.get? #{ms} #{key.(k)}"
      {:get, [_, k, d]} -> "(AssocList.get? #{ms} #{key.(k)}).getD #{paren_or(expr(env, d, t || vt))}"
      {:put, [_, k, v]} -> "AssocList.insert #{ms} #{key.(k)} #{paren_or(expr(env, v, vt))}"
      {:delete, [_, k]} -> "AssocList.erase #{ms} #{key.(k)}"
      {:has_key?, [_, k]} -> "AssocList.hasKey #{ms} #{key.(k)}"
      {:keys, [_]} -> "AssocList.keys #{ms}"
      {:values, [_]} -> "AssocList.values #{ms}"
      {f, [_, {:fn, _, [{:->, _, [[{kp, vp}], body]}]}]} when f in [:filter, :reject] ->
        mt || fail("Map.#{f}: the type of #{Macro.to_string(m)} is not known")
        bind = fn
          {v, _, nil} when is_atom(v) -> lean_ident(Atom.to_string(v))
          other -> fail("Map.#{f}: the function must take a pair of variables, got #{Macro.to_string(other)}")
        end
        {kn, vn} = {bind.(kp), bind.(vp)}
        env2 = env |> Map.put(kn, kt) |> Map.put(vn, vt)
        "AssocList.#{f} #{ms} (fun (#{kn}, #{vn}) => #{expr(env2, body, "Bool")})"
      {f, [_, _]} when f in [:filter, :reject] ->
        fail("Map.#{f} takes a literal `fn {k, v} -> e end`")
      _ -> fail("unsupported map function Map.#{f}/#{length(args)}")
    end
  end

  # ---------- structs, Enum, :queue ----------

  # the fields of struct `t`, as declared by its defstruct and @type t
  defp field_type(st, f) do
    case List.keyfind(struct_fields(st), Atom.to_string(f), 0) do
      {_, t, _} -> t
      nil -> fail("#{st} has no field #{f}")
    end
  end

  defp check_fields(st, kvs) do
    Enum.each(kvs, fn
      {k, _} when is_atom(k) -> field_type(st, k)
      {k, _} -> fail("struct fields must be atoms, got #{Macro.to_string(k)}")
    end)
  end

  defp struct_lit(env, st, kvs) do
    check_fields(st, kvs)
    if kvs == [],
      do: "({} : #{st})",
      else: "({ " <> Enum.map_join(kvs, ", ", fn {f, v} -> "#{f} := #{expr(env, v, field_type(st, f))}" end) <> " } : #{st})"
  end

  # `v.f` where v is the whole-state variable of a struct state: the part the
  # clause's pattern bound to field f, with its Lean type (nil when v is not
  # that variable, and the caller falls back to a Lean projection)
  defp state_field(env, v, f) do
    st = env[:__struct_state__]
    parts = env["__whole__" <> Atom.to_string(v)]
    fs = st && struct_fields(st)
    cond do
      fs == nil or not is_list(parts) or length(parts) < length(fs) -> nil
      true ->
        case Enum.find_index(fs, fn {n, _, _} -> n == Atom.to_string(f) end) do
          nil -> fail("#{st} has no field #{f}")
          i -> {Enum.at(parts, i), elem(Enum.at(fs, i), 1)}
        end
    end
  end

  # A Lean value of type `t`, used only as the fallback of `hd/1` (which
  # raises on the BEAM, and an expression here cannot).
  defp default_expr(t) do
    cond do
      t in ["Nat", "Int", "Pid"] -> "0"
      t == "Bool" -> "false"
      String.starts_with?(t, "Option ") -> "none"
      String.starts_with?(t, "List ") -> "[]"
      struct_fields(t) != nil -> "({} : #{t})"
      true ->
        Map.get(Process.get(:to_lean_firsts, %{}), t) ||
          fail("hd/1 at #{t}: no default value; match on the list instead")
    end
  end

  # Enum over lists. The list's element type comes from the type of the list
  # expression (a pattern variable, a struct field, a let), or from the
  # expected type for the functions that return a list of the same type.
  defp enum_call(env, e, f, args, t) do
    l = List.first(args) || fail("unsupported #{Macro.to_string(e)}")
    lt = type_of(env, l) || if(f in [:filter, :reject, :reverse, :take, :drop], do: t, else: nil)
    et = elem_type(lt)
    ls = paren_or(expr(env, l, lt))
    p = fn g, neg -> lambda(env, g, et, "Bool", neg) end
    case {f, args} do
      {:filter, [_, g]} -> "List.filter #{p.(g, false)} #{ls}"
      {:reject, [_, g]} -> "List.filter #{p.(g, true)} #{ls}"
      {:map, [_, g]} -> "List.map #{lambda(env, g, et, elem_type(t), false)} #{ls}"
      {:any?, [_, g]} -> "List.any #{ls} #{p.(g, false)}"
      {:all?, [_, g]} -> "List.all #{ls} #{p.(g, false)}"
      {:count, [_]} -> "List.length #{ls}"
      {:count, [_, g]} -> "List.length (List.filter #{p.(g, false)} #{ls})"
      {:member?, [_, x]} -> "(#{expr(env, x, et)} ∈ #{ls})"
      {:reverse, [_]} -> "List.reverse #{ls}"
      {:take, [_, n]} -> "List.take #{paren_or(expr(env, n, "Nat"))} #{ls}"
      {:drop, [_, n]} -> "List.drop #{paren_or(expr(env, n, "Nat"))} #{ls}"
      {:at, [_, i]} -> "#{ls}[#{expr(env, i, "Nat")}]?"
      {:empty?, [_]} -> "List.isEmpty #{ls}"
      _ -> fail("unsupported Enum function Enum.#{f}/#{length(args)}")
    end
  end

  # `fn x -> e end` and the capture `&(&1.f == v)` as Lean lambdas. `neg`
  # negates the body: Enum.reject is List.filter of the negation.
  defp lambda(env, {:fn, _, [{:->, _, [[p], b]}]}, et, rt, neg) do
    n =
      case p do
        {v, _, nil} when is_atom(v) -> lean_ident(Atom.to_string(v))
        other -> fail("an anonymous function must take one variable, got #{Macro.to_string(other)}")
      end
    Map.has_key?(env, n) && fail("the anonymous function argument #{n} shadows a bound variable")
    lambda_str(Map.put(env, n, et), n, b, rt, neg)
  end
  defp lambda(env, {:&, _, [b]}, et, rt, neg) do
    Map.has_key?(env, "x1") && fail("x1 is the argument of a capture &(..) and cannot be a source variable")
    lambda_str(Map.put(env, "x1", et), "x1", capture_body(b), rt, neg)
  end
  defp lambda(_env, g, _et, _rt, _neg),
    do: fail("expected `fn x -> e end` or a capture `&(&1..)`, got #{Macro.to_string(g)}")

  defp lambda_str(env, n, b, rt, neg) do
    s = expr(env, b, rt)
    "(fun #{n} => #{if neg, do: "!(#{s})", else: s})"
  end

  # `&(&1.f == v)` -> the body with `&1` replaced by the binder `x1`
  defp capture_body({:/, _, _} = b),
    do: fail("a function capture #{Macro.to_string(b)} is not supported; use &(&1..) or fn x -> .. end")
  defp capture_body(b) do
    Macro.prewalk(b, fn
      {:&, _, [i]} when is_integer(i) and i != 1 -> fail("a capture may only use &1, got &#{i}")
      {:&, _, [1]} -> {:x1, [], nil}
      n -> n
    end)
  end

  defp lambda_body_type(env, {:fn, _, [{:->, _, [[{v, _, nil}], b]}]}, et) when is_atom(v),
    do: type_of(Map.put(env, lean_ident(Atom.to_string(v)), et), b)
  defp lambda_body_type(env, {:&, _, [b]}, et), do: type_of(Map.put(env, "x1", et), capture_body(b))
  defp lambda_body_type(_env, _, _), do: nil

  # `for x <- l, cond, .., do: e` is List.map of the body over the list
  # filtered by each condition (the conditions are applied in source order).
  defp comprehension(env, {:for, _, parts} = e, t) do
    {p, l, rest} =
      case parts do
        [{:<-, _, [p, l]} | rest] -> {p, l, rest}
        _ -> fail("a comprehension must start with `x <- list`: #{Macro.to_string(e)}")
      end
    n =
      case p do
        {v, _, nil} when is_atom(v) -> lean_ident(Atom.to_string(v))
        other -> fail("a comprehension generator must bind a variable, got #{Macro.to_string(other)}")
      end
    {filters, out} =
      case Enum.split(rest, -1) do
        {fs, [[do: b]]} -> {fs, b}
        _ -> fail("a comprehension needs a `do:` body: #{Macro.to_string(e)}")
      end
    lt = type_of(env, l) || fail("comprehension: the type of #{Macro.to_string(l)} is not known")
    Map.has_key?(env, n) && fail("the comprehension variable #{n} shadows a bound variable")
    env2 = Map.put(env, n, elem_type(lt))
    src =
      Enum.reduce(filters, paren_or(expr(env, l, lt)), fn c, acc ->
        "(List.filter (fun #{n} => #{expr(env2, c, "Bool")}) #{acc})"
      end)
    case out do
      {v, _, nil} when is_atom(v) and is_atom(v) ->
        if lean_ident(Atom.to_string(v)) == n,
          do: src,
          else: "List.map (fun #{n} => #{expr(env2, out, elem_type(t))}) #{paren_or(src)}"
      _ -> "List.map (fun #{n} => #{expr(env2, out, elem_type(t))}) #{paren_or(src)}"
    end
  end

  # The Lean type of an expression when it can be read off the environment
  # (a variable, a struct field or literal, a list or queue operation); nil
  # when it cannot, which only costs the caller an expected type.
  defp type_of(env, {v, _, nil}) when is_atom(v), do: Map.get(env, lean_ident(Atom.to_string(v)))
  defp type_of(env, {{:., _, [{v, _, nil}, f]}, _, []}) when is_atom(v) and is_atom(f) do
    case state_field(env, v, f) do
      {_, t} -> t
      nil ->
        case struct_fields(Map.get(env, lean_ident(Atom.to_string(v)))) do
          nil -> nil
          fs -> case List.keyfind(fs, Atom.to_string(f), 0) do
                  {_, t, _} -> t
                  nil -> nil
                end
        end
    end
  end
  defp type_of(_env, {:%, _, [{:__aliases__, _, [n]}, {:%{}, _, _}]}),
    do: if(struct_fields(Atom.to_string(n)) != nil, do: Atom.to_string(n), else: nil)
  defp type_of(env, {:%{}, _, [{:|, _, [b, _]}]}), do: type_of(env, b)
  defp type_of(env, {{:., _, [:queue, f]}, _, args}) when is_list(args), do: queue_type(env, f, args)
  defp type_of(env, {{:., _, [{:__aliases__, _, [:Enum]}, f]}, _, args}) when is_list(args),
    do: enum_result_type(env, f, args)
  defp type_of(_env, {:length, _, [_]}), do: "Nat"
  defp type_of(env, {:tl, _, [l]}), do: type_of(env, l)
  defp type_of(env, {:hd, _, [l]}), do: elem_type(type_of(env, l))
  defp type_of(env, {:++, _, [a, b]}), do: type_of(env, a) || type_of(env, b)
  defp type_of(_env, n) when is_integer(n) and n >= 0, do: "Nat"
  defp type_of(_env, n) when is_integer(n), do: "Int"
  defp type_of(_env, b) when is_boolean(b), do: "Bool"
  defp type_of(_env, {op, _, [_, _]}) when op in [:<=, :>=, :<, :>, :==, :!=, :and, :or], do: "Bool"
  defp type_of(env, {op, _, [a, b]}) when op in [:+, :-], do: type_of(env, a) || type_of(env, b)
  defp type_of(_env, _), do: nil

  defp queue_type(env, :in, [_, q]), do: type_of(env, q)
  defp queue_type(env, f, [q]) when f in [:to_list, :tail, :drop], do: type_of(env, q)
  defp queue_type(_env, :len, [_]), do: "Nat"
  defp queue_type(_env, :is_empty, [_]), do: "Bool"
  defp queue_type(env, :peek, [q]), do: opt_type(elem_type(type_of(env, q)))
  defp queue_type(_env, _, _), do: nil

  defp enum_result_type(env, f, [l | _]) when f in [:filter, :reject, :reverse, :take, :drop],
    do: type_of(env, l)
  defp enum_result_type(_env, f, _) when f in [:count], do: "Nat"
  defp enum_result_type(_env, f, _) when f in [:any?, :all?, :member?, :empty?], do: "Bool"
  defp enum_result_type(env, :at, [l, _]), do: opt_type(elem_type(type_of(env, l)))
  defp enum_result_type(env, :map, [l, g]) do
    case lambda_body_type(env, g, elem_type(type_of(env, l))) do
      nil -> nil
      rt -> "List " <> paren(rt)
    end
  end
  defp enum_result_type(_env, _, _), do: nil

  defp opt_type(nil), do: nil
  defp opt_type(t), do: "Option " <> paren(t)

  defp elem_type("List " <> inner), do: unparen(inner)
  defp elem_type(_), do: nil

  defp fail(msg) do
    IO.puts(:stderr, "error: " <> msg)
    System.halt(2)
  end
end

ToLean.main(System.argv())
