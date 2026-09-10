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
#
# The @type declarations are the type oracle: they decide when a pattern
# variable at an `Option` position needs `some`, when `nil` is `none`, and
# what the Lean inductives look like. This is the point where Elixir's
# gradual types and Lean's dependent types meet.

defmodule ToLean do
  defmodule Ctx do
    defstruct types: %{}, msg_ctors: [], st_ctors: [], pids: %{}, enums: %{}, ns: "Gen", warnings: [],
              extra: [], awaits: %{}, reply_type: nil, effects: false, traps: %{}, pid_vars: [],
              covered: [], inits: %{}
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
    ctx = %Ctx{ns: ns, pids: pids}
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_types(c, name, body) end)
    clauses = for {name, body} <- mods, cl <- clauses(name, body), do: cl
    traps = for {name, body} <- mods, traps?(body), into: %{}, do: {name, true}
    inits = for {name, body} <- mods, init = init_of(name, body), init != nil, into: %{}, do: {name, init}
    effects = map_size(traps) > 0 or Enum.any?(clauses, &effects_in?(&1.body))
    ctx = %{ctx | traps: traps, effects: effects, inits: inits}
    if effects and not List.keymember?(ctx.msg_ctors, :EXIT, 0) and map_size(traps) > 0,
      do: fail("a trapping module must declare {:EXIT, pid(), term()} in @type msg")
    IO.puts(render(ctx, clauses))
    Enum.each(ctx.warnings, &IO.puts(:stderr, "warning: " <> &1))
  end

  def main(_), do: IO.puts(:stderr, "usage: to_lean.exs SRC.ex NAMESPACE [--pid Mod=const]")

  defp traps?(body) do
    {_, found} = Macro.prewalk({:__block__, [], body}, false, fn
      {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

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

  defp effects_in?(body) do
    {_, found} = Macro.prewalk(body, false, fn
      {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, _} = n, _ when f in [:start_link, :start] -> {n, true}
      {{:., _, [{:__aliases__, _, [:Process]}, f]}, _, _} = n, _ when f in [:monitor, :send_after, :exit] -> {n, true}
      {:{}, _, [:noreply, _, _]} = n, _ -> {n, true}
      {:exit, _, [_]} = n, _ -> {n, true}
      {:{}, _, [:stop, _, _]} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
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
      # msg union contributes constructors; state contributes one St constructor
      msg = Map.fetch!(c.types, {mod, :msg})
      c = Enum.reduce(union(msg), c, fn alt, cc -> add_msg_ctor(cc, mod, alt) end)
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
      fields = state_fields(c, mod, st)
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
    # find the @type whose union is exactly these atoms
    case Enum.find(ctx.types, fn {{m, _}, t} -> m == mod and union(t) == alts end) do
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

  defp clauses(mod, body) do
    for {:def, _, [head, [do: b]]} <- body,
        {fname, args, guard} = head_parts(head),
        fname in [:handle_cast, :handle_info, :handle_call],
        cl = clause_of(mod, fname, args, guard, b),
        cl != nil do
      cl
    end
  end

  defp clause_of(mod, :handle_call, [mpat, fpat, spat], guard, b),
    do: %{mod: mod, mpat: mpat, spat: spat, guard: guard, body: b, from: fpat}
  defp clause_of(mod, _, [mpat, spat], guard, b),
    do: %{mod: mod, mpat: mpat, spat: spat, guard: guard, body: b, from: nil}
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
          name not in [:msg, :call] do
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

    sig =
      if ctx.effects do
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
            else: "  -- no module declares {:EXIT, ...}; nobody traps, so this codec is never used\n  exitMsg := fun _ _ => .go\n"
        "/-- Who traps exits (from `Process.flag(:trap_exit, true)`), the EXIT message, the DOWN message. -/\n" <>
          "def sig : Signals St Msg where\n  traps := fun\n#{trap_arms}\n" <> exit_line <> down <> "\n"
      else
        ""
      end

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
          if(ctx.effects, do: "  | _, _, s, _ => (s, [])\n", else: "  | _, s, _ => (s, [])\n")
      end
    beh =
      "def beh : #{if ctx.effects, do: "EBehavior", else: "Behavior"} St Msg\n" <>
        Enum.join(beh_clauses ++ ctx.extra, "\n") <> catch_all


    """
    -- GENERATED by elixir/to_lean.exs. Do not edit.
    import Leanactors.#{if ctx.effects, do: "Sys", else: "Core"}

    namespace #{ctx.ns}

    open Leanactors

    #{Enum.join(enums, "\n")}
    #{msg}
    #{st}
    #{pids}
    #{sig}#{beh}
    end #{ctx.ns}
    """
  end

  defp render_clauses(ctx, clauses) do
    indexed = Enum.with_index(clauses)
    # A clause subsumed by an earlier clause of the same module is unreachable
    # (Elixir warns "this clause cannot match"; with a guard we already inlined it).
    indexed = Enum.reject(indexed, fn {cl, j} ->
      Enum.any?(indexed, fn {e, i} -> i < j and e.mod == cl.mod and general?(e.mpat, cl.mpat) and general?(e.spat, cl.spat) end)
    end)
    Enum.map_reduce(indexed, ctx, fn {cl, i}, c ->
      {env, mp, sp, guards} = patterns(c, cl)
      env = if uses_self?(cl), do: Map.put(env, :__self__, true), else: env
      env = if spawns?(cl), do: Map.put(env, :__fresh__, 0), else: env
      env = if cl.from, do: Map.put(env, :__from__, from_name(cl.from)), else: env
      guard_str = Enum.map(guards, &guard_to_lean(env, &1)) ++ if(cl.guard, do: [guard_to_lean(env, cl.guard)], else: [])
      {body_str, c} = body(c, cl.mod, env, cl.body)
      {rhs, c} =
        case guard_str do
          [] -> {body_str, c}
          gs ->
            {fallback, c} = fallthrough(c, clauses, i, env, sp)
            {"if #{Enum.join(gs, " ∧ ")} then #{body_str} else #{fallback}", c}
        end
      c =
        if cl.guard == nil and bare?(cl.mpat) and bare?(cl.spat),
          do: %{c | covered: [ctor_name(cl.mod) | c.covered]},
          else: c
      header =
        if c.effects,
          do: "  | #{self_name(env)}, #{fresh_name(env)}, #{sp}, #{mp}",
          else: "  | #{self_name(env)}, #{sp}, #{mp}"
      {"#{header} => #{rhs}", c}
    end)
  end

  defp bare?({v, _, nil}) when is_atom(v), do: true
  defp bare?(_), do: false

  defp self_name(env), do: if(Map.has_key?(env, :__self__), do: "me", else: "_")
  defp fresh_name(env), do: if(Map.has_key?(env, :__fresh__), do: "fresh", else: "_")

  # a clause needs `fresh` if it spawns
  defp spawns?(cl) do
    {_, found} = Macro.prewalk(cl.body, false, fn
      {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, _} = n, _ when f in [:start_link, :start] -> {n, true}
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
  # the same module whose patterns are at least as general. That clause's
  # variables are aliased to the current clause's Lean pattern parts.
  defp fallthrough(ctx, clauses, i, env, sp) do
    cl = Enum.at(clauses, i)
    later = clauses |> Enum.with_index() |> Enum.filter(fn {c, j} -> j > i and c.mod == cl.mod end)
    case Enum.find(later, fn {c, _} -> general?(c.mpat, cl.mpat) and general?(c.spat, cl.spat) end) do
      nil ->
        ctx = %{ctx | warnings: ctx.warnings ++ ["clause #{i} guard has no fallthrough; Elixir would crash, modelled as no-op"]}
        {"(#{sp}, [])", ctx}
      {c, _} ->
        env2 = aliases(c.mpat, cl.mpat, env, %{__msg_parts__: env[:__mparts__]})
        env2 = whole_alias(c.spat, sp, env2)
        env2 = if uses_self?(c), do: Map.put(env2, :__self__, true), else: env2
        {b, ctx} = body(ctx, c.mod, env2, c.body)
        if c.guard, do: fail("chained guards are not supported (clause #{i})")
        {b, ctx}
    end
  end

  # is `general` at least as general as `specific`? (var/_ or identical)
  defp general?({v, _, nil}, _) when is_atom(v), do: true
  defp general?(a, a), do: true
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

  defp whole_alias({v, _, nil}, sp, env) when is_atom(v) do
    target = case env[:__sparts__] do
      [single] -> single
      _ -> sp
    end
    Map.put(env, {:alias, Atom.to_string(v)}, target)
  end
  defp whole_alias(_, _, env), do: env

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
          {^tag, arg_types} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("message tag #{inspect(tag)} not in @type msg")
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
          {if(parts == [], do: ".#{tag}", else: ".#{tag} " <> Enum.join(parts, " ")), env, gs}
      end
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(cl.mod), 0)
    sub = state_subpats(cl.spat, length(fields))
    {sparts, env, gs} = pat_list(ctx, sub, Enum.map(fields, &elem(&1, 1)), env, gs)
    sp = if(sparts == [], do: ".#{ctor}", else: ".#{ctor} " <> Enum.join(sparts, " "))
    env = env |> Map.put(:__mp__, mp) |> Map.put(:__sparts__, sparts)
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
  #   this clause: sends-so-far ++ [(target, m me)], state := <mod>_await<i> captured
  #   extra:       | _, .<mod>_await<i> captured, .reply v => rest
  #                | me, .<mod>_await<i> captured, m => (.<mod>_await<i> captured, [(me, m)])
  defp cps_split(ctx, mod, env, before, {:=, _, [lhs, {_, _, [{:__aliases__, _, [target]}, m | _timeout]}]}, rest) do
    ctx.reply_type || fail("GenServer.call used but no module declares @type reply")
    const = Map.get(ctx.pids, Atom.to_string(target)) || fail("no --pid mapping for #{target}")
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
      "  | #{cont_self}, #{if ctx.effects, do: "_, ", else: ""}.#{await}#{cap_str}, .reply #{lhs_pat} => #{cont}",
      "  | me, #{if ctx.effects, do: "_, ", else: ""}.#{await}#{cap_str}, m => (.#{await}#{cap_str}, [#{send_str(ctx, "me", "m")}])"
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

  # a send, rendered as a pair (message mode) or an effect (effects mode)
  defp send_str(ctx, to, m), do: if(ctx.effects, do: ".send #{paren_or(to)} #{paren_or(m)}", else: "(#{to}, #{m})")

  # Statements before the final tuple. Returns {strings, ctx, env}: spawns
  # bind their pid variable to `fresh`, `fresh + 1`, ...
  defp sends(ctx, env, stmts) do
    {strs, {c, e}} =
      Enum.map_reduce(stmts, {ctx, env}, fn s, {c, e} ->
        case s do
          {:send, _, [{:__aliases__, _, [target]}, m]} ->
            const = Map.get(c.pids, Atom.to_string(target)) || fail("no --pid mapping for #{target}")
            {send_str(c, const, msg_expr(c, e, m)), {c, e}}
          {:send, _, [to, m]} -> {send_str(c, expr(e, to, "Pid"), msg_expr(c, e, m)), {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :send_after]}, _, [to, m, _t]} ->
            c.effects || fail("send_after outside effects mode")
            {".sendAfter #{paren_or(expr(e, to, "Pid"))} #{paren_or(msg_expr(c, e, m))}", {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :exit]}, _, [to, r]} ->
            c.effects || fail("Process.exit outside effects mode")
            {".signal #{paren_or(expr(e, to, "Pid"))} #{reason_str(r)}", {c, e}}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [{:__aliases__, _, [target]}, m]} ->
            const = Map.get(c.pids, Atom.to_string(target)) || fail("no --pid mapping for #{target}")
            {send_str(c, const, msg_expr(c, e, m)), {c, e}}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :reply]}, _, [to, r]} ->
            c.reply_type || fail("GenServer.reply used but no @type reply")
            {send_str(c, expr(e, to, "Pid"), ".reply #{paren_or(expr(e, r, c.reply_type))}"), {c, e}}
          {:=, _, [{:ok, {v, _, nil}}, {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [{:__aliases__, _, [child]}, arg]}]} when is_atom(v) and f in [:start_link, :start] ->
            c.effects || fail("spawn outside effects mode")
            {cctor, cfields} = List.keyfind(c.st_ctors, ctor_name(child), 0) || fail("unknown child module #{child}")
            init = child_state(c, e, child, arg, cctor, cfields)
            k = Map.get(e, :__fresh__, 0)
            pid = if k == 0, do: "fresh", else: "(fresh + #{k})"
            e = e |> Map.put(:__fresh__, k + 1) |> Map.put({:alias, Atom.to_string(v)}, pid) |> Map.put(lean_ident(Atom.to_string(v)), "Pid")
            {if(f == :start_link, do: ".spawnLink (#{init})", else: ".spawn (#{init})"), {c, e}}
          {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [target]} ->
            c.effects || fail("monitor outside effects mode")
            {".monitor #{paren_or(expr(e, target, "Pid"))}", {c, e}}
          {:=, _, [{_ref, _, nil}, {{:., _, [{:__aliases__, _, [:Process]}, :monitor]}, _, [target]}]} ->
            c.effects || fail("monitor outside effects mode")
            {".monitor #{paren_or(expr(e, target, "Pid"))}", {c, e}}
          other -> fail("unsupported statement #{Macro.to_string(other)}")
        end
      end)
    {strs, c, e}
  end

  defp reason_str(:normal), do: ".normal"
  defp reason_str(_), do: ".error"

  defp plain_body(ctx, mod, env, stmts) do
    {sends, [last]} = Enum.split(stmts, -1)
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    {send_strs, ctx, env} = sends(ctx, env, sends)
    {state, tail} =
      case last do
        {:noreply, e} -> {state_expr(env, e, ctor, fields), []}
        {:{}, _, [:reply, r, e]} ->
          from = env[:__from__] || fail("{:reply, ...} outside handle_call")
          {state_expr(env, e, ctor, fields), [send_str(ctx, from, ".reply #{paren_or(expr(env, r, ctx.reply_type))}")]}
        {:{}, _, [:noreply, e, _t]} ->
          ctx.effects || fail("{:noreply, s, timeout} outside effects mode")
          List.keymember?(ctx.msg_ctors, :timeout, 0) || fail("GenServer timeout used but :timeout not in @type msg")
          {state_expr(env, e, ctor, fields), [".sendAfter me .timeout"]}
        {:{}, _, [:stop, r, e]} ->
          ctx.effects || fail("{:stop, ...} outside effects mode")
          {state_expr(env, e, ctor, fields), [".exit #{reason_str(r)}"]}
        {:exit, _, [r]} ->
          ctx.effects || fail("exit/1 outside effects mode")
          st = env[{:alias, "__state__"}] || whole_state(env, ctor, fields)
          {st, [".exit #{reason_str(r)}"]}
        other -> fail("last statement must be {:noreply, state}, {:reply, r, state} or {:stop, r, state}, got #{Macro.to_string(other)}")
      end
    {"(#{state}, [#{Enum.join(send_strs ++ tail, ", ")}])", ctx}
  end

  # the current state rebuilt from the clause's state pattern (for exit/1)
  defp whole_state(env, ctor, _fields) do
    case env[:__sparts__] do
      nil -> fail("exit/1 needs the state bound by the pattern")
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
