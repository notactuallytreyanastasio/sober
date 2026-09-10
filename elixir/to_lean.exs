# Translate typespec-annotated GenServer modules into a Lean actor model.
#
#   elixir elixir/to_lean.exs SRC.ex NAMESPACE [--pid Module=const ...] > OUT.lean
#
# Supported subset (anything else is a hard error):
#   @type msg   :: union of atoms and tagged tuples {:tag, T...}
#   @type state :: T, where T is pid(), integer(), non_neg_integer(),
#                  [T], T | nil, a union of atoms, a tuple, or a local type()
#   handle_cast/2 and handle_info/2 clauses, optional `when` guard, body =
#   zero or more send/2 or GenServer.cast/2 calls followed by {:noreply, e};
#   `if`/`case` are allowed around whole bodies.
#
# The @type declarations are the type oracle: they decide when a pattern
# variable at an `Option` position needs `some`, when `nil` is `none`, and
# what the Lean inductives look like. This is the point where Elixir's
# gradual types and Lean's dependent types meet.

defmodule ToLean do
  defmodule Ctx do
    defstruct types: %{}, msg_ctors: [], st_ctors: [], pids: %{}, enums: %{}, ns: "Gen", warnings: []
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
    IO.puts(render(ctx, clauses))
    Enum.each(ctx.warnings, &IO.puts(:stderr, "warning: " <> &1))
  end

  def main(_), do: IO.puts(:stderr, "usage: to_lean.exs SRC.ex NAMESPACE [--pid Mod=const]")

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
      st = Map.fetch!(c.types, {mod, :state})
      fields = state_fields(c, mod, st)
      %{c | st_ctors: c.st_ctors ++ [{ctor_name(mod), fields}]}
    end)
  end

  defp union({:|, _, [a, b]}), do: union(a) ++ union(b)
  defp union(t), do: [t]

  defp add_msg_ctor(ctx, mod, alt) do
    {tag, args} =
      case alt do
        a when is_atom(a) -> {a, []}
        {:{}, _, [a | rest]} when is_atom(a) -> {a, rest}
        {a, b} when is_atom(a) -> {a, [b]}
        other -> fail("unsupported message alternative: #{Macro.to_string(other)}")
      end
    ltypes = Enum.map(args, &lean_type(ctx, mod, &1))
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
  defp lean_type(_ctx, _mod, {:integer, _, []}), do: "Int"
  defp lean_type(_ctx, _mod, {:non_neg_integer, _, []}), do: "Nat"
  defp lean_type(_ctx, _mod, {:boolean, _, []}), do: "Bool"
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
  defp ctor_name(mod), do: mod |> Atom.to_string() |> String.downcase()

  # ---------- clauses ----------

  defp clauses(mod, body) do
    for {:def, _, [head, [do: b]]} <- body,
        {fname, args, guard} = head_parts(head),
        fname in [:handle_cast, :handle_info],
        [mpat, spat] = args do
      %{mod: mod, mpat: mpat, spat: spat, guard: guard, body: b}
    end
  end

  defp head_parts({:when, _, [{f, _, args}, g]}), do: {f, args, g}
  defp head_parts({f, _, args}), do: {f, args, nil}

  # ---------- rendering ----------

  defp render(ctx, clauses) do
    enums =
      for {{mod, name}, t} <- ctx.types,
          alts = union(t),
          Enum.all?(alts, &is_atom/1) and not Enum.member?(alts, nil),
          name != :msg do
        _ = mod
        ename = name |> Atom.to_string() |> String.capitalize()
        "inductive #{ename}\n" <> Enum.map_join(alts, "\n", &"  | #{&1}") <> "\n  deriving Repr, DecidableEq\n"
      end
      |> Enum.uniq()

    msg =
      "inductive Msg\n" <>
        Enum.map_join(ctx.msg_ctors, "\n", fn {tag, ts} ->
          fields = ts |> Enum.with_index() |> Enum.map_join(" ", fn {t, i} -> "(a#{i} : #{t})" end)
          "  | #{tag}" <> if(fields == "", do: "", else: " " <> fields)
        end) <> "\n  deriving Repr, DecidableEq\n"

    st =
      "inductive St\n" <>
        Enum.map_join(ctx.st_ctors, "\n", fn {name, fields} ->
          "  | #{name} " <> Enum.map_join(fields, " ", fn {f, t} -> "(#{f} : #{t})" end)
        end) <> "\n  deriving Repr, DecidableEq\n"

    pids =
      ctx.pids
      |> Enum.with_index()
      |> Enum.map_join("", fn {{mod, const}, i} -> "/-- Registered name `#{mod}`. -/\ndef #{const} : Pid := #{i}\n" end)

    {beh_clauses, ctx} = render_clauses(ctx, clauses)

    beh =
      "def beh : Behavior St Msg\n" <>
        Enum.join(beh_clauses, "\n") <>
        "\n  -- Unmatched message: GenServer would crash (cast) or ignore (info). Modelled as ignore.\n" <>
        "  | _, s, _ => (s, [])\n"

    """
    -- GENERATED by elixir/to_lean.exs. Do not edit.
    import Leanactors.Core

    namespace #{ctx.ns}

    open Leanactors

    #{Enum.join(enums, "\n")}
    #{msg}
    #{st}
    #{pids}
    #{beh}
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
      guard_str = Enum.map(guards, &guard_to_lean(env, &1)) ++ if(cl.guard, do: [guard_to_lean(env, cl.guard)], else: [])
      {body_str, c} = body(c, cl.mod, env, cl.body)
      {rhs, c} =
        case guard_str do
          [] -> {body_str, c}
          gs ->
            {fallback, c} = fallthrough(c, clauses, i, env, sp)
            {"if #{Enum.join(gs, " ∧ ")} then #{body_str} else #{fallback}", c}
        end
      {"  | #{self_name(env)}, #{sp}, #{mp} => #{rhs}", c}
    end)
  end

  defp self_name(env), do: if(Map.has_key?(env, :__self__), do: "me", else: "_")

  defp uses_self?(cl) do
    {_, found} = Macro.prewalk(cl.body, false, fn
      {:self, _, []} = n, _ -> {n, true}
      n, acc -> {n, acc}
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

  # Translate both patterns. Returns {env, msg_pat, state_pat, equality_guards}.
  defp patterns(ctx, cl) do
    {mp, env, gs} =
      case cl.mpat do
        {v, _, nil} when is_atom(v) ->
          name = Atom.to_string(v)
          if String.starts_with?(name, "_"), do: {"_", %{}, []}, else: {name, %{name => "Msg"}, []}
        _ ->
          {tag, args} = msg_shape(cl.mpat)
          {^tag, arg_types} = List.keyfind(ctx.msg_ctors, tag, 0) || fail("message tag #{inspect(tag)} not in @type msg")
          length(args) == length(arg_types) || fail("arity mismatch for #{tag}")
          {parts, env, gs} = pat_list(ctx, args, arg_types, %{}, [])
          {if(parts == [], do: ".#{tag}", else: ".#{tag} " <> Enum.join(parts, " ")), env, gs}
      end
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(cl.mod), 0)
    sub = state_subpats(cl.spat, length(fields))
    {sparts, env, gs} = pat_list(ctx, sub, Enum.map(fields, &elem(&1, 1)), env, gs)
    sp = if(sparts == [], do: ".#{ctor}", else: ".#{ctor} " <> Enum.join(sparts, " "))
    env = env |> Map.put(:__mp__, mp) |> Map.put(:__sparts__, sparts)
    {env, mp, sp, gs}
  end

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
  defp pat(_ctx, {:_, _, nil}, _t, env, gs), do: {"_", env, gs}
  defp pat(_ctx, nil, "Option " <> _, env, gs), do: {"none", env, gs}
  defp pat(_ctx, [], "List " <> _, env, gs), do: {"[]", env, gs}
  defp pat(ctx, [{:|, _, [h, t]}], "List " <> inner = lt, env, gs) do
    {hs, env, gs} = pat(ctx, h, unparen(inner), env, gs)
    {ts, env, gs} = pat(ctx, t, lt, env, gs)
    {"(#{hs} :: #{ts})", env, gs}
  end
  defp pat(_ctx, a, t, env, gs) when is_atom(a) and a not in [nil, true, false] do
    if enum_type?(t), do: {".#{a}", env, gs}, else: fail("atom #{a} at non-enum position #{t}")
  end
  defp pat(_ctx, n, t, env, gs) when is_integer(n) and t in ["Int", "Nat"], do: {"#{n}", env, gs}
  defp pat(ctx, {v, _, nil}, t, env, gs) when is_atom(v) do
    {name, whole?} =
      case Atom.to_string(v) do
        "__whole__" <> rest -> {rest, true}
        s -> {s, false}
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
      true ->
        _ = ctx
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
  defp enum_type?(t), do: t =~ ~r/^[A-Z][a-z]*$/ and t not in ["Pid", "Int", "Nat", "Bool"]

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
  defp body(ctx, mod, env, b) do
    stmts = stmts(b)
    {sends, [last]} = Enum.split(stmts, -1)
    {ctor, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    state =
      case last do
        {:noreply, e} -> state_expr(env, e, ctor, fields)
        other -> fail("last statement must be {:noreply, state}, got #{Macro.to_string(other)}")
      end
    {send_strs, ctx} =
      Enum.map_reduce(sends, ctx, fn s, c ->
        case s do
          {:send, _, [to, m]} -> {"(#{expr(env, to, "Pid")}, #{msg_expr(c, env, m)})", c}
          {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [{:__aliases__, _, [target]}, m]} ->
            const = Map.get(c.pids, Atom.to_string(target)) || fail("no --pid mapping for #{target}")
            {"(#{const}, #{msg_expr(c, env, m)})", c}
          other -> fail("unsupported statement #{Macro.to_string(other)}")
        end
      end)
    {"(#{state}, [#{Enum.join(send_strs, ", ")}])", ctx}
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
        name = Atom.to_string(v)
        case env[name] do
          "Option " <> _ -> Map.get(env, {:alias, name}, name)
          _ -> "some #{expr(env, e, unparen(inner))}"
        end
      _ -> "some " <> paren_or(expr(env, e, unparen(inner)))
    end
  end
  defp expr(_env, {:self, _, []}, _t), do: "me"
  defp expr(_env, a, _t) when is_atom(a) and a not in [nil, true, false], do: ".#{a}"
  defp expr(_env, n, _t) when is_integer(n), do: "#{n}"
  defp expr(_env, [], _t), do: "[]"
  defp expr(env, xs, t) when is_list(xs), do: "[" <> Enum.map_join(xs, ", ", &expr(env, &1, elem_type(t))) <> "]"
  defp expr(env, {v, _, nil}, _t) when is_atom(v), do: Map.get(env, {:alias, Atom.to_string(v)}, Atom.to_string(v))
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
