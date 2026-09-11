# Translate typespec-annotated GenServer modules into a Lean actor model.
#
#   elixir elixir/to_lean.exs SRC.ex NAMESPACE [--pid Module=const ...] [--pubsub Module ...] > OUT.lean
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
#   {:noreply, e} or (handle_call only) {:reply, r, e}; `if`/`case`/`cond`
#   are allowed around whole bodies, and are expressions everywhere else
#   (see Control flow and expressions). The other GenServer return forms:
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
#   init/1: `def init(p), do: {:ok, e}` or a block ending in `{:ok, e}`,
#   where p is a variable or a tuple of variables and e is a pure expression
#   of p. The statements before the return may be
#   `Process.flag(:trap_exit, true)`, a PubSub subscribe/unsubscribe, a
#   `Logger` call (dropped: logging is not modelled), a call to a local
#   helper, or a binding `v = e` of a pure expression, which is substituted
#   into the later statements and into the state expression -- init/1 has no
#   Lean binder of its own, because the state is built at the spawn site. The
#   option list a real init/1 is handed is not modelled: a parameter used as
#   one is the empty keyword list, so `Keyword.get(opts, :k, d)` is its
#   literal default `d` and `Keyword.get(opts, :k)` is nil. That is an
#   approximation of the running system and the translator warns about it. At
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
#   Structs: `defstruct f: d, ..` with `@type t :: %__MODULE__{f: T, ..}`
#   is a Lean `structure` with the same fields, each defaulting to `d`
#   (a field with no declared type takes Nat/Int/Bool from a numeric or
#   boolean default, `String` from a binary one and `List Term` from
#   `:queue.new()`; anything else must be declared). `%Mod{f: e}` is
#   `({ f := e } : Mod)` with the other fields at their defaults, `%{s | f:
#   e}` is `{ s with f := e }`, `x.f` is the projection, and a pattern
#   `%Mod{f: p}` is the anonymous constructor `⟨.., p, ..⟩` with a wildcard
#   for every field not named (`%Mod{..} = v` binds the whole value as
#   `v@⟨..⟩`). A GenServer whose `@type state` is its own struct (`t()` or
#   `%__MODULE__{}`) has it flattened into the state constructor, one field
#   per defstruct field in order and under the struct's own names: `state.f`
#   is then the part the clause's pattern bound to f, `%{state | f: e}`
#   rebuilds the constructor with the named parts replaced, and a whole-state
#   value cannot be bound to a variable (it does not exist in the model).
#   Such a module's own struct is not emitted as a Lean `structure` unless
#   some other type mentions it. Declarations are emitted in dependency
#   order; a cycle would need a `mutual` block and is an error.
#   Enum over lists: Enum.filter/reject are `List.filter` (reject of the
#   negated predicate), map `List.map`, count `List.length` (of the filtered
#   list when a predicate is given), any?/all? `List.any`/`List.all`,
#   member? `∈`, reverse/take/drop the same names, at `l[i]?` (an Option),
#   empty? `List.isEmpty`; `length` is `List.length`, `tl` `List.tail`,
#   `++` `++`, and `hd` is `List.headD` at the element type's default (it
#   raises on the BEAM, which an expression here cannot; an element type
#   with no default value is an error). The predicate is a literal
#   `fn x -> e end` or a capture `&(&1..)`, whose argument is the Lean
#   binder `x1` (so `x1` is reserved, and only `&1` may appear). A
#   comprehension `for x <- l, c, .., do: e` is `List.map` of the body over
#   the list filtered by each condition in source order.
#   :queue is the list, oldest first: `:queue.queue(T)` is `List T`,
#   `:queue.new()` is `[]`, `:queue.in(x, q)` is `q ++ [x]`,
#   `:queue.to_list(q)` is `q`, `:queue.len`/`:queue.is_empty` are the List
#   functions, `:queue.peek(q)` is `List.head?` (matched with `{:value, x}`
#   and `:empty`), `{_, q} = :queue.out(q0)` is `let q := List.tail q0` (out
#   of an empty queue gives it back, as `tail` does), and
#   `case :queue.out(q)` matches the list: `{{:value, x}, rest}` is
#   `x :: rest` and `{:empty, q}` is `[]` with q aliased to it.
#   A local binding `v = e` is a Lean `let` wrapped around the clause's
#   result. Statements may be followed by an if/case body, in which case the
#   bindings wrap the whole branch (so the condition sees them) and a
#   statement with an effect of its own (a send, a spawn) is pushed into
#   every branch: its effect is prepended to the effects of whichever leaf
#   runs, which is once in the text per leaf and exactly once in any run.
#   A module attribute holding a literal (`@max 3`) is substituted into
#   every later read of it in the module body, so a defstruct default, a
#   guard or a state expression may name one.
#   After a blocking call the rest of the body may be a single if/case.
#   PubSub: `Phoenix.PubSub.subscribe(server, topic)` is the effect
#   `.subscribe me topic`, `Phoenix.PubSub.unsubscribe(server, topic)` is
#   `.unsubscribe me topic` and `Phoenix.PubSub.broadcast(server, topic, m)`
#   (or `broadcast!`) is `.broadcast topic m`, where m is a message
#   expression (an alternative of the file's message unions) and the server
#   argument is ignored (one PubSub per model). The topic must be a string
#   literal or a module attribute (`@topic "feed"`, referenced as `@topic`)
#   bound to one; anything else is an error. Which module is PubSub is by
#   name: `Phoenix.PubSub` always, `PubSub` by default (the local
#   elixir/src/pubsub.ex twin, so a driver runs without the phoenix_pubsub
#   dependency), and any module named with `--pubsub Mod`. A subscribe or
#   unsubscribe may also appear in init/1 (before its `{:ok, state}`): the
#   spawn site `{:ok, pid} = GenServer.start[_link](Mod, arg)` then emits
#   `.subscribe fresh topic` after the spawn, attributing the subscription
#   to the child, and `:ok = Phoenix.PubSub.subscribe(...)` is accepted
#   wherever the bare call is. A module whose init/1 subscribes but that no
#   module in the file spawns has no spawn site to hang the effect on, so
#   the model would show no subscription: that is a warning, and the
#   hand-written example placing such an actor adds the effect itself.
#   The effects live on `Sys.subs` (Leanactors/Sys.lean): a broadcast is one
#   delivery to every subscriber in subscription order and a death drops its
#   subscriptions.
#
#   Local bindings: a statement `v = e` inside a callback body binds `v`
#   to the rendered expression (nothing is emitted); the rest of the body
#   uses it. `Map.pop(m, k)` is only supported as a `case` scrutinee:
#   `case Map.pop(m, k) do {nil, rest} -> ..; {v, rest} -> .. end` becomes
#   `match AssocList.get? m k with | none => .. | some v => ..` with `rest`
#   bound to `m` in the first arm and to `AssocList.erase m k` in the
#   second. (On the BEAM a stored `nil` would take the first arm too; the
#   model's values are never nil.)
#
# Control flow and expressions. The pure fragment is compiled as a language,
#   not as a body shape: any sub-expression may itself be a control form.
#     * `a |> f(b)` is `f(a, b)`. Pipes, `cond` and `unless` are rewritten
#       over the whole module body before anything else looks at it
#       (`desugar/1`), so nothing downstream ever sees one.
#     * `if c, do: a, else: b` is `(if c then a else b)`, each branch
#       compiled at the expected type (so `some`/`none` is inserted per
#       branch, not around the whole `if`). An `if` with no `else` is nil on
#       the BEAM, which the model has only at an Option type: anywhere else
#       it is an error.
#     * `cond` is nested `if`s. Its last clause must be `true ->`: falling
#       off the end raises CondClauseError, and an expression cannot raise.
#     * `case e do p -> b; .. end` is `(match e with | p => b | ..)`, the
#       arms using the same type-directed pattern machinery as a clause head
#       (`case_arm_pat`, shared with the body compiler). Inside an expression
#       there is nothing to fall through to, so an arm pattern that would
#       need a guard, and a map pattern, are errors; `case Map.pop(m, k)`
#       and `case :queue.out(q)` stay whole-body forms.
#     * A block `(a; b; c)` is nested `let`s with the last statement as the
#       value. Its other statements must be bindings: an effect belongs to
#       the clause body, where the model can order it. The one non-binding
#       statement allowed is `{_, q} = :queue.out(q0)`, which is the same
#       `let q := List.tail q0` the statement form gives it.
#     * A binding `x = e` is `let x := e` (a variable simply shadows; Lean's
#       `let` is not recursive, so the right-hand side still reads the old
#       one). A pattern binding `{a, b} = e` is `let (a, b) := e`, and a
#       struct pattern `%Mod{f: p} = e` the anonymous constructor (a pair of
#       two typed expressions has the product type `A × B`, so
#       `{a, b} = if .. do {x, y} else {u, v} end` binds). Only a
#       pattern that is total at its type may be bound (`irrefutable?`):
#       a variable, `_`, a pair at a product type, a struct pattern,
#       `%{}`. `{:ok, v} = Map.fetch(m, k)` and `%{k => v} = m` can fail and
#       have nothing to fall through to, so they are errors -- match on them.
#   Kernel guards and functions. A type test is decided statically, because
#   a value of the model has exactly one type: `is_pid` on a `pid()` is
#   `true`, `is_list` on a `[T]` is `true` and `is_map` on it is `false`; at
#   a `T | nil`, `is_nil` is `isNone` and the others are `isSome` or `false`.
#   `is_nil`, `is_pid`, `is_list`, `is_map`, `is_integer`, `is_atom`,
#   `is_boolean`, `is_number`, `is_float`, `is_tuple` and `is_binary` (a
#   binary is a Lean `String`) are supported this way; a test at an opaque
#   `Term`, or at a tagged union (whose alternatives are both atoms and
#   tuples), is not decidable and is an error.
#   `elem/2` and `tuple_size/1` read the pair of a map entry, the one tuple
#   the model has as a value (the fields of a tagged tuple are reached by
#   matching). `abs/1` is `Int.natAbs`, `min`/`max` are Lean's, and
#   `div`/`rem` are `/` and `%` on non_neg_integer() only: Elixir's `div`
#   truncates toward zero and Lean's integer division does not, so an Int
#   operand is an error rather than a silent difference. `x in l` is list
#   membership. `&&`, `||` and `!` are `and`, `or` and `not` (a non-boolean
#   operand is Elixir truthiness, which no value of the model has), `===`
#   and `!==` are `==` and `!=`, and `*` is multiplication.
# Untyped mode. A module that declares none of @type msg/cast/info/call
#   has its message unions inferred from its own source, and a file with no
#   @type reply and a module with no @type state likewise (`infer_types/1`
#   builds exactly the declarations the typed path above consumes, so every
#   decision downstream is still type-directed):
#     * messages: each handle_cast/handle_info/handle_call clause pattern
#       contributes its tag at the arity it is matched with, and the
#       callback fixes the kind (cast/info/call); messages the module sends
#       with a literal tag (`send/2`, `GenServer.cast/2`,
#       `Process.send_after/3`, `Phoenix.PubSub.broadcast/3`) that nobody
#       handles or declares join its @type msg. A tag matched at two
#       arities is an error: declare it.
#     * reply: when every `{:reply, r, _}`, `{:reply, r, _, _}`,
#       `{:stop, _, r, _}` and `GenServer.reply(_, r)` in the file is a
#       literal atom or tagged tuple, the alternatives become the tagged
#       union `Reply` as a declared @type reply would. A tag that appears at
#       two arities (`:ok` and `{:ok, ref}`) names its tuple form with the
#       arity appended (`ok` and `ok1`). When NO reply is a literal there is
#       no union to infer, but the expressions may still have one type
#       between them: the file is rendered once with the replies left out,
#       the type each reply expression has in its own clause is collected,
#       and if there is exactly one the whole file is compiled again with it
#       as `@type reply` -- so a list-valued or struct-valued reply carries
#       its real type (`Msg.reply (a0 : List Term)`), and every decision
#       downstream is still made from a declared type. A mixed file (a
#       literal atom beside a typed expression, or two reply expressions of
#       different types) keeps `term()`, and a reply expression that does
#       have a type in the model is then an error naming `@type reply`: the
#       opaque constructor cannot carry it, and there is no one type to
#       promote. (Unifying the mixed case would need a `Reply` inductive
#       with a constructor per shape, wrapped at every reply site and
#       unwrapped at every `reply v` await-resume pattern; nothing in the
#       measured projects needs it yet.)
#     * state: the literal of `init/1`. `%{k: e, ..}` (atom keys) is a
#       record type (see below), `%{}` a map, an integer `integer()`, a
#       boolean `boolean()`, a binary `binary()`, `nil` `term() | nil`, a
#       list `[term()]`, a tuple positional, `%Mod{..}` that struct;
#       anything else `term()`. With no init/1 either, the
#       shape comes from the state patterns of the callbacks, which must
#       agree: a map pattern anywhere -- or a body that updates or returns
#       named keys, as a LiveView's `assign` does -- makes it a record whose
#       fields are the keys the patterns match and the keys the bodies write,
#       tuple patterns of one size make it positional, and patterns that only
#       bind the state whole with nothing written by name leave it `term()`.
#       Such a field's type is the shape of the values the bodies write to
#       it, read by the same rules as an init/1 literal (a list append or a
#       list literal is `[term()]`, an integer `integer()`, and so on); a
#       field nothing pins, or one written at two different shapes, stays
#       `term()`.
#   Every inferred field type is `term()`, which renders as the opaque
#   `Term` of Leanactors/Term.lean (a structure over Nat with DecidableEq
#   and Repr, imported when it occurs); `any()` and `reference()` render
#   the same way. A @type declaration, where one is present, refines those
#   fields exactly as before, so the annotated sources translate byte for
#   byte. An atom literal at a `Term` position is an error: give the field
#   a @type so it becomes an enum.
#
# LiveView assigns. A socket is a struct with an `assigns` map and Phoenix
#   imports `assign/2,3`, which updates it functionally, so a socket is
#   modelled as exactly the record the state machinery already has:
#   `assign(s, :k, e)` is the map update `%{s | k: e}`, `assign(s, k: e, ..)`
#   and `assign(s, %{k: e, ..})` the multi-field one, and `s.assigns.k` the
#   field read `s.k`. The rewrite happens before anything else looks at the
#   body, needs a variable socket and literal atom keys (a computed key is
#   left alone and reported as the unsupported call it is), and is skipped
#   entirely for a module that defines `assign` itself. Nothing else about
#   LiveView is modelled: `mount/3` and `render/1` are not callbacks, so the
#   initial state comes from the spawn site as it does for a GenServer with
#   no init/1, and `handle_event/3` is a browser event rather than a message,
#   so it is not a clause of `beh` -- but because that IS a transition the
#   real process makes, the generated file names it in its own header
#   comment. The assigns no callback reads or writes are not in the model,
#   which is the abstraction a record state makes of any map.
#
# Record-shaped state. A state type `%{k: T, ..}` with atom keys becomes
#   one St constructor with NAMED fields, one per key, in declaration
#   order. In a clause, a whole-state variable `s` binds every field the
#   body reads (`s.f` is the field, `%{s | f: e}` rebuilds the constructor
#   with that field replaced, a bare `s` is the whole constructor); a field
#   the body never reads is `_`. A map pattern `%{f: p, ..}`, optionally
#   `= s`, binds the named fields to their sub-patterns and the rest as the
#   whole variable would. A record state literal must give every field.
#
# External resources. `:ets.new(..)` on the right of a binding is a fresh
#   opaque reference: the module's state gets a hidden trailing counter
#   field `(ets : Nat)` (like the after-timer generation), the k-th table a
#   body creates is `Term.mk (ets + k)`, and the continuing state advances
#   the counter. `:ets.f(..)` as a statement, and a `try .. rescue .. end`
#   whose body is only such calls, are dropped before translation: what
#   happens inside ETS is not modelled, so properties proved about such a
#   module are properties of the map of references it keeps, not of ETS. A
#   `try` with any other body, or with an `after`/`else`/`catch` block, is
#   an error. A blocking call in a module that creates tables is not
#   supported.
#
# Module-local functions. A `def`/`defp` that is not a callback and that a
#   callback reaches, directly or through another helper, becomes a Lean
#   definition emitted before `beh`, named `<module>_<function>`; a call to
#   it renders as a call. Its body must be in the pure fragment: `if`, `cond`
#   (with a final `true ->`) and `case` as expressions, a block of bindings
#   `v = e` ending in a value (a Lean `let`), and everything `expr` renders.
#   A helper that sends, spawns or logs has no effect the model could carry,
#   so it is an error naming the helper -- once, not once per call site.
#   Multiple clauses become a `match` over the arguments, or -- when every
#   clause matches its arguments with variables and some has a `when` guard
#   -- an `if` chain in source order, whose last clause must be unguarded
#   because a Lean definition is total. Default arguments are filled in at
#   the call site.
#   Types come from the helper's `@spec f(T..) :: R` when it has one, and
#   otherwise from the types it is called at: the arguments and the expected
#   result at its call sites, which must agree, and `Term` for what use does
#   not fix. Two different types in one position is an error asking for a
#   @spec.
#   Recursion: a helper that recurses on the tail of a list argument is
#   emitted as an ordinary `def` (Lean sees the structural recursion);
#   anything else self-recursive takes a leading `fuel : Nat`, returns the
#   default value of its result type when the fuel runs out, and is called
#   with the constant `localFuel` (64), which the generated file documents as
#   an approximation. Two helpers that call each other would need a Lean
#   `mutual` block and are an error naming both.
#
# Public API. `def`s that are not callbacks and that no callback reaches
#   (init, handle_*, start, start_link, terminate, child_spec, the receive
#   loop) are not translated: they are the module's own API wrappers around
#   GenServer.call/cast, and `raise` inside one is not a callback body. The
#   generated file names them in a comment under its header.
#
# Registered names: `send(Mod, m)`, `GenServer.cast(Mod, m)` and
#   `GenServer.call(Mod, m)` need a constant pid for Mod. With `--pid`
#   flags the map is exactly those flags. Without any, it is derived from
#   the source: `GenServer.start_link/start(_, _, name: N)` and
#   `Process.register(_, N)` anywhere in a module register N (__MODULE__,
#   an alias or an atom) as the constant N lowercased (Cache -> cache).
#   `name: Keyword.get(opts, :name, N)` is N with a warning: the option
#   list a real `start_link` is handed is not modelled, the same rule
#   `init/1` follows. Atom names may be used as send/cast targets
#   (`send(:cache, m)`).
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
# Standard-library calls: ONE table. `@remote` at the top of this file maps
#   {module segments, function, arity} to what the call becomes -- a
#   rendering, `:noop` (a statement with no effect in the model, dropped
#   before anything is translated, arguments included) or `{:error, why}` (a
#   clear refusal naming what the model lacks). Extending the translator to
#   another standard-library function is adding a row, not a clause. The
#   rendering kinds are `{:assoc, op}` (an association-list operation, the
#   same `map_call/4` a `Map` call uses), `{:set, f}` (Leanactors/SetList),
#   `{:const, e, t}` (a constant, its arguments ignored) and
#   `{:fun, f, ats, t}` (a Lean function applied to the arguments at the
#   given types).
#
# Binaries are Lean `String`s (Leanactors/Str.lean). `String.t()`,
#   `binary()`, `bitstring()`, `iodata()` in a @type are `String`; a string
#   literal is the Lean literal; `a <> b` is `a ++ b`; a string literal in a
#   pattern is a Lean literal pattern (which never *covers* a clause, so a
#   module that matches one still needs a catch-all or a crash clause).
#   Interpolation `"a#{e}b"` is `"a" ++ Str.toStr e ++ "b"`, where `Str.toStr`
#   is the `ToStr` class of Leanactors/Str.lean: the instances for String,
#   Nat, Int and Bool are the BEAM's own rendering, and everything else --
#   an enum, a tagged union, a `Term`, an `Instant` -- goes through its
#   derived `Repr`, an opaque but deterministic rendering that no property
#   should depend on the bytes of. `#{e}` where e is already a binary emits
#   e itself; `inspect(e)` and `to_string(e)`, inside an interpolation or
#   out of it, are `Str.toStr e`.
#
# Keyword lists are association lists. `[k: v, ..]` is `List (Atom × V)`
#   over an `Atom` inductive the file generates from the keys the rendering
#   actually used, so `keyword()`, `keyword(T)`, `Keyword.t()` and
#   `Keyword.t(T)` are map types and `Keyword.get/2,3`, `fetch/2`, `put/3`,
#   `delete/2`, `has_key?/2`, `keys/1`, `values/1`, `Access.get/2,3` and the
#   `opts[:k]` that parses to it are the AssocList functions a `Map` call
#   already uses. `Keyword.fetch!/2` raises on the BEAM, which an expression
#   here cannot, so it is the lookup at the value type's default, like
#   `hd/1`. `[ok: 1]` and `[{:ok, 1}]` are the same AST: at a known type the
#   type decides, and at an unknown one a key that is an alternative of one
#   of the file's tagged unions keeps the tagged-tuple reading.
#
# MapSet is a duplicate-free list in insertion order
#   (Leanactors/SetList.lean): `MapSet.t(T)` is `List T`, `MapSet.new()` is
#   `[]`, and new/1, put, delete, member?, size, to_list, union, difference
#   and intersection are the SetList functions. `to_list` is the identity on
#   that list, so it is in insertion order and not the BEAM's term order: a
#   property may count a set and test membership, but not depend on the
#   order `to_list` gives.
#
# Time is not modelled. `DateTime.utc_now/0,1`, `NaiveDateTime.utc_now`,
#   `Date.utc_today`, `System.monotonic_time`, `System.system_time` and
#   `System.os_time` are all the single opaque `Instant.now` of
#   Leanactors/Time.lean, which has `DecidableEq` and `Repr` and nothing
#   else. A module may store an instant, pass it on and reply with one;
#   `DateTime.diff/add/compare/to_iso8601` are `{:error, ..}` rows and `<`,
#   `>`, `+`, `-` on an operand of type `Instant` are refused with a message
#   saying the model has no clock. Two instants are therefore equal, which
#   is a fact about the model and not about time: no property should rest on
#   it. Timeouts, which *are* modelled, are a different thing (`sendAfter`
#   and the `after` generation counter above).
#
# A module name as a value (`Fallback`, `Loom.MCP.Client` in an expression,
#   `module()` in a @type) is a constant of a `Module` inductive the file
#   generates from the names used, dotted names joined with `_`. It can be
#   stored, sent and compared; nothing can be called on it.
#
# Logging is not an effect. `Logger.debug/info/notice/warn/warning/error/
#   critical/alert/emergency` at both arities, `Logger.log/2,3`,
#   `Logger.metadata/1` and `Logger.configure/1` are `:noop` rows: the
#   statement is removed from the body before translation, arguments
#   included, wherever `:ets.*` statements are removed -- inside `init/1`
#   too. A pattern variable whose only use was such a statement is renamed
#   `_v`, as an unused one always is.
#
# The @type declarations are the type oracle: they decide when a pattern
# variable at an `Option` position needs `some`, when `nil` is `none`, and
# what the Lean inductives look like. This is the point where Elixir's
# gradual types and Lean's dependent types meet.

defmodule ToLean do
  # ---------- the remote-call table ----------
  #
  # ONE table says what every supported standard-library call becomes. A row
  # is `{module segments, function, arity, action}` and the next round
  # extends the translator to a new function by adding a row, not by adding
  # a clause to `expr/3`. Actions:
  #
  #   :noop            a statement with no effect in the model. It is dropped
  #                    from the body before anything is translated (like the
  #                    `:ets.*` calls), so its arguments are never rendered
  #                    and it can never become an effect. Not an expression.
  #   {:error, why}    a clear translation error: `why` says what the model
  #                    lacks. Use this for a function whose meaning the model
  #                    cannot represent, so it is refused instead of faked.
  #   {:assoc, op}     an association-list operation over a keyword list, the
  #                    same `Leanactors/AssocList.lean` a map uses. `op` is
  #                    the `map_call/4` name (`:get`, `:put`, ..), so
  #                    `Keyword.get/3` and `Map.get/3` render identically.
  #   {:set, fun}      `Leanactors/SetList.lean` `fun` applied to the
  #                    rendered arguments in order.
  #   {:const, e, t}   a constant Lean expression `e` of Lean type `t` (the
  #                    argument expressions are ignored: they are the units
  #                    and calendars the model does not have).
  #   {:fun, f, ats, t}
  #                    the Lean function `f` applied to the arguments, each
  #                    rendered at its Lean type in `ats`, with result type
  #                    `t` (any of them may be nil for "unknown"). This is
  #                    the row kind for an ordinary total function.
  #
  # A module/function/arity with no row falls through to the usual
  # "unsupported" error, which names the call.
  @remote [
    # Logging is not an effect of the actor model: the BEAM's Logger is a
    # separate process this model does not run, and a log line cannot change
    # any actor's state, so every level and both arities are dropped. A
    # `Logger.info("..#{e}..")` therefore needs no string support at all.
    {[:Logger], :debug, 1, :noop},
    {[:Logger], :debug, 2, :noop},
    {[:Logger], :info, 1, :noop},
    {[:Logger], :info, 2, :noop},
    {[:Logger], :notice, 1, :noop},
    {[:Logger], :notice, 2, :noop},
    {[:Logger], :warn, 1, :noop},
    {[:Logger], :warn, 2, :noop},
    {[:Logger], :warning, 1, :noop},
    {[:Logger], :warning, 2, :noop},
    {[:Logger], :error, 1, :noop},
    {[:Logger], :error, 2, :noop},
    {[:Logger], :critical, 1, :noop},
    {[:Logger], :critical, 2, :noop},
    {[:Logger], :alert, 1, :noop},
    {[:Logger], :alert, 2, :noop},
    {[:Logger], :emergency, 1, :noop},
    {[:Logger], :emergency, 2, :noop},
    {[:Logger], :log, 2, :noop},
    {[:Logger], :log, 3, :noop},
    {[:Logger], :metadata, 1, :noop},
    {[:Logger], :configure, 1, :noop},

    # A keyword list is `List (Atom × V)`, so `Keyword` is `AssocList`.
    {[:Keyword], :get, 2, {:assoc, :get}},
    {[:Keyword], :get, 3, {:assoc, :get}},
    {[:Keyword], :fetch, 2, {:assoc, :fetch}},
    {[:Keyword], :fetch!, 2, {:assoc, :fetch!}},
    {[:Keyword], :put, 3, {:assoc, :put}},
    {[:Keyword], :delete, 2, {:assoc, :delete}},
    {[:Keyword], :has_key?, 2, {:assoc, :has_key?}},
    {[:Keyword], :keys, 1, {:assoc, :keys}},
    {[:Keyword], :values, 1, {:assoc, :values}},
    # `opts[:k]`, which is `Access.get(opts, :k)` after parsing, is the same
    # lookup over the same list (and, like `Map.get/2`, an Option).
    {[:Access], :get, 2, {:assoc, :get}},
    {[:Access], :get, 3, {:assoc, :get}},

    # A MapSet is a duplicate-free list in insertion order.
    {[:MapSet], :new, 0, {:const, "[]", nil}},
    {[:MapSet], :new, 1, {:set, "SetList.ofList"}},
    {[:MapSet], :put, 2, {:set, "SetList.insert"}},
    {[:MapSet], :delete, 2, {:set, "SetList.erase"}},
    {[:MapSet], :member?, 2, {:set, "SetList.contains"}},
    {[:MapSet], :size, 1, {:set, "SetList.size"}},
    {[:MapSet], :to_list, 1, {:set, "SetList.toList"}},
    {[:MapSet], :union, 2, {:set, "SetList.union"}},
    {[:MapSet], :difference, 2, {:set, "SetList.difference"}},
    {[:MapSet], :intersection, 2, {:set, "SetList.intersection"}},

    # The clock the model does not have: every read is the one opaque
    # `Instant` of Leanactors/Time.lean, and anything that would order or
    # subtract two instants is refused rather than faked.
    {[:DateTime], :utc_now, 0, {:const, "Instant.now", "Instant"}},
    {[:DateTime], :utc_now, 1, {:const, "Instant.now", "Instant"}},
    {[:NaiveDateTime], :utc_now, 0, {:const, "Instant.now", "Instant"}},
    {[:NaiveDateTime], :utc_now, 1, {:const, "Instant.now", "Instant"}},
    {[:Date], :utc_today, 0, {:const, "Instant.now", "Instant"}},
    {[:System], :monotonic_time, 0, {:const, "Instant.now", "Instant"}},
    {[:System], :monotonic_time, 1, {:const, "Instant.now", "Instant"}},
    {[:System], :system_time, 0, {:const, "Instant.now", "Instant"}},
    {[:System], :system_time, 1, {:const, "Instant.now", "Instant"}},
    {[:System], :os_time, 0, {:const, "Instant.now", "Instant"}},
    {[:System], :os_time, 1, {:const, "Instant.now", "Instant"}},
    {[:DateTime], :diff, 2, {:error, "the model has no clock: an Instant has equality and nothing else"}},
    {[:DateTime], :diff, 3, {:error, "the model has no clock: an Instant has equality and nothing else"}},
    {[:DateTime], :add, 2, {:error, "the model has no clock: an Instant has equality and nothing else"}},
    {[:DateTime], :add, 3, {:error, "the model has no clock: an Instant has equality and nothing else"}},
    {[:DateTime], :compare, 2, {:error, "the model has no clock: two Instants are always equal, so a comparison would be meaningless"}},
    {[:DateTime], :before?, 2, {:error, "the model has no clock: two Instants are always equal, so a comparison would be meaningless"}},
    {[:DateTime], :after?, 2, {:error, "the model has no clock: two Instants are always equal, so a comparison would be meaningless"}},
    {[:DateTime], :to_iso8601, 1, {:error, "an Instant has no printable form in the model"}},
    {[:DateTime], :to_unix, 1, {:error, "the model has no clock: an Instant has equality and nothing else"}},

    # Binaries, where Lean's own String has the function.
    {[:String], :length, 1, {:fun, "String.length", ["String"], "Nat"}},
    {[:String], :upcase, 1, {:fun, "String.toUpper", ["String"], "String"}},
    {[:String], :downcase, 1, {:fun, "String.toLower", ["String"], "String"}},
    {[:String], :to_string, 1, {:fun, "Str.toStr", [nil], "String"}}
  ]

  defmodule Ctx do
    defstruct types: %{}, msg_ctors: [], st_ctors: [], pids: %{}, enums: %{}, ns: "Gen", warnings: [],
              extra: [], awaits: %{}, reply_type: nil, traps: %{}, pid_vars: [],
              covered: [], inits: %{}, mods: [], kinds: %{}, loops: %{}, defers: [], afters: %{},
              pubsub: [[:Phoenix, :PubSub], [:PubSub]], attrs: %{}, init_subs: %{},
              structs: %{}, struct_states: %{}, struct_order: [],
              records: %{}, ets: [], ignored: [], events: [],
              locals: %{}, local_specs: %{}, local_decls: ""
  end

  # ---------- entry ----------

  def main([src, ns | rest]) do
    {out, warnings} = compile(src, ns, rest, nil)
    IO.puts(out)
    Enum.each(warnings, &IO.puts(:stderr, "warning: " <> &1))
  end

  def main(_), do: IO.puts(:stderr, "usage: to_lean.exs SRC.ex NAMESPACE [--pid Mod=const] [--pubsub Mod]")

  # The whole translation. `reply` is the Lean type the file's replies were
  # probed to have (see `reply_probe`), or nil on the first pass.
  defp compile(src, ns, rest, reply) do
    # a second pass starts from a clean slate: the notes below are collected
    # while the source is walked, and would otherwise be reported twice
    Process.delete(:to_lean_reg_notes)
    pids =
      rest
      |> Enum.chunk_every(2)
      |> Enum.flat_map(fn
        ["--pid", kv] -> [kv |> String.split("=") |> List.to_tuple()]
        _ -> []
      end)
      |> Map.new()
    # modules treated as PubSub (`--pubsub My.PubSub`), besides Phoenix.PubSub and PubSub
    pubsubs =
      rest
      |> Enum.chunk_every(2)
      |> Enum.flat_map(fn
        ["--pubsub", m] -> [m |> String.split(".") |> Enum.map(&String.to_atom/1)]
        _ -> []
      end)

    {:ok, ast} = src |> File.read!() |> Code.string_to_quoted(columns: false)
    # a module `Loom.Teams.TableRegistry` is known by its last segment
    mods = for {:defmodule, _, [{:__aliases__, _, segs}, [do: body]]} <- top(ast),
               do: {List.last(segs), strip_resource_noops(List.last(segs), rewrite_assigns(desugar(subst_attrs(stmts(body)))))}
    # registered names: the --pid flags if any are given, else derived from
    # the source (name: __MODULE__ in start_link/start, Process.register/2)
    pids = if map_size(pids) == 0, do: register_names(mods), else: pids
    # module-local helpers: the def/defp that are not callbacks. The ones a
    # callback reaches are translated into Lean definitions emitted before
    # `beh`, and every call to one is rewritten to the private node
    # `{:__local_call__, meta, [id | args]}` before anything else runs.
    ldefs = for {name, body} <- mods, into: %{}, do: {name, local_defs(name, body)}
    lreach = for {name, body} <- mods, into: %{}, do: {name, reachable_locals(ldefs[name], body)}
    mods = for {name, body} <- mods, do: {name, rewrite_def_bodies(ldefs[name], lreach[name], name, body)}
    ldefs = for {name, body} <- mods, into: %{}, do: {name, local_defs(name, body)}
    locals = for {name, _} <- mods, k <- lreach[name], into: %{}, do: {local_id(name, k), ldefs[name][k]}
    specs = for {name, body} <- mods, {id, sp} <- local_specs(name, body), into: %{}, do: {id, sp}
    ctx = %Ctx{ns: ns, pids: pids, locals: locals, local_specs: specs}
    ctx = %{ctx | pubsub: ctx.pubsub ++ pubsubs}
    # every module's @type declarations and defstruct first (a struct or a
    # remote type `Mod.t()` may be used before the module that declares it),
    # then the message and state constructors of the GenServer modules
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_raw_types(c, name, body) end)
    ctx = collect_structs(ctx)
    # a module with a defstruct and no callbacks or receive loop only
    # declares a struct: it has no state and no clauses
    mods = Enum.reject(mods, fn {name, body} -> struct_only?(ctx, name, body) end)
    # untyped mode: message unions, the reply and the state a module does
    # not declare are inferred from its clauses, replies, sends and init/1;
    # a declaration always wins over an inferred one
    ctx = %{ctx | types: Map.merge(infer_types(ctx, mods, reply), ctx.types)}
    ctx = Enum.reduce(mods, ctx, fn {name, body}, c -> collect_types(c, name, body) end)
    # modules that create ETS tables carry a hidden counter field `ets`
    ctx = %{ctx | ets: for({name, body} <- mods, ets_new?(body), do: name),
                  ignored: for({name, body} <- mods, f <- ignored_defs(body),
                                not String.starts_with?(f, "handle_event/"),
                                not Map.has_key?(locals, "#{name}.#{f}"), do: "#{name}.#{f}"),
                  events: for({name, body} <- mods, f <- ignored_defs(body),
                              String.starts_with?(f, "handle_event/"), do: "#{name}.#{f}")}
    # the tagged unions and structs by Lean name, for the expression and
    # pattern renderers (which do not carry the context)
    Process.put(:to_lean_unions, tagged_unions(ctx))
    Process.put(:to_lean_structs, ctx.structs)
    Process.put(:to_lean_struct_states, ctx.struct_states)
    # the first alternative of every enum, the only default value `hd/1` has
    Process.put(:to_lean_firsts, first_ctors(ctx))
    # the record-shaped modules, for `spat_bare?`/`spat_general?`
    Process.put(:to_lean_records, ctx.records)
    clauses = for {name, body} <- mods, cl <- ordered(clauses(name, body)), do: cl
    traps = for {name, body} <- mods, traps?(body), into: %{}, do: {name, true}
    inits0 = for {name, body} <- mods, init = init_of(ctx, name, body), init != nil, do: {name, init}
    inits = for {name, {p, e, _, _}} <- inits0, into: %{}, do: {name, {p, e}}
    # the PubSub subscriptions init/1 makes, attributed to the child at its spawn site
    init_subs = for {name, {_, _, subs, _}} <- inits0, subs != [], into: %{}, do: {name, subs}
    init_notes = for {_, {_, _, _, notes}} <- inits0, n <- notes, uniq: true, do: n
    # raw receive loops: module -> loop function; those without a catch-all
    # clause defer (re-enqueue) unmatched messages; those with an `after`
    # clause arm a self-timer for the message after_<loop>
    loops = for {name, body} <- mods, {fname, _, _, _} <- [loop_of(body)], into: %{}, do: {name, fname}
    afters = for {name, body} <- mods, {fname, _, _, ab} <- [loop_of(body)], ab != nil, into: %{}, do: {name, after_tag(fname)}
    defers =
      for {name, _} <- loops,
          not Enum.any?(clauses, fn cl -> cl.mod == name and cl.guard == nil and bare?(cl.mpat) end),
          do: name
    ctx = %{ctx | traps: traps, inits: inits, init_subs: init_subs, mods: Enum.map(mods, &elem(&1, 0)),
                  loops: loops, defers: defers, afters: afters,
                  warnings: ctx.warnings ++ init_notes ++ Process.get(:to_lean_reg_notes, [])}
    # a module whose init/1 subscribes but that nothing in this file spawns:
    # the effect has no spawn site to hang on, so the model would show no
    # subscription at all. Warn; the hand-written example that places such an
    # actor must put the `subscribe` in its own initial effects.
    ctx = Enum.reduce(Map.keys(init_subs), ctx, fn m, c ->
      if m in spawned_modules(ast) do
        c
      else
        %{c | warnings: c.warnings ++
          ["#{m}.init/1 subscribes to PubSub but no module in this file spawns #{m}: " <>
           "the subscription is not in the model (place it where the actor is placed)"]}
      end
    end)
    # a raw process has no handle_cast/handle_call: its messages are all info
    for {name, _} <- loops, kt <- [:cast, :call], Map.has_key?(ctx.types, {name, kt}),
        do: fail("#{name} is a raw process (receive loop) and cannot declare @type #{kt}")
    ctx = %{ctx | kinds: classify(ctx, clauses)}
    if map_size(traps) > 0 and not List.keymember?(ctx.msg_ctors, :EXIT, 0),
      do: fail("a trapping module must declare {:EXIT, pid(), term()} in @type msg")
    # the local helpers: their signatures come from a @spec or from the types
    # they are called at, so this runs once everything else is known
    ctx = local_sigs(ctx, clauses)
    ctx = %{ctx | local_decls: render_locals(ctx)}
    # untyped mode: a file whose replies are not literals has no reply union
    # to infer, but the expressions may still have one type between them.
    # Probe for it and, if there is one, compile the file again with it.
    case reply_probe(ctx, clauses, reply) do
      nil ->
        {out, ctx} = render(ctx, clauses)
        {out, ctx.warnings}

      t ->
        compile(src, ns, rest, t)
    end
  end

  # The Lean type of the file's replies, or nil. Untyped mode leaves the
  # reply type opaque (`term()`) when the replies are not all literal atoms
  # and tagged tuples, and a reply whose value does have a type in the model
  # -- a list, a struct, a number -- then has nowhere to go. So when every
  # reply is a non-literal expression, render the clauses once with the reply
  # itself left out (`:to_lean_reply_probe`), collect the types those
  # expressions have in their own clause environments, and report the type
  # when there is exactly one. The caller compiles the file again with it, so
  # every decision downstream is still made from a declared type -- as if the
  # source carried `@type reply :: that`.
  defp reply_probe(_ctx, _clauses, prev) when prev != nil, do: nil

  defp reply_probe(ctx, clauses, _prev) do
    if Process.get(:to_lean_reply_candidate, false) do
      Process.put(:to_lean_reply_types, [])
      Process.put(:to_lean_reply_probe, true)

      try do
        render(ctx, clauses)
      after
        Process.delete(:to_lean_reply_probe)
      end

      case Process.get(:to_lean_reply_types, []) |> Enum.reject(&is_nil/1) |> Enum.uniq() do
        [t] when t != "Term" -> t
        _ -> nil
      end
    end
  end

  # every module spawned by `GenServer.start_link/start(Mod, _)` in the file
  defp spawned_modules(ast) do
    {_, mods} =
      Macro.prewalk(ast, [], fn
        {{:., _, [{:__aliases__, _, [:GenServer]}, f]}, _, [{:__aliases__, _, [child]} | _]} = n, acc
        when f in [:start_link, :start] -> {n, [child | acc]}
        n, acc -> {n, acc}
      end)
    mods
  end

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
  # (that module), an alias or an atom. The Lean constant is N underscored
  # (`Cache` -> `cache`, `TableRegistry` -> `table_registry`).
  defp register_names(mods) do
    for {mod, body} <- mods, name <- registered_in(mod, body), into: %{}, do: {name, Macro.underscore(name)}
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
  # `name: Keyword.get(opts, :name, N)`: the option list a real `start_link`
  # is handed is not modelled (the same rule `init/1` follows), so the
  # registered name is the literal default. Warned about, because a caller
  # that passes `name:` gets a differently named actor than the model has.
  defp reg_name(mod, {{:., _, [{:__aliases__, _, [:Keyword]}, :get]}, _, [{v, _, nil}, :name, d]})
       when is_atom(v) do
    Process.put(:to_lean_reg_notes,
      Process.get(:to_lean_reg_notes, []) ++
        ["#{mod}: the registered name is Keyword.get(#{v}, :name, #{Macro.to_string(d)}); " <>
         "the option list is not modelled, so the model uses the default"])
    reg_name(mod, d)
  end
  defp reg_name(_mod, {:__aliases__, _, segs}), do: Atom.to_string(List.last(segs))
  defp reg_name(_mod, a) when is_atom(a) and a not in [nil, true, false], do: Atom.to_string(a)
  defp reg_name(mod, x), do: fail("#{mod}: unsupported registered name #{Macro.to_string(x)}")

  # the Lean constant for a registered name (an alias `Mod` or an atom `:name`)
  defp pid_const(ctx, name) do
    Map.get(ctx.pids, Atom.to_string(name)) ||
      fail("no registered name for #{name}: start it with name: __MODULE__, Process.register/2 it, or pass --pid #{name}=const")
  end

  # the model-only message a receive loop with `after` sends itself
  defp after_tag(fname), do: :"after_#{fname}"

  # ---------- untyped mode: inferred declarations ----------

  # The @type declarations a module lacks, inferred from its source and keyed
  # like the declared ones, so everything downstream is type-directed as
  # before. A module with none of @type msg/cast/info/call gets its message
  # unions from the patterns of its handle_cast/handle_info/handle_call
  # clauses (or receive arms): each tag with the arity of its pattern and the
  # kind of the callback, every field `term()` (an opaque `Term`); messages
  # it sends (`send/2`, `GenServer.cast/2`, `Process.send_after/3`) with a
  # literal tag join its msg union. A file with no @type reply gets one
  # inferred from every `{:reply, r, ..}`, `{:stop, _, r, _}` and
  # `GenServer.reply(_, r)`: a tagged union of the literal atoms and tagged
  # tuples (fields `term()`) when every reply is one, `term()` otherwise. A
  # module with no @type state gets the state of its `init/1` literal: a
  # map with atom keys is a record `%{k: T, ..}`, `%{}` a map `%{term() =>
  # term()}`, integers `integer()`, booleans `boolean()`, `nil` `term() |
  # nil`, lists `[term()]`, tuples positionally, anything else `term()`.
  defp infer_types(ctx, mods, reply) do
    declared = fn _mod, body, name ->
      Enum.any?(body, fn
        {:@, _, [{:type, _, [{:"::", _, [{^name, _, _}, _]}]}]} -> true
        _ -> false
      end)
    end
    known_tags =
      for {mod, body} <- mods, name <- [:msg, :cast, :info, :call], declared.(mod, body, name),
          {:@, _, [{:type, _, [{:"::", _, [{^name, _, _}, t]}]}]} <- body, alt <- union(t), do: tag_of(alt)
    msgs =
      for {mod, body} <- mods, not Enum.any?([:msg, :cast, :info, :call], &declared.(mod, body, &1)),
          {name, alts} <- inferred_msgs(mod, body, known_tags), alts != [],
          into: %{}, do: {{mod, name}, union_ast(alts)}
    replies =
      if Enum.any?(mods, fn {mod, body} -> declared.(mod, body, :reply) end) do
        %{}
      else
        rs = for {_, body} <- mods, r <- replies_of(body), do: r
        with_calls = for {mod, body} <- mods, replies_of(body) != [], do: mod
        # a second pass compiles the file with the type the replies were
        # probed to have; on the first pass, record whether probing could help
        Process.put(:to_lean_reply_candidate,
          reply == nil and rs != [] and not Enum.any?(rs, &reply_literal?/1))
        cond do
          rs == [] -> %{}
          Enum.all?(rs, &reply_literal?/1) ->
            alts = rs |> Enum.map(&reply_alt/1) |> Enum.uniq_by(&{tag_of(&1), tuple_arity(&1)})
            for mod <- with_calls, into: %{}, do: {{mod, :reply}, union_ast(alts)}
          reply != nil ->
            for mod <- with_calls, into: %{}, do: {{mod, :reply}, {:__lean__, [], [reply]}}
          true ->
            for mod <- with_calls, into: %{}, do: {{mod, :reply}, {:term, [], []}}
        end
      end
    states =
      for {mod, body} <- mods, not declared.(mod, body, :state),
          t = inferred_state(ctx, mod, body), t != nil,
          into: %{}, do: {{mod, :state}, t}
    Map.merge(msgs, replies) |> Map.merge(states)
  end

  # the state type of a module that does not declare one: the literal of its
  # init/1, or -- when it has no init/1 either -- the shape its callbacks
  # match the state at (`state_from_clauses`)
  defp inferred_state(ctx, mod, body) do
    case init_of(ctx, mod, body) do
      nil -> state_from_clauses(mod, body)
      init -> infer_type(elem(init, 1))
    end
  end

  # A module with neither `@type state` nor an init/1 to infer one from: the
  # shape is read off the callbacks' state patterns, which must agree. A map
  # pattern anywhere makes it a record whose fields are the keys the patterns
  # match and the keys the bodies update or return; tuple patterns of one
  # size make it positional; patterns that only bind the state whole leave it
  # opaque (`term()`). Anything else is nil: the module keeps the error.
  defp state_from_clauses(mod, body) do
    case clauses(mod, body) do
      [] -> nil
      cls ->
        pats = Enum.map(cls, & &1.spat)
        keys = Enum.uniq(Enum.flat_map(pats, &state_pat_keys/1) ++ Enum.flat_map(cls, &state_keys_in(&1.body)))
        sizes = pats |> Enum.map(&state_pat_size/1) |> Enum.uniq()
        record = fn -> {:%{}, [], for(k <- keys, do: {k, state_key_type(cls, k)})} end
        cond do
          # a map pattern anywhere, or -- a LiveView whose callbacks bind the
          # socket whole and update named assigns -- keys only from the bodies
          Enum.any?(pats, &(state_pat_keys(&1) != [])) or (keys != [] and sizes == [:var]) ->
            if keys != [] and Enum.all?(sizes, &(&1 in [:var, :map])),
              do: record.(),
              else: nil
          sizes == [:var] -> {:term, [], []}
          true ->
            case Enum.reject(sizes, &(&1 == :var)) do
              [n] when is_integer(n) and n > 1 -> {:{}, [], List.duplicate({:term, [], []}, n)}
              _ -> nil
            end
        end
    end
  end

  # The type of an inferred record field: the shape of the values the bodies
  # write to it (`%{s | k: e}`, or a record literal returned as the state),
  # read by the same `infer_type` an init/1 literal goes through. Fields
  # nothing pins stay opaque, and so do fields written at two different
  # shapes -- there is no way to choose between them here, and `term()` is
  # the abstraction that is always sound.
  defp state_key_type(cls, k) do
    case cls |> Enum.flat_map(&state_key_values(&1.body, k)) |> Enum.map(&infer_type/1)
             |> Enum.reject(&(&1 == {:term, [], []})) |> Enum.uniq() do
      [t] -> t
      _ -> {:term, [], []}
    end
  end

  defp state_key_values(body, k) do
    {_, vs} =
      Macro.prewalk(body, [], fn
        {:%{}, _, [{:|, _, [_, kvs]}]} = n, acc when is_list(kvs) ->
          {n, acc ++ for({^k, v} <- kvs, do: v)}
        {:%{}, _, kvs} = n, acc when is_list(kvs) ->
          {n, acc ++ for({^k, v} <- kvs, do: v)}
        n, acc -> {n, acc}
      end)

    vs
  end

  # the atom keys a state pattern matches (`%{f: p, ..}`, optionally `= s`)
  defp state_pat_keys({:=, _, [{:%{}, _, _} = p, {v, _, nil}]}) when is_atom(v), do: state_pat_keys(p)
  defp state_pat_keys({:%{}, _, kvs}) when is_list(kvs), do: for({k, _} <- kvs, atom_key?(k), do: k)
  defp state_pat_keys(_), do: []

  defp atom_key?(k), do: is_atom(k) and k not in [nil, true, false]

  # :var (binds the state whole), :map (a map pattern), a tuple size, or nil
  defp state_pat_size({v, _, nil}) when is_atom(v), do: :var
  defp state_pat_size({:=, _, [{:%{}, _, _}, {v, _, nil}]}) when is_atom(v), do: :map
  defp state_pat_size({:%{}, _, kvs}) when is_list(kvs), do: :map
  defp state_pat_size({:{}, _, xs}), do: length(xs)
  defp state_pat_size({_, _}), do: 2
  defp state_pat_size(_), do: nil

  # the record keys a body mentions: a map update `%{s | k: e}` and a map
  # literal returned as the new state
  defp state_keys_in(body) do
    {_, keys} =
      Macro.prewalk(body, [], fn
        {:%{}, _, [{:|, _, [_, kvs]}]} = n, acc when is_list(kvs) ->
          {n, acc ++ for({k, _} <- kvs, atom_key?(k), do: k)}
        {:noreply, {:%{}, _, kvs}} = n, acc when is_list(kvs) ->
          {n, acc ++ for({k, _} <- kvs, atom_key?(k), do: k)}
        {:{}, _, [:reply, _, {:%{}, _, kvs}]} = n, acc when is_list(kvs) ->
          {n, acc ++ for({k, _} <- kvs, atom_key?(k), do: k)}
        n, acc -> {n, acc}
      end)

    Enum.uniq(keys)
  end

  # {kind name, alternatives} for an undeclared module: the clause patterns
  # by callback, then the sent messages whose tag nobody declares or handles
  defp inferred_msgs(mod, body, known_tags) do
    cls = clauses(mod, body)
    by_kind =
      for cl <- cls, not bare?(cl.mpat), cl[:after] == nil, {tag, args} = msg_shape(cl.mpat), reduce: %{} do
        acc ->
          name = if(loop_of(body) != nil, do: :msg, else: %{handle_cast: :cast, handle_info: :info, handle_call: :call}[cl.kind])
          case Enum.find(Map.get(acc, name, []), &(tag_of(&1) == tag)) do
            nil -> Map.update(acc, name, [msg_alt(tag, length(args))], &(&1 ++ [msg_alt(tag, length(args))]))
            alt ->
              tuple_arity(alt) == length(args) ||
                fail("#{mod}: message tag #{tag} is matched with #{tuple_arity(alt)} and #{length(args)} arguments; declare its shape with a @type")
              acc
          end
      end
    handled = for {_, alts} <- by_kind, alt <- alts, do: tag_of(alt)
    sent =
      for m <- sent_msgs(body), tag_of(m) != nil, tag_of(m) not in handled, tag_of(m) not in known_tags,
          uniq: true, do: msg_alt(tag_of(m), tuple_arity(m))
    Map.to_list(Map.update(by_kind, :msg, sent, &(&1 ++ sent)))
  end

  defp msg_alt(tag, 0), do: tag
  defp msg_alt(tag, n), do: {:{}, [], [tag | List.duplicate({:term, [], []}, n)]}

  defp union_ast([a]), do: a
  defp union_ast([a | rest]), do: {:|, [], [a, union_ast(rest)]}

  defp tuple_arity(a) when is_atom(a), do: 0
  defp tuple_arity({_, _}), do: 1
  defp tuple_arity({:{}, _, [_ | rest]}), do: length(rest)

  # message literals the module sends (a variable message has no tag to infer)
  defp sent_msgs(body) do
    {_, ms} = Macro.prewalk({:__block__, [], body}, [], fn
      {:send, _, [_, m]} = n, acc -> {n, [m | acc]}
      {{:., _, [{:__aliases__, _, [:GenServer]}, :cast]}, _, [_, m]} = n, acc -> {n, [m | acc]}
      {{:., _, [{:__aliases__, _, [:Process]}, :send_after]}, _, [_, m, _]} = n, acc -> {n, [m | acc]}
      # a PubSub broadcast delivers its message to the subscribers, so its
      # literal is a message of this file exactly as a `send` is
      {{:., _, [{:__aliases__, _, segs}, f]}, _, [_, _, m]} = n, acc
        when f in [:broadcast, :broadcast!] ->
        if List.last(segs) == :PubSub, do: {n, [m | acc]}, else: {n, acc}
      n, acc -> {n, acc}
    end)
    Enum.reverse(ms) |> Enum.filter(&(is_atom(&1) or tagged_tuple?(&1)))
  end

  # every reply expression of a module's callbacks, in source order
  defp replies_of(body) do
    {_, rs} = Macro.prewalk({:__block__, [], body}, [], fn
      {:{}, _, [:reply, r, _]} = n, acc -> {n, [r | acc]}
      {:{}, _, [:reply, r, _, _]} = n, acc -> {n, [r | acc]}
      {:{}, _, [:stop, _, r, _]} = n, acc -> {n, [r | acc]}
      {{:., _, [{:__aliases__, _, [:GenServer]}, :reply]}, _, [_, r]} = n, acc -> {n, [r | acc]}
      n, acc -> {n, acc}
    end)
    Enum.reverse(rs)
  end

  defp reply_literal?(a) when is_atom(a) and a not in [nil, true, false], do: true
  defp reply_literal?(t), do: tagged_tuple?(t)

  defp reply_alt(a) when is_atom(a), do: a
  defp reply_alt(t), do: msg_alt(tag_of(t), tuple_arity(t))

  # the type of an init/1 state literal (see infer_types)
  defp infer_type({:%{}, _, []}), do: {:%{}, [], [{{:term, [], []}, {:term, [], []}}]}
  defp infer_type({:%{}, _, pairs} = e) do
    Keyword.keyword?(pairs) || fail("cannot infer a state type from #{Macro.to_string(e)}: give it a @type state")
    {:%{}, [], for({k, v} <- pairs, do: {k, infer_type(v)})}
  end
  defp infer_type(n) when is_integer(n), do: {:integer, [], []}
  defp infer_type(s) when is_binary(s), do: {:binary, [], []}
  defp infer_type({:<<>>, _, _}), do: {:binary, [], []}
  defp infer_type({:<>, _, [_, _]}), do: {:binary, [], []}
  defp infer_type(b) when is_boolean(b), do: {:boolean, [], []}
  defp infer_type(nil), do: {:|, [], [{:term, [], []}, nil]}
  defp infer_type(l) when is_list(l), do: [{:term, [], []}]
  # `l ++ [x]`: whichever side is a list says what the value is
  defp infer_type({:++, _, [a, b]}) do
    case {infer_type(a), infer_type(b)} do
      {[t], _} -> [t]
      {_, [t]} -> [t]
      _ -> {:term, [], []}
    end
  end
  defp infer_type({:{}, _, xs}), do: {:{}, [], Enum.map(xs, &infer_type/1)}
  defp infer_type({a, b}), do: {:{}, [], [infer_type(a), infer_type(b)]}
  # a struct literal is that struct's type, whatever fields the literal sets
  # (the field types come from `defstruct` and `@type t`, not from here)
  defp infer_type({:%, _, [m, {:%{}, _, _}]}), do: {:%, [], [m, {:%{}, [], []}]}
  defp infer_type(_), do: {:term, [], []}

  # ---------- external resources ----------

  # `:ets.f(...)` as a statement, and a `try do .. rescue .. end` whose body
  # is only such calls, are removed before translation: the model does not
  # see ETS. `:ets.new(...)` on the right of a binding stays (it yields a
  # fresh opaque reference, see `sends`). A try/rescue around anything else
  # is an error: caught exceptions are not modelled.
  defp strip_resource_noops(mod, body) do
    Macro.prewalk(body, fn
      {:__block__, m, stmts} -> {:__block__, m, Enum.reject(stmts, &resource_noop?(mod, &1))}
      n -> n
    end)
  end

  defp resource_noop?(_mod, {{:., _, [:ets, _f]}, _, _}), do: true
  defp resource_noop?(mod, {:try, _, [opts]} = t) do
    Enum.each(Keyword.keys(opts), fn k -> k in [:do, :rescue] || fail("#{mod}: try with #{k} is not supported: #{Macro.to_string(t)}") end)
    Enum.all?(stmts(opts[:do]), &match?({{:., _, [:ets, _]}, _, _}, &1)) ||
      fail("#{mod}: try/rescue is only supported around external resource calls (:ets.*), which are no-ops in the model; got #{Macro.to_string(t)}")
    true
  end
  # a @remote row of `:noop` (every Logger call): logging is not an effect
  # of the actor model, so the statement and its arguments disappear before
  # anything is translated
  defp resource_noop?(_mod, e) when is_tuple(e) and tuple_size(e) == 3, do: remote_noop?(e)
  defp resource_noop?(_mod, _), do: false

  defp ets_new?(body) do
    {_, found} = Macro.prewalk({:__block__, [], body}, false, fn
      {{:., _, [:ets, :new]}, _, _} = n, _ -> {n, true}
      n, acc -> {n, acc}
    end)
    found
  end

  # public functions that are not callbacks (API wrappers around
  # GenServer.call/cast, `raise` inside them included) are not translated;
  # start/start_link are the conventional entry points and go unmentioned
  @callbacks [:init, :handle_cast, :handle_info, :handle_call, :handle_continue, :start, :start_link, :terminate, :child_spec]
  defp ignored_defs(body) do
    loop = case loop_of(body), do: ({f, _, _, _} -> f; nil -> nil)
    for {:def, _, [head | _]} <- body, {f, args, _} = head_parts(head), f not in @callbacks, f != loop,
        uniq: true, do: "#{f}/#{length(args || [])}"
  end

  # ---------- module-local functions ----------
  #
  # A `def`/`defp` of a module that is not a callback and that a callback
  # reaches (directly or through another helper) becomes a Lean definition
  # emitted before `beh`; every call to it is rewritten, before translation,
  # to the private node `{:__local_call__, meta, [id | args]}` so that no
  # other expression form can be confused with it.

  # names the translator gives its own meaning to: a def of one of them is
  # not a helper the model may call
  @local_reserved [:send, :spawn, :spawn_link, :spawn_monitor, :exit, :raise, :throw, :self,
                   :receive, :not, :and, :or, :length, :hd, :tl, :is_map_key, :map_size, :for]

  defp strip_default({:\\, _, [p, _]}), do: p
  defp strip_default(p), do: p

  # every non-callback def/defp of a module, by {name, arity}:
  # %{mod, name, arity, min_arity, defaults, clauses: [{params, guard, body}]}.
  # Default arguments make the function callable at every arity from
  # min_arity up; the missing arguments are filled in at the call site.
  defp local_defs(mod, body) do
    loop =
      case loop_of(body) do
        {f, _, _, _} -> f
        nil -> nil
      end

    for {d, _, [head | rest]} <- body, d in [:def, :defp],
        {f, args, guard} = head_parts(head),
        f not in @callbacks, f != loop, f not in @local_reserved,
        reduce: %{} do
      acc ->
        args = args || []
        blocks =
          case rest do
            [kw] when is_list(kw) -> kw
            _ -> []
          end
        params = Enum.map(args, &strip_default/1)
        defaults = for {:\\, _, [_, dv]} <- args, do: dv
        key = {f, length(params)}
        e =
          Map.get(acc, key, %{mod: mod, name: f, arity: length(params), min_arity: length(params),
                              defaults: [], clauses: [], blocks: [], id: local_id(mod, key)})
        e = if defaults == [], do: e, else: %{e | defaults: defaults, min_arity: length(params) - length(defaults)}
        e =
          if blocks[:do] == nil,
            do: e,
            else: %{e | clauses: e.clauses ++ [{params, guard, blocks[:do]}],
                        blocks: e.blocks ++ (Keyword.keys(blocks) -- [:do])}
        Map.put(acc, key, e)
    end
  end

  defp local_id(mod, {f, n}), do: "#{mod}.#{f}/#{n}"

  defp local_lname(id) do
    [m, rest] = String.split(id, ".", parts: 2)
    [f, _] = String.split(rest, "/", parts: 2)
    ctor_name(String.to_atom(m)) <> "_" <> lean_ident(f)
  end

  # the {name, arity} of the local a bare call `f(a1, .., an)` resolves to
  defp local_key(defs, f, n) do
    Enum.find(Map.keys(defs), fn {g, m} -> g == f and n <= m and n >= defs[{g, m}].min_arity end)
  end

  # the bodies a local helper may be reached from
  defp local_roots(body) do
    loop =
      case loop_of(body) do
        {f, _, _, _} -> f
        nil -> nil
      end

    for {:def, _, [head | rest]} <- body,
        {f, _, _} = head_parts(head),
        f in [:init, :handle_cast, :handle_info, :handle_call, :handle_continue] or f == loop,
        [kw] <- [rest],
        is_list(kw),
        kw[:do] != nil,
        do: kw[:do]
  end

  defp local_calls_in(defs, ast) do
    {_, acc} =
      Macro.prewalk(ast, [], fn
        {f, _, args} = n, acc when is_atom(f) and is_list(args) ->
          case local_key(defs, f, length(args)) do
            nil -> {n, acc}
            k -> {n, [k | acc]}
          end

        n, acc -> {n, acc}
      end)

    Enum.uniq(acc)
  end

  # the helpers a callback reaches, transitively
  defp reachable_locals(defs, body) do
    seed = body |> local_roots() |> Enum.flat_map(&local_calls_in(defs, &1)) |> Enum.uniq()
    close_locals(defs, seed, seed)
  end

  defp close_locals(_defs, [], acc), do: acc

  defp close_locals(defs, frontier, acc) do
    next =
      for k <- frontier, e = defs[k], {_, _, b} <- e.clauses, c <- local_calls_in(defs, b),
          c not in acc, uniq: true, do: c

    close_locals(defs, next, acc ++ next)
  end

  # rewrite the calls to reachable helpers inside every def body of a module
  defp rewrite_def_bodies(defs, reach, mod, body) do
    Enum.map(body, fn
      {d, m, [head | rest]} when d in [:def, :defp] ->
        rest =
          Enum.map(rest, fn
            kw when is_list(kw) -> for {k, v} <- kw, do: {k, rewrite_local_calls(defs, reach, mod, v)}
            other -> other
          end)

        {d, m, [head | rest]}

      other -> other
    end)
  end

  defp rewrite_local_calls(defs, reach, mod, ast) do
    Macro.prewalk(ast, fn
      {f, m, args} = n when is_atom(f) and is_list(args) ->
        case local_key(defs, f, length(args)) do
          nil -> n
          k ->
            if k in reach do
              e = defs[k]
              {:__local_call__, m, [local_id(mod, k) | args ++ Enum.drop(e.defaults, length(args) - e.min_arity)]}
            else
              n
            end
        end

      n -> n
    end)
  end

  # `@spec f(T, ..) :: R`, the type oracle for a helper when it is given
  defp local_specs(mod, body) do
    for {:@, _, [{:spec, _, [{:"::", _, [{f, _, argts}, rt]}]}]} <- body, is_list(argts), is_atom(f),
        into: %{}, do: {local_id(mod, {f, length(argts)}), {argts, rt}}
  end

  defp local_callees(ast) do
    {_, acc} =
      Macro.prewalk(ast, [], fn
        {:__local_call__, _, [id | _]} = n, acc -> {n, [id | acc]}
        n, acc -> {n, acc}
      end)

    Enum.uniq(acc)
  end

  defp local_callees_of(entry), do: Enum.flat_map(entry.clauses, fn {_, _, b} -> local_callees(b) end) |> Enum.uniq()

  # dependency order: a helper is emitted after the helpers it calls. A cycle
  # between two helpers is mutual recursion, which Lean would need a `mutual`
  # block for; self-recursion is not a cycle here.
  defp order_locals(locals) do
    order_locals(locals, locals |> Map.keys() |> Enum.sort(), [])
  end

  defp order_locals(_locals, [], done), do: done

  defp order_locals(locals, pending, done) do
    {ready, rest} =
      Enum.split_with(pending, fn id ->
        Enum.all?(local_callees_of(locals[id]) -- [id], &(&1 in done or not Map.has_key?(locals, &1)))
      end)

    ready == [] &&
      fail("mutually recursive local helpers #{Enum.join(pending, ", ")}: a helper may call itself, " <>
             "but a cycle would need a Lean `mutual` block")

    order_locals(locals, rest, done ++ ready)
  end

  # ---- signatures ----

  # how many times the signature inference is iterated (see `local_sigs`)
  @local_rounds 3

  # {argument types, result type} of a helper: its @spec when it has one,
  # otherwise the types it is used at (the arguments and the expected result
  # at its call sites, which must agree) and `Term` for what use does not fix.
  defp local_sigs(ctx, clauses) do
    ctx = %{ctx | locals: for({id, e} <- ctx.locals, into: %{}, do: {id, Map.merge(e, %{ptypes: nil, rtype: nil, fuel: false})})}
    Process.put(:to_lean_local_sigs, sig_table(ctx))
    # Three rounds, each starting from the types the last one found: the
    # first sees only the call sites in the callbacks (the helpers' own
    # bodies cannot render yet), the next two see the helpers calling each
    # other at the types they now have.
    Enum.reduce(1..@local_rounds, ctx, fn _, c ->
      c = assign_sigs(c, collect_local_uses(c, clauses))
      Process.put(:to_lean_local_sigs, sig_table(c))
      c
    end)
  end

  defp sig_table(ctx) do
    for {id, e} <- ctx.locals, into: %{} do
      {id, %{lname: local_lname(id), ptypes: e.ptypes, rtype: e.rtype, fuel: e.fuel}}
    end
  end

  # render everything once with the signatures known so far, only to record
  # how each helper is called (`record_local_use`). Errors are swallowed: the
  # real pass reports them.
  defp collect_local_uses(ctx, clauses) do
    Process.put(:to_lean_local_uses, %{})
    Process.put(:to_lean_dry, true)

    try do
      render_clauses(ctx, clauses)
      for id <- order_locals(ctx.locals), do: local_decl(ctx, ctx.locals[id])
    catch
      _, _ -> :ok
    end

    Process.delete(:to_lean_dry)
    Process.get(:to_lean_local_uses, %{})
  end

  defp record_local_use(id, argtypes, rtype) do
    case Process.get(:to_lean_local_uses) do
      nil -> :ok
      uses -> Process.put(:to_lean_local_uses, Map.update(uses, id, [{argtypes, rtype}], &[{argtypes, rtype} | &1]))
    end
  end

  defp assign_sigs(ctx, uses) do
    Enum.reduce(order_locals(ctx.locals), ctx, fn id, c ->
      %{c | locals: Map.put(c.locals, id, sig_of(c, c.locals[id], Map.get(uses, id, [])))}
    end)
  end

  defp sig_of(ctx, entry, uses) do
    entry.clauses == [] && fail("#{entry.id} is called but has no body in this module")
    entry.blocks == [] ||
      fail("#{entry.id}: a local helper with a #{Enum.join(Enum.uniq(entry.blocks), "/")} block is not supported")

    {ptypes, rtype} =
      case Map.get(ctx.local_specs, entry.id) do
        {argts, rt} when length(argts) == entry.arity ->
          {Enum.map(argts, &lean_type(ctx, entry.mod, &1)), lean_type(ctx, entry.mod, rt)}

        _ ->
          ps = for i <- 0..(entry.arity - 1)//1, do: agreed(entry, uses, i) || "Term"
          {ps, nil}
      end

    env = local_env(entry, ptypes)
    {_, _, first_body} = hd(entry.clauses)
    # the definition fixes the result type where it can; the call sites only
    # fill in what it cannot, so an opaque use cannot make a typed helper
    # opaque
    rtype = rtype || local_rtype(env, first_body) || agreed(entry, uses, :result) || "Term"
    fuel = entry.id in local_callees_of(entry) and not structural?(entry)
    # a fuel-limited helper must have a default value to return at fuel 0
    _ = if fuel, do: default_of(ctx, rtype)
    %{entry | ptypes: ptypes, rtype: rtype, fuel: fuel}
  end

  # the single type a helper is used at in one argument position (or at its
  # result); two different ones mean the helper is not monomorphic here
  defp agreed(entry, uses, pos) do
    ts =
      for {argtypes, rt} <- uses,
          t = if(pos == :result, do: rt, else: Enum.at(argtypes, pos)),
          t != nil,
          uniq: true,
          do: t

    case ts do
      [] -> nil
      [t] -> t
      many ->
        where = if pos == :result, do: "its result", else: "argument #{pos + 1}"
        fail("#{entry.id} is used with #{where} at #{Enum.join(many, " and ")}: " <>
               "give it a @spec, or use one type")
    end
  end

  defp local_env(entry, ptypes) do
    {params, _, _} = hd(entry.clauses)

    if Enum.all?(params, &local_var_pat?/1) do
      for {p, t} <- Enum.zip(params, ptypes), into: %{:__mod__ => entry.mod, :__in_local__ => entry.id} do
        {lean_ident(Atom.to_string(elem(p, 0))), t}
      end
    else
      %{:__mod__ => entry.mod, :__in_local__ => entry.id}
    end
  end

  defp local_var_pat?({v, _, nil}) when is_atom(v), do: true
  defp local_var_pat?(_), do: false

  # the result type of a helper body, when the source fixes it
  defp local_rtype(env, {:if, _, [_, [do: a, else: _]]}), do: local_rtype(env, a)
  defp local_rtype(env, {:cond, _, [[do: [{:->, _, [[_], b]} | _]]]}), do: local_rtype(env, b)
  defp local_rtype(env, {:case, _, [_, [do: [{:->, _, [[_], b]} | _]]]}), do: local_rtype(env, b)
  defp local_rtype(env, {:__block__, _, stmts}) when stmts != [], do: local_rtype(env, List.last(stmts))
  defp local_rtype(env, e), do: type_of(env, e)

  # Lean accepts a helper that recurses on the tail of a list argument as
  # structural; anything else gets a fuel parameter.
  defp structural?(entry) do
    entry.arity > 0 and
      Enum.any?(0..(entry.arity - 1)//1, fn i ->
        Enum.all?(entry.clauses, fn {params, _, b} ->
          case Enum.at(params, i) do
            [{:|, _, [_, {t, _, nil}]}] when is_atom(t) ->
              recursive_args(entry.id, b, i) in [[], [{t, [], nil}]]

            _ -> recursive_args(entry.id, b, i) == []
          end
        end)
      end)
  end

  defp recursive_args(id, ast, i) do
    {_, acc} =
      Macro.prewalk(ast, [], fn
        {:__local_call__, _, [^id | args]} = n, acc -> {n, [Enum.at(args, i) | acc]}
        n, acc -> {n, acc}
      end)

    acc |> Enum.map(fn {v, _, nil} when is_atom(v) -> {v, [], nil}; x -> x end) |> Enum.uniq()
  end

  # ---- rendering ----

  defp local_fuel_name, do: "localFuel"

  @local_fuel 64

  defp render_locals(ctx) do
    order = order_locals(ctx.locals)

    if order == [] do
      ""
    else
      fuel =
        if Enum.any?(order, &ctx.locals[&1].fuel) do
          "/-- Fuel for the local helpers whose recursion Lean does not see as structural.\n" <>
            "    A call that would need more than `#{local_fuel_name()}` steps returns the default\n" <>
            "    value of its result type, so such a helper models the Elixir function only up\n" <>
            "    to that depth. -/\ndef #{local_fuel_name()} : Nat := #{@local_fuel}\n\n"
        else
          ""
        end

      fuel <> Enum.map_join(order, "\n", &local_decl(ctx, ctx.locals[&1])) <> "\n"
    end
  end

  defp local_decl(ctx, entry) do
    fuelb = if entry.fuel, do: ["(fuel : Nat)"], else: []

    {binders, inner} =
      case entry.clauses do
        [{params, nil, body}] ->
          if Enum.all?(params, &local_var_pat?/1) do
            names = for p <- params, do: lean_ident(Atom.to_string(elem(p, 0)))
            env = local_env(entry, entry.ptypes)
            {for({n, t} <- Enum.zip(names, entry.ptypes), do: "(#{n} : #{t})"),
             local_expr(ctx, env, body, entry.rtype)}
          else
            {local_binders(entry), local_match(ctx, entry)}
          end

        _ -> {local_binders(entry), local_match(ctx, entry)}
      end

    rhs =
      if entry.fuel,
        do: "match fuel with | 0 => #{paren_or(default_of(ctx, entry.rtype))} | fuel + 1 => (#{inner})",
        else: inner

    head = Enum.join([local_lname(entry.id) | fuelb ++ Enum.map(binders, &hide_unused_binder(&1, rhs))], " ")
    "/-- `#{entry.id}` -/\ndef #{head} : #{entry.rtype} :=\n  #{rhs}\n"
  end

  # a binder the body never mentions would trip Lean's unused-variable linter
  defp hide_unused_binder("(" <> rest = b, rhs) do
    name = rest |> String.split(" ") |> hd()
    if String.starts_with?(name, "_") or Regex.match?(~r/\b#{name}\b/, rhs), do: b, else: "(_" <> rest
  end

  defp local_binders(entry) do
    for {t, i} <- Enum.with_index(entry.ptypes), do: "(a#{i} : #{t})"
  end

  # Clauses that differ only by a `when` guard, all of whose parameters are
  # variables, become an `if` chain in source order; the last clause must be
  # unguarded, since a Lean definition is total.
  defp local_match(ctx, entry) do
    all_vars = Enum.all?(entry.clauses, fn {params, _, _} -> Enum.all?(params, &local_var_pat?/1) end)

    if all_vars and Enum.any?(entry.clauses, fn {_, g, _} -> g != nil end) do
      {_, last, _} = List.last(entry.clauses)
      last == nil ||
        fail("#{entry.id}: the last clause is guarded, so the helper has no value when every guard fails; " <>
               "add an unguarded clause")
      local_guard_chain(ctx, entry, entry.clauses)
    else
      local_arms(ctx, entry)
    end
  end

  defp local_guard_chain(ctx, entry, [{params, nil, body} | _]),
    do: local_expr(ctx, local_clause_env(entry, params), body, entry.rtype)

  defp local_guard_chain(ctx, entry, [{params, g, body} | rest]) do
    env = local_clause_env(entry, params)
    "(if #{expr(env, g, nil)} then #{local_expr(ctx, env, body, entry.rtype)} " <>
      "else #{local_guard_chain(ctx, entry, rest)})"
  end

  # one clause's parameter names, aliased to the definition's binders
  defp local_clause_env(entry, params) do
    for {p, {t, i}} <- Enum.zip(params, Enum.with_index(entry.ptypes)),
        reduce: %{:__mod__ => entry.mod, :__in_local__ => entry.id} do
      env ->
        v = Atom.to_string(elem(p, 0))
        env |> Map.put(lean_ident(v), t) |> Map.put({:alias, v}, "a#{i}")
    end
  end

  defp local_arms(ctx, entry) do
    entry.arity > 0 || fail("#{entry.id}: a helper with no arguments needs a single unguarded clause")
    scruts = Enum.map_join(0..(entry.arity - 1)//1, ", ", &"a#{&1}")

    arms =
      for {params, guard, body} <- entry.clauses do
        guard == nil ||
          fail("#{entry.id}: a `when` guard is only supported when every clause matches its arguments " <>
                 "with variables (otherwise use `if` in the body)")
        env0 = %{:__mod__ => entry.mod, :__in_local__ => entry.id}
        {parts, env, gs} = pat_list(ctx, params, entry.ptypes, env0, [])
        gs == [] || fail("#{entry.id}: this clause pattern needs a guard, which a local helper cannot fall through")
        "| #{Enum.join(parts, ", ")} => #{local_expr(ctx, env, body, entry.rtype)}"
      end

    "match #{scruts} with " <> Enum.join(arms, " ")
  end

  # The pure fragment a helper body may use: `if`, `cond` and `case` as
  # expressions, a block of bindings ending in a value, and anything `expr`
  # renders.
  defp local_expr(ctx, env, e, t) do
    case e do
      {:if, _, [c, [do: a, else: b]]} ->
        "(if #{expr(env, c, "Bool")} then #{local_expr(ctx, env, a, t)} else #{local_expr(ctx, env, b, t)})"

      {:if, _, [_, [do: _]]} ->
        fail("#{env[:__in_local__]}: `if` without `else` has no value (every branch must return one)")

      {:unless, _, _} ->
        fail("#{env[:__in_local__]}: `unless` is not supported (use `if`)")

      {:cond, _, [[do: arms]]} -> local_cond(ctx, env, arms, t)

      {:case, _, [scrut, [do: arms]]} ->
        st = guess_type(env, scrut)

        strs =
          for {:->, _, [[p], b]} <- arms do
            {pstr, env2, gs} = pat(ctx, prune_arm_vars(p, b, env), st, env, [])
            gs == [] || fail("#{env[:__in_local__]}: a pattern needing a guard is not supported in a local helper")
            "| #{pstr} => #{local_expr(ctx, env2, b, t)}"
          end

        "(match #{expr(env, scrut, nil)} with " <> Enum.join(strs, " ") <> ")"

      {:__block__, _, stmts} -> local_block(ctx, env, stmts, t)
      _ -> expr(env, e, t)
    end
  end

  defp local_cond(ctx, env, [{:->, _, [[c], b]} | rest], t) do
    cond do
      c == true -> local_expr(ctx, env, b, t)
      rest == [] -> fail("#{env[:__in_local__]}: `cond` needs a final `true ->` branch")
      true -> "(if #{expr(env, c, "Bool")} then #{local_expr(ctx, env, b, t)} else #{local_cond(ctx, env, rest, t)})"
    end
  end

  defp local_block(ctx, env, stmts, t) do
    {binds, [last]} = Enum.split(stmts, -1)

    {lets, env} =
      Enum.map_reduce(binds, env, fn
        {:=, _, [{v, _, nil}, rhs]}, e when is_atom(v) ->
          vt = type_of(e, rhs) || expr_type(e, rhs)
          name = lean_ident(Atom.to_string(v))
          s = "let #{name} := #{local_expr(ctx, e, rhs, vt)}"
          {s, if(vt, do: Map.put(e, name, vt), else: e)}

        s, _e ->
          fail("#{env[:__in_local__]}: #{Macro.to_string(s)} is not a binding; a local helper is a pure expression " <>
                 "(it cannot send, spawn or log)")
      end)

    "(" <> Enum.join(lets ++ [local_expr(ctx, env, last, t)], "; ") <> ")"
  end

  # a call to a helper of the same module: its Lean name applied to the
  # arguments (a fuel-limited helper takes the fuel first)
  defp local_call_str(env, id, args, t) do
    sig = Process.get(:to_lean_local_sigs, %{})[id]
    ptypes = (sig && sig.ptypes) || List.duplicate(nil, length(args))
    record_local_use(id, Enum.map(args, &type_of(env, &1)), t)

    fuel =
      cond do
        sig == nil or not sig.fuel -> []
        env[:__in_local__] == id -> ["fuel"]
        true -> [local_fuel_name()]
      end

    name = (sig && sig.lname) || local_lname(id)
    s = Enum.join([name | fuel ++ Enum.map(Enum.zip(args, ptypes), fn {a, pt} -> paren_or(expr(env, a, pt)) end)], " ")
    rt = sig && sig.rtype

    case t do
      "Option " <> inner when rt != nil and rt != t ->
        if unparen(inner) == rt, do: "some " <> paren_or(s), else: s

      _ -> s
    end
  end

  # `init/1` as a pure state expression of its parameter: {param_pattern,
  # expr, pubsub_subscriptions, notes}. `def init(p), do: {:ok, e}`, or a
  # block of statements ending in `{:ok, e}`:
  #
  #   * `Process.flag(:trap_exit, true)` (the module traps exits),
  #   * a PubSub subscribe/unsubscribe (recorded as {:subscribe |
  #     :unsubscribe, topic}, emitted at the spawn site for the child),
  #   * a `Logger` call, dropped (logging is not modelled),
  #   * a binding `v = e` of a pure expression, substituted into the later
  #     statements and into the state expression (init/1 has no Lean binder
  #     of its own: the state is built at the spawn site).
  #
  # The option list init/1 is usually handed is not modelled: a parameter
  # used as one is the empty keyword list, so `Keyword.get(opts, :k, d)` is
  # its literal default `d` and `Keyword.get(opts, :k)` is nil. That is an
  # approximation of a real init, and it is reported as a warning.
  #
  # nil when undefined (the `use GenServer` default init is the identity).
  defp init_of(ctx, mod, body) do
    case for {:def, _, [{:init, _, [p]}, [do: b]]} <- body, do: {p, b} do
      [] -> nil
      [{p, b}] ->
        params = init_params(mod, p)
        {b, opts?} = init_opts(mod, params, b)
        notes = if opts?, do: ["#{mod}.init/1: the option list is modelled as empty, so every " <>
                               "Keyword.get takes its default"], else: []
        {pre, [last]} = Enum.split(stmts(b), -1)
        {subs, notes, binds} = init_pre(ctx, mod, pre, notes)
        e = case last do
          {:ok, e} -> subst_binds(e, binds)
          other -> fail("#{mod}.init/1 must end in {:ok, state}, got #{Macro.to_string(other)}")
        end
        Enum.each(free_vars(e), fn v ->
          v in params || fail("#{mod}.init/1: state expression uses #{v}, which is not a parameter")
        end)
        {_, selfs} = Macro.prewalk(e, false, fn {:self, _, []} = n, _ -> {n, true}; n, a -> {n, a} end)
        selfs && fail("#{mod}.init/1: self() in the initial state is not supported")
        {p, e, subs, notes}
      _ -> fail("#{mod}.init/1 must have exactly one clause")
    end
  end

  # the statements of init/1 before its `{:ok, state}`: {subscriptions,
  # notes, bindings}
  defp init_pre(ctx, mod, stmts, notes0) do
    Enum.reduce(stmts, {[], notes0, %{}}, fn s0, {subs, notes, binds} ->
      s = subst_binds(s0, binds)
      case s do
        {{:., _, [{:__aliases__, _, [:Process]}, :flag]}, _, [:trap_exit, true]} ->
          {subs, notes, binds}
        {{:., _, [{:__aliases__, _, [:Logger]}, f]}, _, args} when is_atom(f) and is_list(args) ->
          {subs, Enum.uniq(notes ++ ["#{mod}.init/1: Logger calls are dropped (logging is not modelled)"]), binds}
        {:__local_call__, _, [id | _]} ->
          fail("#{mod}.init/1: #{id} is called for its effect, but a local helper is a pure expression")
        {:=, _, [{v, _, nil}, rhs]} when is_atom(v) ->
          {subs, notes, Map.put(binds, v, rhs)}
        _ ->
          case pubsub_call(ctx, mod, s) do
            {f, topic, nil} when f in [:subscribe, :unsubscribe] -> {subs ++ [{f, topic}], notes, binds}
            {f, _, _} -> fail("#{mod}.init/1: #{f} is not supported in init/1")
            nil -> fail("#{mod}.init/1: unsupported statement #{Macro.to_string(s0)}")
          end
      end
    end)
  end

  defp subst_binds(ast, binds) when map_size(binds) == 0, do: ast
  defp subst_binds(ast, binds) do
    Macro.postwalk(ast, fn
      {v, _, nil} = n when is_atom(v) -> Map.get(binds, v, n)
      n -> n
    end)
  end

  # `Keyword.get(opts, :k, d)` where opts is an init/1 parameter: the option
  # list is not modelled, so the call is its literal default.
  defp init_opts(mod, params, ast) do
    out =
      Macro.prewalk(ast, fn
        {{:., _, [{:__aliases__, _, [:Keyword]}, :get]}, _, [{v, _, nil}, k, d]} = n when is_atom(v) and is_atom(k) ->
          if Atom.to_string(v) in params do
            literal?(d) ||
              fail("#{mod}.init/1: #{Macro.to_string(n)} needs a literal default " <>
                     "(the option list is not modelled, so the default is what the state gets)")
            d
          else
            n
          end
        {{:., _, [{:__aliases__, _, [:Keyword]}, :get]}, _, [{v, _, nil}, k]} = n when is_atom(v) and is_atom(k) ->
          if Atom.to_string(v) in params, do: nil, else: n
        n -> n
      end)
    {out, out != ast}
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
      nil -> state_expr(ctx, env, arg, cctor, cfields)
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
        state_expr(ctx, env, bound, cctor, cfields)
    end
  end

  # A PubSub call: {f, topic, message_ast | nil} for `Mod.f(server, topic[, m])`
  # where Mod is one of ctx.pubsub (or `:ok = Mod.f(...)`); nil otherwise.
  # The topic is resolved to a string literal here (`topic_str`).
  defp pubsub_call(ctx, mod, {:=, _, [:ok, call]}), do: pubsub_call(ctx, mod, call)
  defp pubsub_call(ctx, mod, {{:., _, [{:__aliases__, _, segs}, f]}, _, args}) do
    if segs in ctx.pubsub do
      case {f, args} do
        {:subscribe, [_server, topic]} -> {:subscribe, topic_str(ctx, mod, topic), nil}
        {:unsubscribe, [_server, topic]} -> {:unsubscribe, topic_str(ctx, mod, topic), nil}
        {f, [_server, topic, m]} when f in [:broadcast, :broadcast!] -> {:broadcast, topic_str(ctx, mod, topic), m}
        _ -> fail("#{mod}: unsupported PubSub call #{Enum.join(segs, ".")}.#{f}/#{length(args)} (subscribe/2, unsubscribe/2, broadcast/3)")
      end
    end
  end
  defp pubsub_call(_ctx, _mod, _), do: nil

  # a topic: a string literal, or a module attribute bound to one, as a Lean string literal
  defp topic_str(_ctx, _mod, t) when is_binary(t), do: inspect(t)
  defp topic_str(ctx, mod, {:@, _, [{name, _, nil}]} = a) when is_atom(name) do
    case Map.fetch(ctx.attrs, {mod, name}) do
      {:ok, t} when is_binary(t) -> inspect(t)
      _ -> fail("#{mod}: PubSub topic #{Macro.to_string(a)} is not a module attribute bound to a string literal")
    end
  end
  defp topic_str(_ctx, mod, t), do: fail("#{mod}: PubSub topic #{Macro.to_string(t)} must be a string literal or a module attribute bound to one")

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

  # ---------- desugaring ----------

  # Purely syntactic rewrites of the whole module body, done once before
  # anything else looks at it, so nothing downstream ever sees a `|>`, a
  # `cond` or an `unless`:
  #
  #   a |> f(b)               ->  f(a, b)
  #   cond do c -> b; .. end  ->  nested `if`s (the last clause must be `true`)
  #   unless c, do: a         ->  if c, do: nil, else: a
  #
  # Chains fold left to right: `Macro.prewalk` rewrites the outermost pipe
  # first and then descends into the result.
  # ---------- LiveView assigns ----------

  # A LiveView socket is a struct with an `assigns` map, and Phoenix's
  # imported `assign/2,3` is a functional update of it: `assign(s, :k, v)` is
  # `put_in(s.assigns[:k], v)` and `s.assigns.k` is the fetch. Nothing else
  # about LiveView is modelled -- not the lifecycle, not the rendering, not
  # the diff -- so a socket here is exactly the record the state machinery
  # already has: `assign(s, :k, v)` is rewritten to the map update
  # `%{s | k: v}` and `s.assigns.k` to the field read `s.k`, and the state of
  # such a module is inferred as a record over the keys its callbacks touch,
  # the way a map-patterned state already is. The assigns a callback never
  # reads or writes are not in the model, which is the same abstraction the
  # record state makes of any map.
  #
  # The rewrite is skipped for a module that defines `assign` itself (then it
  # is that module's function, not Phoenix's), and it only fires for a
  # literal atom key on a variable socket: anything else stays as it was and
  # is reported as the unsupported call it is.
  defp rewrite_assigns(body) do
    if defines?(body, :assign), do: body, else: Macro.prewalk(body, &assign_node/1)
  end

  # `s.assigns.k` -> `s.k`
  defp assign_node({{:., m, [{{:., _, [{v, _, nil} = s, :assigns]}, _, []}, k]}, _, []})
       when is_atom(v) and is_atom(k),
       do: {{:., m, [s, k]}, [no_parens: true] ++ m, []}

  # `assign(s, :k, e)` -> `%{s | k: e}`
  defp assign_node({:assign, m, [{v, _, nil} = s, k, e]}) when is_atom(v) and is_atom(k) and k not in [nil, true, false],
    do: {:%{}, m, [{:|, m, [s, [{k, e}]]}]}

  # `assign(s, k: e, ..)` and `assign(s, %{k: e, ..})` -> `%{s | k: e, ..}`
  defp assign_node({:assign, m, [{v, _, nil} = s, kvs]}) when is_atom(v) and is_list(kvs),
    do: if(assign_keys?(kvs), do: {:%{}, m, [{:|, m, [s, kvs]}]}, else: {:assign, m, [s, kvs]})

  defp assign_node({:assign, m, [{v, _, nil} = s, {:%{}, _, kvs}]} = n) when is_atom(v) and is_list(kvs),
    do: if(assign_keys?(kvs), do: {:%{}, m, [{:|, m, [s, kvs]}]}, else: n)

  defp assign_node(n), do: n

  defp assign_keys?(kvs),
    do: Keyword.keyword?(kvs) and kvs != [] and Enum.all?(kvs, fn {k, _} -> atom_key?(k) end)

  # does this module body define a function of that name (any arity)?
  defp defines?(body, name) do
    {_, found} =
      Macro.prewalk({:__block__, [], body}, false, fn
        {d, _, [{^name, _, args} | _]} = n, _ when d in [:def, :defp] and is_list(args) -> {n, true}
        {d, _, [{:when, _, [{^name, _, args} | _]} | _]} = n, _ when d in [:def, :defp] and is_list(args) -> {n, true}
        n, acc -> {n, acc}
      end)

    found
  end

  defp desugar(ast) do
    Macro.prewalk(ast, fn
      {:|>, _, [l, r]} -> pipe_into(l, r)
      {:cond, _, [[do: arms]]} -> cond_to_if(arms)
      {:unless, m, [c, blocks]} when is_list(blocks) ->
        {:if, m, [c, [do: Keyword.get(blocks, :else), else: Keyword.get(blocks, :do)]]}
      n -> n
    end)
  end

  # `cond` is nested `if`s. Its last clause must be an unconditional
  # `true ->`: a `cond` that falls off the end raises CondClauseError, and an
  # expression in the model cannot raise.
  defp cond_to_if([{:->, _, [[c], b]}]) do
    c in [true, :otherwise] || fail("the last clause of a `cond` must be `true ->`, got #{Macro.to_string(c)}")
    b
  end
  defp cond_to_if([{:->, m, [[c], b]} | rest]), do: {:if, m, [c, [do: b, else: cond_to_if(rest)]]}
  defp cond_to_if(arms), do: fail("unsupported `cond` clauses #{Macro.to_string(arms)}")

  @unpipeable [:fn, :__block__, :__aliases__, :%{}, :%, :{}, :<<>>, :&, :^, :when, :"::"]
  defp pipe_into(l, {f, _, _} = r) when f in @unpipeable,
    do: fail("cannot pipe #{Macro.to_string(l)} into #{Macro.to_string(r)}")
  defp pipe_into(l, {f, m, args}) when is_list(args), do: {f, m, [l | args]}
  defp pipe_into(l, {f, m, nil}) when is_atom(f), do: {f, m, [l]}
  defp pipe_into(l, r), do: fail("cannot pipe #{Macro.to_string(l)} into #{Macro.to_string(r)}")

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
      # a string-valued module attribute (a PubSub topic)
      {:@, _, [{name, _, [v]}]}, c when is_atom(name) and is_binary(v) ->
        put_in(c.attrs[{mod, name}], v)
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
                    # a binary default is a String, a `:queue.new()` the
                    # empty queue (the list, oldest first)
                    is_binary(d) -> "String"
                    match?({{:., _, [:queue, :new]}, _, []}, d) -> "List Term"
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
      st = Map.get(c.types, {mod, :state}) || fail("#{mod} declares no @type state and has no init/1 to infer it from")
      # hidden trailing fields: the after-timer generation, the ETS counter
      hidden = if(after?, do: [{"gen", "Nat"}], else: []) ++ if(ets_new?(body), do: [{"ets", "Nat"}], else: [])
      {fields, c} = state_fields(c, mod, st)
      %{c | st_ctors: c.st_ctors ++ [{ctor_name(mod), fields ++ hidden}]}
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
  # record type `%{k: T, ..}` (a map with atom keys) gets the keys as named
  # fields and the module is remembered as record-shaped; a state that is a
  # struct (the module's own `t()` or `%__MODULE__{}`, or another module's)
  # is flattened into one field per struct field, in defstruct order and
  # under the struct's field names.
  defp state_fields(ctx, mod, {:{}, _, ts}), do: {ts |> Enum.with_index() |> Enum.map(fn {t, i} -> {"f#{i}", lean_type(ctx, mod, t)} end), ctx}
  defp state_fields(ctx, mod, {a, b}), do: state_fields(ctx, mod, {:{}, [], [a, b]})
  defp state_fields(ctx, mod, {:%{}, _, pairs}) when pairs != [] and is_list(pairs) do
    if Keyword.keyword?(pairs) do
      fields = for {k, t} <- pairs, do: {lean_ident(Atom.to_string(k)), lean_type(ctx, mod, t)}
      {fields, %{ctx | records: Map.put(ctx.records, mod, Enum.map(pairs, &elem(&1, 0)))}}
    else
      {[{"s", lean_type(ctx, mod, {:%{}, [], pairs})}], ctx}
    end
  end
  defp state_fields(ctx, mod, t) do
    lt = lean_type(ctx, mod, t)
    case Map.get(ctx.structs, lt) do
      nil -> {[{"s", lt}], ctx}
      fields -> {Enum.map(fields, fn {f, ft, _} -> {f, ft} end), %{ctx | struct_states: Map.put(ctx.struct_states, ctor_name(mod), lt)}}
    end
  end

  # Elixir type AST -> Lean type (string)
  # a Lean type the translator computed itself, not one the source wrote:
  # the probed reply type of untyped mode (see `reply_probe`)
  defp lean_type(_ctx, _mod, {:__lean__, _, [t]}) when is_binary(t), do: t
  defp lean_type(_ctx, _mod, {:pid, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:GenServer]}, :from]}, _, []}), do: "Pid"
  defp lean_type(_ctx, _mod, {:integer, _, []}), do: "Int"
  defp lean_type(_ctx, _mod, {:non_neg_integer, _, []}), do: "Nat"
  defp lean_type(_ctx, _mod, {:boolean, _, []}), do: "Bool"
  # a struct type: the module's own `%__MODULE__{}`, or `%Mod{}` (the fields
  # in the type, if any, are checked by collect_structs for `@type t`)
  defp lean_type(ctx, mod, {:%, _, [{:__MODULE__, _, _}, {:%{}, _, _}]}), do: struct_type(ctx, mod)
  defp lean_type(ctx, _mod, {:%, _, [{:__aliases__, _, [m]}, {:%{}, _, _}]}), do: struct_type(ctx, m)
  # ---- the value types of the @remote families (Leanactors/Str.lean,
  # Leanactors/Time.lean, Leanactors/SetList.lean, and the per-file `Atom`
  # and `Module` inductives). These names win over a module of the same
  # name declared in the file.
  defp lean_type(_ctx, _mod, {t, _, []}) when t in [:binary, :bitstring, :iodata, :iolist], do: "String"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:String]}, :t]}, _, []}), do: "String"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [m]}, :t]}, _, []})
       when m in [:DateTime, :NaiveDateTime, :Date, :Time], do: "Instant"
  defp lean_type(_ctx, _mod, {:atom, _, []}), do: "Atom"
  defp lean_type(_ctx, _mod, {:module, _, []}), do: "Module"
  defp lean_type(_ctx, _mod, {:keyword, _, []}), do: "List (Atom × Term)"
  defp lean_type(ctx, mod, {:keyword, _, [t]}), do: "List (Atom × #{lean_type(ctx, mod, t)})"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:Keyword]}, :t]}, _, []}), do: "List (Atom × Term)"
  defp lean_type(ctx, mod, {{:., _, [{:__aliases__, _, [:Keyword]}, :t]}, _, [t]}),
    do: "List (Atom × #{lean_type(ctx, mod, t)})"
  defp lean_type(_ctx, _mod, {{:., _, [{:__aliases__, _, [:MapSet]}, :t]}, _, []}), do: "List Term"
  defp lean_type(ctx, mod, {{:., _, [{:__aliases__, _, [:MapSet]}, :t]}, _, [t]}),
    do: "List " <> paren(lean_type(ctx, mod, t))
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
  # an opaque term (Leanactors/Term.lean): what untyped mode gives every
  # field, and what an ETS reference is
  defp lean_type(_ctx, _mod, {t, _, []}) when t in [:term, :any, :reference], do: "Term"
  defp lean_type(ctx, mod, a) when is_atom(a) and a not in [nil, true, false], do: enum_name(ctx, mod, [a])
  defp lean_type(ctx, mod, [t]), do: "List " <> paren(lean_type(ctx, mod, t))
  # a map %{K => V} is an association list; see Leanactors/AssocList.lean
  defp lean_type(ctx, mod, {:%{}, _, [{k, v}]}) when not is_atom(k),
    do: "List (" <> lean_type(ctx, mod, k) <> " × " <> lean_type(ctx, mod, v) <> ")"
  defp lean_type(_ctx, _mod, {:%{}, _, pairs} = t) when is_list(pairs) and pairs != [] do
    if Keyword.keyword?(pairs),
      do: fail("a record type `%{k: T, ..}` is only supported as the whole @type state: #{Macro.to_string(t)}"),
      else: fail("a map type needs exactly one `K => V` pair: #{Macro.to_string(t)}")
  end
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

  # The Lean constructor of a tagged union for a tag at an arity:
  # {name, field types}. A tag that occurs at two arities (an inferred reply
  # union with both `:ok` and `{:ok, ref}`) names its tuple forms with the
  # arity appended (`ok`, `ok1`); an atom keeps the bare tag.
  defp union_ctor(ctors, tag, arity) do
    case Enum.find(ctors, fn {t, ts} -> t == tag and length(ts) == arity end) do
      nil -> nil
      {_, ts} -> {union_ctor_name(ctors, tag, arity), ts}
    end
  end

  defp union_ctor_name(ctors, tag, arity) do
    if arity > 0 and Enum.count(ctors, fn {t, _} -> t == tag end) > 1,
      do: "#{tag}#{arity}",
      else: Atom.to_string(tag)
  end

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
  # `Cache` -> `cache`, `TableRegistry` -> `table_registry`
  defp ctor_name(mod), do: mod |> Atom.to_string() |> Macro.underscore()

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

  # Lean has no forward references, so every declaration is emitted after the
  # ones its field types mention; within one batch the source order is kept.
  # A cycle would need a `mutual` block, which the model does not use.
  defp order_decls(decls) do
    names = Enum.map(decls, &elem(&1, 0))
    order_loop(for({n, ts, txt} <- decls, do: {n, decl_deps(ts, names) -- [n], txt}), [], [])
  end

  defp order_loop([], _done, acc), do: Enum.reverse(acc)
  defp order_loop(pending, done, acc) do
    case Enum.split_with(pending, fn {_n, deps, _} -> deps -- done == [] end) do
      {[], [{n, _, _} | _]} ->
        fail("#{n} and the types its fields mention are mutually recursive; Lean would need a `mutual` block")
      {ready, rest} ->
        order_loop(rest, done ++ Enum.map(ready, &elem(&1, 0)),
                   Enum.reverse(Enum.map(ready, &elem(&1, 2))) ++ acc)
    end
  end

  # the declared type names a list of Lean types mentions
  defp decl_deps(types, names),
    do: for(n <- names, Enum.any?(types, &Regex.match?(~r/\b#{n}\b/, &1)), do: n)

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
        {name, Enum.flat_map(ctors, &elem(&1, 1)),
         "inductive #{name}\n" <>
           Enum.map_join(ctors, "\n", fn {tag, ts} ->
             String.trim_trailing("  | #{union_ctor_name(ctors, tag, length(ts))} " <> (ts |> Enum.with_index() |> Enum.map_join(" ", fn {t, i} -> "(a#{i} : #{t})" end)))
           end) <> "\n  deriving Repr, DecidableEq\n"}
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
        {name, Enum.map(ctx.structs[name], &elem(&1, 1)),
         "structure #{name} where\n" <>
           Enum.map_join(ctx.structs[name], "\n", fn {f, t, d} -> "  #{f} : #{t} := #{expr(%{}, d, t)}" end) <>
           "\n  deriving Repr, DecidableEq\n"}
      end
    enums = enums ++ order_decls(unions ++ structs)

    # a map anywhere in the types needs the association-list helpers
    all_types = base_types ++ Enum.flat_map(used_structs, fn n -> Enum.map(ctx.structs[n], &elem(&1, 1)) end)
    maps_import = if Enum.any?(all_types, &String.contains?(&1, " × ")), do: "import Leanactors.AssocList\n", else: ""
    # an opaque field needs Leanactors/Term.lean
    term_import = if Enum.any?(all_types, &(&1 =~ ~r/\bTerm\b/)), do: "import Leanactors.Term\n", else: ""

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


    # public functions that are not callbacks: noted, not translated
    ignored_note =
      if ctx.ignored == [],
        do: "",
        else: "-- Not translated (public API, not a callback): " <> Enum.join(ctx.ignored, ", ") <> "\n"

    # A LiveView's `handle_event` is not a message the mailbox carries, so it
    # is not a clause of `beh` -- but unlike a public API wrapper it IS a
    # transition the running process makes, driven by the browser channel.
    # Say so in the file: a property proved of this model is a property of
    # the module's message handling only.
    events_note =
      if ctx.events == [],
        do: "",
        else: "-- Not translated (a LiveView browser event is not a message, but it IS a " <>
              "transition of the real process, which this model does not carry): " <>
              Enum.join(ctx.events, ", ") <> "\n"

    # The per-file `Atom` and `Module` inductives are built from what the
    # rendering used, so they can only be emitted now, and the helper files
    # the rendering reached for are found the same way (a String, a SetList
    # or an Instant can appear in a clause without appearing in any type).
    enums = value_decls(all_types) ++ enums
    rendered = Enum.join(enums, "\n") <> msg <> st <> beh
    imp = fn text, line -> if String.contains?(rendered, text), do: line, else: "" end
    str_import = imp.("Str.toStr", "import Leanactors.Str\n")
    set_import = imp.("SetList.", "import Leanactors.SetList\n")
    time_import = if rendered =~ ~r/\bInstant\b/, do: "import Leanactors.Time\n", else: ""
    maps_import = if maps_import == "", do: imp.("AssocList.", "import Leanactors.AssocList\n"), else: maps_import
    term_import = if term_import == "" and rendered =~ ~r/\bTerm\b/, do: "import Leanactors.Term\n", else: term_import

    """
    -- GENERATED by elixir/to_lean.exs. Do not edit.
    #{ignored_note}#{events_note}import Leanactors.Sys
    #{maps_import}#{term_import}#{str_import}#{set_import}#{time_import}
    namespace #{ctx.ns}

    open Leanactors

    #{Enum.join(enums, "\n")}
    #{msg}
    #{st}
    #{pids}
    #{ctx.local_decls}#{sig}#{beh}
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
  defp default_of(_ctx, "Term"), do: "(Term.mk 0)"
  defp default_of(_ctx, "String"), do: "\"\""
  defp default_of(_ctx, "Instant"), do: "Instant.now"
  defp default_of(_ctx, "Atom"), do: "." <> (List.first(Process.get(:to_lean_atoms, [])) || fail("no Atom value for the exitMsg placeholder"))
  defp default_of(_ctx, "Module"), do: "." <> (List.first(Process.get(:to_lean_mods, [])) || fail("no Module value for the exitMsg placeholder"))
  defp default_of(_ctx, "List " <> _), do: "[]"
  defp default_of(_ctx, "Option " <> _), do: "none"
  defp default_of(ctx, t) do
    case Enum.find(ctx.types, fn {{_, n}, _} -> n |> Atom.to_string() |> String.capitalize() == t end) do
      {_, u} ->
        case tuple_tag(List.first(union(u))) do
          {tag, []} -> ".#{tag}"
          {tag, args} ->
            {name, ts} = union_ctor(union_ctors(t), tag, length(args))
            "(.#{name} " <> Enum.map_join(ts, " ", &paren_or(default_of(ctx, &1))) <> ")"
        end
      nil -> fail("no default value of type #{t} for the exitMsg placeholder")
    end
  end

  # A whole-state part the clause's right-hand side never mentions (a struct
  # state whose every field is replaced, say) would trip Lean's unused
  # variable linter, so it is renamed `_part` in the state pattern.
  defp hide_unused_parts(env, sp, rhs) do
    parts =
      (for {k, v} <- env, is_binary(k), String.starts_with?(k, "__whole__"), is_list(v), p <- v,
           plain?(p), do: p) ++
        # and any other pattern variable of the state the right-hand side
        # does not mention: a clause whose only use of it was a statement the
        # model drops (a Logger call) would trip the linter just as much
        (for {k, _} <- env, is_binary(k), not String.starts_with?(k, "__whole__"), plain?(k), do: k)
    Enum.reduce(Enum.uniq(parts), sp, fn p, acc ->
      if String.starts_with?(p, "_") or Regex.match?(~r/\b#{p}\b/, rhs),
        do: acc,
        else: Regex.replace(~r/\b#{p}\b/, acc, "_" <> p)
    end)
  end

  defp render_clauses(ctx, clauses) do
    indexed = Enum.with_index(clauses)
    # A clause subsumed by an earlier clause of the same module is unreachable
    # (Elixir warns "this clause cannot match"; with a guard we already inlined it).
    # Across kinds it is not unreachable on the BEAM (separate callbacks) but
    # would be in the single Lean match, so that is an error.
    indexed = Enum.reject(indexed, fn {cl, j} ->
      Enum.any?(indexed, fn {e, i} ->
        sub = i < j and e.mod == cl.mod and general?(e.mpat, cl.mpat) and spat_general?(cl.mod, e.spat, cl.spat)
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
        if cl.guard == nil and bare?(cl.mpat) and spat_bare?(cl.mod, cl.spat),
          do: %{c | covered: [ctor_name(cl.mod) | c.covered]},
          else: c
      # a deferring fallback re-enqueues the whole message: name the pattern
      {me, mp} = if deferred, do: {"me", "#{msg_name(env)}@(#{mp})"}, else: {self_name(env), mp}
      sp = hide_unused_parts(env, sp, rhs)
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
  # the state fields and message arguments. The sentinel `:__every__` (a
  # name no Elixir atom tag can be, unlike the `:all` this once used, which
  # a module with a `:all` message collided with) says the bare-message
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
    if bare != [] and exhaustive?(ctx, bare, ftypes), do: [:__every__ | tags], else: tags
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
      {_, ctors} -> for {tag, ts} <- ctors, do: {{:ctor, union_ctor_name(ctors, tag, length(ts))}, ts}
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
        if :__every__ in covered do
          []
        else
          for {tag, _} <- c.msg_ctors,
              Map.get(c.kinds, {mod, tag}) in [:handle_cast, :handle_call],
              tag not in covered,
              do: tag
        end
      crash = Enum.map(needed, &crash_clause(c, mod, &1))
      info = live_info(c, mod, ci, needed, info)
      chunk = ci ++ info
      # Every tag is covered (or gets a crash clause): the module's arms are
      # exhaustive, so a trailing defer clause or the global catch-all would
      # be a redundant alternative, which Lean rejects.
      total = covered_tags(c, mod, chunk)
      exhaustive = :__every__ in total or Enum.all?(c.msg_ctors, fn {tag, _} -> tag in total or tag in needed end)
      c = if exhaustive, do: %{c | covered: [ctor_name(mod) | c.covered]}, else: c
      defer = if mod in c.defers and not exhaustive, do: [defer_clause(c, mod)], else: []
      strs = fn xs -> Enum.map(xs, &elem(&1, 2)) end
      {strs.(ci) ++ crash ++ strs.(info) ++ defer, c}
    end)
    |> then(fn {groups, c} -> {List.flatten(groups), c} end)
  end

  # The handle_info clauses that can still be reached. A source catch-all
  # `def handle_info(_msg, state), do: {:noreply, state}` is dead when the
  # clauses before it -- the module's own, plus the crash clauses inserted
  # for the cast/call tags they miss -- already match every Msg constructor:
  # on the BEAM nothing would reach it, and Lean rejects the alternative as
  # redundant. Dropping it changes no behaviour, and it is the shape a
  # LiveView writes (one real `handle_info` and a catch-all for the rest).
  defp live_info(ctx, mod, ci, needed, info) do
    {kept, _} =
      Enum.flat_map_reduce(info, ci, fn {cl, _, _} = row, prev ->
        cov = covered_tags(ctx, mod, prev)

        dead? =
          cl.guard == nil and bare?(cl.mpat) and spat_bare?(mod, cl.spat) and
            (:__every__ in cov or
               Enum.all?(ctx.msg_ctors, fn {tag, _} -> tag in cov or tag in needed end))

        {if(dead?, do: [], else: [row]), prev ++ [row]}
      end)

    kept
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
    sp = state_str(ctor, parts ++ hidden_fields(ctx, mod))
    sp2 = state_str(ctor, parts) <> hidden_next(ctx, mod, %{})
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

  # The hidden trailing state fields of a module, in order: the after-timer
  # generation `gen` of a loop with `after`, the ETS counter `ets` of a
  # module that calls `:ets.new`. Source patterns and expressions never see
  # them; `patterns` binds them by name, every continuing state appends
  # them (`hidden_next`), a spawn starts them at 0 (`spawn_hidden`).
  defp hidden_fields(ctx, mod),
    do: if(Map.has_key?(ctx.afters, mod), do: ["gen"], else: []) ++ if(mod in ctx.ets, do: ["ets"], else: [])

  # the state fields a source pattern or expression sees
  defp visible_fields(ctx, mod, fields), do: Enum.drop(fields, -length(hidden_fields(ctx, mod)))

  # the hidden fields of a continuing state: the generation bumped, the ETS
  # counter advanced by the tables the body created (`sends` counts them)
  defp hidden_next(ctx, mod, env) do
    Enum.map_join(hidden_fields(ctx, mod), "", fn
      "gen" -> " (gen + 1)"
      "ets" ->
        case Map.get(env, :__ets__, 0) do
          0 -> " ets"
          k -> " (ets + #{k})"
        end
    end)
  end
  defp spawn_hidden(ctx, mod), do: Enum.map_join(hidden_fields(ctx, mod), "", fn _ -> " 0" end)

  defp state_str(ctor, []), do: ".#{ctor}"
  defp state_str(ctor, parts), do: ".#{ctor} " <> Enum.join(parts, " ")

  # the clause's state pattern re-entered: the visible parts unchanged, gen bumped
  defp reenter_state(ctx, mod, env) do
    {ctor, _} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    state_str(ctor, env[:__vparts__]) <> hidden_next(ctx, mod, env)
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
      # a PubSub subscribe/unsubscribe is on behalf of `me`
      {{:., _, [{:__aliases__, _, segs}, f]}, _, [_, _]} = n, _ when f in [:subscribe, :unsubscribe] and is_list(segs) -> {n, true}
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
    case Enum.find(later, fn {c, _} -> general?(c.mpat, cl.mpat) and spat_general?(cl.mod, c.spat, cl.spat) end) do
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
        env2 =
          if Map.has_key?(ctx.records, cl.mod),
            do: record_alias(ctx, cl.mod, c.spat, env, env2),
            else: whole_alias(c.spat, state_str(ctor, env[:__vparts__]), visible_fields(ctx, cl.mod, fields), env2)
        env2 = if c.from, do: Map.put(env2, {:alias, from_var(c.from)}, env[:__from__]), else: env2
        env2 = if uses_self?(c), do: Map.put(env2, :__self__, true), else: env2
        {b, ctx} = body(ctx, c.mod, env2, c.body)
        if c.guard, do: fail("chained guards are not supported (clause #{i})")
        {b, ctx, false}
    end
  end

  # A state pattern of a record-shaped module is a real Lean pattern, one
  # part per field, not a variable plus guards, so `bare?`/`general?` must
  # look at the field patterns. `record_parts` is the pattern as that list
  # (`nil` for a module whose state is not a record).
  defp record_parts(mod, p) do
    keys = Map.get(Process.get(:to_lean_records, %{}), mod)
    pairs =
      case p do
        {:%{}, _, ps} when is_list(ps) -> ps
        {:=, _, [{:%{}, _, ps}, {v, _, nil}]} when is_atom(v) and is_list(ps) -> ps
        {v, _, nil} when is_atom(v) -> []
        _ -> nil
      end
    if keys == nil or pairs == nil,
      do: nil,
      else: for(k <- keys, do: (case List.keyfind(pairs, k, 0) do
              {_, x} -> x
              nil -> {:_, [], nil}
            end))
  end

  defp spat_bare?(mod, p) do
    case record_parts(mod, p) do
      nil -> bare?(p)
      parts -> Enum.all?(parts, &bare?/1)
    end
  end

  defp spat_general?(mod, a, b) do
    case {record_parts(mod, a), record_parts(mod, b)} do
      {pa, pb} when pa != nil and pb != nil ->
        Enum.zip(pa, pb) |> Enum.all?(fn {x, y} -> general?(x, y) end)
      _ -> general?(a, b)
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

  # The later clause's record state pattern bound to the current clause's
  # parts (a guarded clause keeps every field named): a whole variable gets
  # the parts field by field, a map pattern's variables the parts of their
  # fields
  defp record_alias(ctx, mod, spat, env, env2) do
    keys = Map.fetch!(ctx.records, mod)
    {_, fields} = List.keyfind(ctx.st_ctors, ctor_name(mod), 0)
    types = visible_fields(ctx, mod, fields) |> Enum.map(&elem(&1, 1))
    parts = env[:__vparts__]
    whole = fn e, v ->
      name = lean_ident(Atom.to_string(v))
      e = Enum.zip([keys, parts, types]) |> Enum.reduce(e, fn {k, part, t}, e -> e |> Map.put({:field, name, k}, part) |> Map.put(part, t) end)
      e |> Map.put("__whole__" <> name, parts) |> Map.put({:record, name}, keys)
    end
    sub = fn e, pairs ->
      Enum.reduce(pairs, e, fn
        {k, {v, _, nil}}, e when is_atom(v) ->
          name = Atom.to_string(v)
          i = Enum.find_index(keys, &(&1 == k)) || fail("#{mod}: #{k} is not a field of the state")
          if String.starts_with?(name, "_"), do: e, else: e |> Map.put({:alias, name}, Enum.at(parts, i)) |> Map.put(lean_ident(name), Enum.at(types, i))
        {_, other}, _ -> fail("#{mod}: cannot alias the fallthrough pattern #{Macro.to_string(other)}")
      end)
    end
    case spat do
      {v, _, nil} when is_atom(v) -> if(String.starts_with?(Atom.to_string(v), "_"), do: env2, else: whole.(env2, v))
      {:=, _, [{:%{}, _, pairs}, {v, _, nil}]} when is_atom(v) -> sub.(whole.(env2, v), pairs)
      {:%{}, _, pairs} -> sub.(env2, pairs)
      _ -> env2
    end
  end

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
    {vparts, env, gs} =
      if Map.has_key?(ctx.records, cl.mod) do
        record_pats(ctx, cl, vfields, env, gs)
      else
        # a struct state pattern `%__MODULE__{f: p} = v`: the whole variable
        # names all the parts, the named fields included
        struct = Map.get(ctx.struct_states, ctor_name(cl.mod))
        {sub, whole} = state_subpats(cl.spat, length(vfields), struct, vfields)
        {vparts, env, gs} = pat_list(ctx, sub, Enum.map(vfields, &elem(&1, 1)), env, gs)
        env = if whole, do: Map.put(env, "__whole__" <> whole, vparts), else: env
        env = if struct, do: Map.put(env, :__struct_state__, struct), else: env
        {vparts, env, gs}
      end
    # the hidden fields are the pattern variables `gen` and `ets`
    {sparts, env} =
      Enum.reduce(hidden_fields(ctx, cl.mod), {vparts, env}, fn h, {parts, env} ->
        if Map.has_key?(env, h), do: fail("#{cl.mod}: `#{h}` is reserved for the hidden #{if(h == "gen", do: "after-timer generation", else: "ETS counter")} field")
        {parts ++ [h], Map.put(env, h, "Nat")}
      end)
    sp = state_str(ctor, sparts)
    env = env |> Map.put(:__mp__, mp) |> Map.put(:__sparts__, sparts) |> Map.put(:__vparts__, vparts)
    {env, mp, sp, gs}
  end

  # The state pattern of a record-shaped module (`%{k: T, ..}`), one Lean
  # part per field. A whole-state variable `s` binds every field by its own
  # name (`s_<field>` when the name is taken), and `s.f`, `%{s | f: e}` and a
  # bare `s` in the body read those parts (`expr`, `state_expr`); a field the
  # body never reads is the wildcard `_`. A map pattern `%{f: p, ..}`,
  # optionally `= s`, binds the mentioned fields to their sub-patterns (typed
  # by the field) and the others as the whole variable would, or `_`.
  defp record_pats(ctx, cl, vfields, env, gs) do
    fnames = Enum.map(vfields, &elem(&1, 0))
    keys = Map.fetch!(ctx.records, cl.mod)
    {whole, pairs} =
      case cl.spat do
        {:_, _, nil} -> {nil, []}
        {v, _, nil} when is_atom(v) -> {v, []}
        {:=, _, [{:%{}, _, pairs}, {v, _, nil}]} when is_atom(v) -> {v, pairs}
        {:%{}, _, pairs} -> {nil, pairs}
        p -> fail("#{cl.mod}: state pattern #{Macro.to_string(p)} does not fit the record state %{#{Enum.join(keys, ", ")}}")
      end
    Enum.each(pairs, fn {k, _} -> k in keys || fail("#{cl.mod}: #{k} is not a field of the state (#{Enum.join(keys, ", ")})") end)
    whole_name = whole && lean_ident(Atom.to_string(whole))
    # a whole variable needs the fields the body reads through it; a guard,
    # a map-pattern fallthrough or an exit/raise (they rebuild the state)
    # keep every field
    used =
      cond do
        whole == nil -> []
        cl.guard != nil or env[:__mapbinds__] != nil or needs_state?(cl.body) -> :all
        String.starts_with?(Atom.to_string(whole), "_") -> []
        true -> used_fields(record_uses([cl.body], whole), keys)
      end
    {parts, {env, gs}} =
      Enum.zip([keys, vfields]) |> Enum.map_reduce({env, gs}, fn {k, {fname, t}}, {e, g} ->
        case List.keyfind(pairs, k, 0) do
          {_, sub} ->
            {ps, e, g} = pat(ctx, sub, t, e, g)
            {ps, {e, g}}
          nil ->
            if used == :all or k in used do
              name = if(Map.has_key?(e, fname), do: "#{whole_name}_#{fname}", else: fname)
              {name, {Map.put(e, name, t), g}}
            else
              {"_", {e, g}}
            end
        end
      end)
    env =
      if whole do
        parts_by_key = Enum.zip(keys, parts)
        env = Enum.reduce(parts_by_key, env, fn {k, part}, e -> if(part == "_", do: e, else: Map.put(e, {:field, whole_name, k}, part)) end)
        env |> Map.put("__whole__" <> whole_name, parts) |> Map.put({:record, whole_name}, keys)
      else
        env
      end
    _ = fnames
    {parts, env, gs}
  end

  # how a body uses the whole-state variable `v` of a record: `v.f` reads
  # field f, `%{v | f: e, ..}` reads every field but those, a bare `v`
  # reads all
  defp record_uses({{:., _, [{v, _, nil}, f]}, _, []}, v) when is_atom(f), do: [f]
  defp record_uses({:%{}, _, [{:|, _, [{v, _, nil}, ups]}]}, v) when is_list(ups),
    do: [{:all_but, Keyword.keys(ups)} | Enum.flat_map(ups, fn {_, e} -> record_uses(e, v) end)]
  defp record_uses({v, _, nil}, v), do: [:all]
  defp record_uses({f, _, args}, v) when is_list(args), do: record_uses(f, v) ++ Enum.flat_map(args, &record_uses(&1, v))
  defp record_uses({a, b}, v), do: record_uses(a, v) ++ record_uses(b, v)
  defp record_uses(l, v) when is_list(l), do: Enum.flat_map(l, &record_uses(&1, v))
  defp record_uses(_, _), do: []

  defp used_fields(uses, keys) do
    if :all in uses do
      :all
    else
      Enum.flat_map(uses, fn
        {:all_but, ks} -> keys -- ks
        f -> [f]
      end) |> Enum.uniq()
    end
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
  defp pat(_ctx, s, t, env, gs) when is_binary(s) do
    t in [nil, "String"] || fail("string pattern #{inspect(s)} at non-string position #{t}")
    {str_lit(s), env, gs}
  end
  defp pat(_ctx, a, t, env, gs) when is_atom(a) and a not in [nil, true, false] do
    cond do
      t == "Atom" -> {atom_ctor(a), env, gs}
      enum_type?(t) -> {".#{a}", env, gs}
      true -> fail("atom #{a} at non-enum position #{t}")
    end
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
        {name, ts} = union_ctor(union_ctors(t), tag, length(args)) || fail("#{tag}/#{length(args)} is not an alternative of #{t}")
        {parts, env, gs} = pat_list(ctx, args, ts, env, gs)
        {"(.#{name}" <> Enum.map_join(parts, "", &(" " <> &1)) <> ")", env, gs}
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
  defp enum_type?(t), do: t =~ ~r/^[A-Z][a-z]*$/ and t not in ["Pid", "Int", "Nat", "Bool", "Reason", "Term", "String"]

  defp guard_to_lean(_env, {:eq, a, b}), do: "#{a} = #{b}"
  defp guard_to_lean(_env, {:map_has, m, k}), do: "AssocList.hasKey #{m} #{paren_or(k)}"
  defp guard_to_lean(_env, {:map_eq, m, k, v}), do: "AssocList.get? #{m} #{paren_or(k)} = some #{paren_or(v)}"
  defp guard_to_lean(env, g), do: expr(env, g, nil)

  # ---------- the pure expression compiler ----------
  #
  # An expression of the pure fragment may itself be a control form. Each is
  # compiled at the expected type, so `some`/`none` insertion and the
  # type-directed pattern machinery work inside a branch exactly as they do at
  # body level:
  #
  #   if c, do: a, else: b     ->  (if c then a else b)
  #   if c, do: a              ->  (if c then some a else none): an `if` with
  #                                no `else` is nil, so only at an Option type
  #   case e do p -> b; .. end ->  (match e with | p => b | ..), the arms using
  #                                the same `pat` as a clause head
  #   (a; b; c)                ->  nested `let`s, the last statement the value
  #   x = e   (in a block)     ->  let x := e
  #   {a, b} = e               ->  let (a, b) := e  (irrefutable patterns only)
  #
  # `cond` and `unless` never reach here: `desugar/1` rewrote them.
  #
  # `pat` consults only `ctx.pid_vars`, the clause-head narrowing of an
  # `Option Pid` a body sends to, which does not apply to a pattern inside an
  # expression: an empty context is exactly "no narrowing".
  defp expr_ctx(), do: %Ctx{}

  defp ctl_expr(env, {:if, _, [c, blocks]}, t) when is_list(blocks), do: if_expr(env, c, blocks, t)

  defp ctl_expr(_env, {:case, _, [{{:., _, [:queue, :out]}, _, _}, _]} = e, _t),
    do: fail("`case :queue.out(q)` is only supported as a whole clause body, not inside an expression: #{Macro.to_string(e)}")
  defp ctl_expr(_env, {:case, _, [{{:., _, [{:__aliases__, _, [:Map]}, :pop]}, _, _}, _]} = e, _t),
    do: fail("`case Map.pop(m, k)` is only supported as a whole clause body, not inside an expression: #{Macro.to_string(e)}")
  defp ctl_expr(env, {:case, _, [scrut, [do: arms]]} = e, t) do
    st = guess_type(env, scrut)
    {arm_strs, _} =
      Enum.map_reduce(arms, false, fn
        {:->, _, [[p], b]}, saw_nil ->
          {ps, env2, gs} = case_arm_pat(expr_ctx(), p, b, st, env, saw_nil)
          gs == [] ||
            fail("a `case` arm pattern that needs a guard is not supported inside an expression (there is nothing to fall through to): #{Macro.to_string(p)}")
          env2[:__mapbinds__] == env[:__mapbinds__] ||
            fail("a map pattern is not supported in a `case` arm inside an expression (it needs a fallthrough): #{Macro.to_string(p)}")
          {"| #{ps} => #{expr(env2, b, t)}", saw_nil or p == nil}
        other, _ -> fail("unsupported `case` clause #{Macro.to_string(other)} in #{Macro.to_string(e)}")
      end)
    "(match #{expr(env, scrut, nil)} with " <> Enum.join(arm_strs, " ") <> ")"
  end

  # a block `(a; b; c)` as an expression: nested `let`s, the last statement
  # the value. An empty block has no value.
  defp ctl_expr(env, {:__block__, _, [last]}, t), do: expr(env, last, t)
  defp ctl_expr(env, {:__block__, _, stmts}, t) when stmts != [] do
    {pre, [last]} = Enum.split(stmts, -1)
    {lets, env2} = Enum.map_reduce(pre, env, &block_let/2)
    "(" <> Enum.map_join(lets, "", &(&1 <> "; ")) <> expr(env2, last, t) <> ")"
  end
  defp ctl_expr(_env, {:__block__, _, []}, _t), do: fail("an empty block has no value")

  defp ctl_expr(_env, {:=, _, [lhs, rhs]}, _t),
    do: fail("a binding is only supported as a statement or inside a block: #{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}")

  defp if_expr(env, c, blocks, t) do
    a = Keyword.get(blocks, :do)
    b =
      case Keyword.fetch(blocks, :else) do
        {:ok, e} -> e
        # `if c, do: a` is nil when c is false, and nil is `none`
        :error ->
          (t != nil and String.starts_with?(t, "Option ")) ||
            fail("an `if` with no `else` is nil at #{t || "an unknown type"}, which the model has no value for; give it an `else`")
          nil
      end
    "(if #{expr(env, c, nil)} then #{expr(env, a, t)} else #{expr(env, b, t)})"
  end

  # One statement of a block expression: a binding, and nothing else. An
  # effect (a send, a spawn) is a statement of the clause body, where the
  # model can order it; inside an expression there is no order to put it in.
  defp block_let(s, env) do
    case s do
      # `{_, q} = :queue.out(q0)`: the queue without its oldest element, the
      # same rule the statement form follows (`:queue.out` of an empty queue
      # gives it back unchanged, as `tail` does). The pair it returns has no
      # type in the model, so it cannot go through `bind_pat_let`.
      {:=, _, [{{:_, _, nil}, {v, _, nil}}, {{:., _, [:queue, :out]}, _, [q]}]} when is_atom(v) ->
        qt = type_of(env, q)
        name = lean_ident(Atom.to_string(v))
        env = Map.delete(env, {:alias, Atom.to_string(v)})
        env = if qt, do: Map.put(env, name, qt), else: Map.delete(env, name)
        {"let #{name} := List.tail #{paren_or(expr(env, q, qt))}", env}
      {:=, _, [lhs, rhs]} -> bind_pat_let(env, lhs, rhs)
      other -> fail("only bindings are supported inside a block expression, got #{Macro.to_string(other)}")
    end
  end

  # `x = e` and `{a, b} = e` as a Lean `let`. Returns {"let p := e", env}.
  # A variable simply shadows (Lean's `let` is not recursive, so the
  # right-hand side still reads the old one); any other pattern must be
  # irrefutable at its type, because a `let` has nothing to fall through to.
  defp bind_pat_let(env, lhs, rhs) do
    t = type_of(env, rhs) || expr_type(env, rhs)
    struct_state_of_type(t) &&
      fail("#{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}: a whole state value cannot be bound; bind its fields or return it")
    s = expr(env, rhs, t)
    case lhs do
      {v, _, nil} when is_atom(v) ->
        name = lean_ident(Atom.to_string(v))
        env = Map.delete(env, {:alias, Atom.to_string(v)})
        env = if t, do: Map.put(env, name, t), else: Map.delete(env, name)
        {"let #{name} := #{s}", env}
      _ ->
        t || fail("#{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}: the type of the right-hand side is not known")
        irrefutable?(lhs, t) ||
          fail("#{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}: the pattern is not total at #{t}, so the binding could fail and there is nothing to fall through to")
        {ps, env2, gs} = pat(expr_ctx(), lhs, t, env, [])
        gs == [] || fail("#{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}: a pattern that needs a guard cannot be bound")
        env2[:__mapbinds__] == env[:__mapbinds__] ||
          fail("#{Macro.to_string(lhs)} = #{Macro.to_string(rhs)}: a map pattern cannot be bound (the key may be absent)")
        {"let #{ps} := #{s}", env2}
    end
  end

  # Is a pattern total at its type? A variable and `_` are; a tuple at a
  # product type (the model's one tuple value, a map entry) and a struct
  # pattern are, field by field, because each has one constructor; `%{}`
  # matches any map. Everything else -- a literal, a list pattern, one
  # alternative of a union, a map pattern with keys -- can fail.
  defp irrefutable?({:_, _, nil}, _t), do: true
  defp irrefutable?({v, _, nil}, _t) when is_atom(v), do: true
  defp irrefutable?({:=, _, [p, {v, _, nil}]}, t) when is_atom(v), do: irrefutable?(p, t)
  defp irrefutable?({:%, _, [_, {:%{}, _, kvs}]}, t), do: struct_fields(t) != nil and struct_irrefutable?(kvs, t)
  defp irrefutable?({:%{}, _, kvs}, t) do
    if struct_fields(t) != nil, do: struct_irrefutable?(kvs, t), else: kvs == []
  end
  defp irrefutable?(p, t) when is_tuple(p) and (tuple_size(p) == 2 or elem(p, 0) == :{}) do
    case {prod_type(t), tuple_parts(p)} do
      {{kt, vt}, [a, b]} -> irrefutable?(a, kt) and irrefutable?(b, vt)
      _ -> false
    end
  end
  defp irrefutable?(_p, _t), do: false

  defp struct_irrefutable?(kvs, t) do
    Enum.all?(kvs, fn
      {k, p} when is_atom(k) -> irrefutable?(p, field_type(t, k))
      _ -> false
    end)
  end

  # One `case` arm pattern, shared by the body-level and the expression-level
  # compilers: `[]` for the alias of the `:queue.out` empty arm, `some v` for
  # a variable arm that follows a `nil` arm over an Option (`case Map.get(m,
  # k) do nil -> ..; v -> .. end`), otherwise the type-directed `pat`.
  defp case_arm_pat(ctx, p, b, st, env, saw_nil) do
    case {p, st} do
      {{:__queue_empty__, _, [v]}, "List " <> _} ->
        name = lean_ident(Atom.to_string(v))
        env2 = if String.starts_with?(name, "_"), do: env, else: env |> Map.put(name, st) |> Map.put({:alias, Atom.to_string(v)}, "[]")
        {"[]", env2, []}
      # after a `nil` arm, a variable arm over an Option binds the value itself
      {{v, _, nil}, "Option " <> inner} when is_atom(v) and saw_nil ->
        name = lean_ident(Atom.to_string(v))
        if String.starts_with?(name, "_") or Map.has_key?(env, name),
          do: pat(ctx, p, st, env, []),
          else: {"(some #{name})", Map.put(env, name, unparen(inner)), []}
      _ -> pat(ctx, prune_arm_vars(p, b, env), st, env, [])
    end
  end

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

  # `case Map.pop(m, k)`: a match on `get? m k`; the arm `{nil, r}` is `none`
  # with r the map itself, `{p, r}` is `some p` with r the map without k
  # (`erase`). A value that is literally nil would take the first arm on the
  # BEAM; the model's values are never nil.
  defp body(ctx, mod, env, {:case, _, [{{:., _, [{:__aliases__, _, [:Map]}, :pop]}, _, [m, k]} = scrut, [do: arms]]}) do
    {kt, vt} = map_type(var_type(env, m)) || fail("case over #{Macro.to_string(scrut)}: #{Macro.to_string(m)} is not a map variable or field")
    mt = "List (#{kt} × #{vt})"
    ms = paren_or(expr(env, m, mt))
    ks = paren_or(expr(env, k, kt))
    bind_rest = fn env, r, rest ->
      case r do
        {v, _, nil} when is_atom(v) ->
          name = Atom.to_string(v)
          if String.starts_with?(name, "_"), do: env, else: env |> Map.put({:alias, name}, rest) |> Map.put(lean_ident(name), mt)
        other -> fail("case Map.pop: the second element of an arm pattern must be a variable, got #{Macro.to_string(other)}")
      end
    end
    {arm_strs, ctx} =
      Enum.map_reduce(arms, ctx, fn {:->, _, [[p], b]}, c ->
        {pstr, env2} =
          case p do
            {nil, r} -> {"none", bind_rest.(env, r, ms)}
            {vp, r} ->
              {ps, env2, []} = pat(c, prune_arm_vars(vp, b, env), vt, env, [])
              {"(some #{ps})", bind_rest.(env2, r, "(AssocList.erase #{ms} #{ks})")}
            other -> fail("case Map.pop: arm pattern must be a pair {value, rest}, got #{Macro.to_string(other)}")
          end
        {bs, c} = body(c, mod, env2, b)
        {"| #{pstr} => #{bs}", c}
      end)
    {"(match AssocList.get? #{ms} #{ks} with " <> Enum.join(arm_strs, " ") <> ")", ctx}
  end
  defp body(ctx, mod, env, {:case, _, [scrut, [do: arms]]}) do
    st = guess_type(env, scrut)
    {arm_strs, {ctx, _}} =
      Enum.map_reduce(arms, {ctx, false}, fn {:->, _, [[p], b]}, {c, saw_nil} ->
        {pstr, env2, []} = case_arm_pat(c, p, b, st, env, saw_nil)
        {bs, c} = body(c, mod, env2, b)
        {"| #{pstr} => #{bs}", {c, saw_nil or p == nil}}
      end)
    {"(match #{expr(env, scrut, nil)} with " <> Enum.join(arm_strs, " ") <> ")", ctx}
  end
  defp body(ctx, mod, env, b), do: body_stmts(ctx, mod, env, stmts(b))

  # a fresh variable of a case-arm pattern the arm's body never uses (its only
  # use was a resource call the model dropped) is the wildcard `_v`
  defp prune_arm_vars(p, b, env) do
    used = free_vars(b)
    Macro.postwalk(p, fn
      {v, m, nil} = n when is_atom(v) ->
        s = Atom.to_string(v)
        if s in used or String.starts_with?(s, "_") or Map.has_key?(env, lean_ident(s)), do: n, else: {:"_#{s}", m, nil}
      n -> n
    end)
  end

  # the rest of a body after a blocking call may be a single `if`/`case`
  defp body_stmts(ctx, mod, env, [{:if, _, _} = e]), do: body(ctx, mod, env, e)
  defp body_stmts(ctx, mod, env, [{:case, _, _} = e]), do: body(ctx, mod, env, e)
  # Statements followed by an `if`/`case` body. The bindings become `let`s
  # around the whole branch, so the condition and every branch see them. A
  # statement with an effect of its own cannot be lifted like that, because
  # the branch is what produces the effect list: it is carried in the
  # environment as `:__pre_effects__` and prepended to the effects of
  # whichever leaf runs -- which is pushing it into every branch, once per
  # leaf in the text and exactly once in any run. The spawn and ETS counters
  # advance in `env2`, so a leaf that spawns continues the numbering.
  defp body_stmts(ctx, mod, env, stmts)
       when length(stmts) > 1 do
    {pre, [last]} = Enum.split(stmts, -1)
    if match?({tag, _, _} when tag in [:if, :case], last) and not Enum.any?(stmts, &blocking_call?/1) do
      {effs, ctx, env2} = sends(ctx, env, pre)
      env3 = if effs == [], do: env2, else: Map.update(env2, :__pre_effects__, effs, &(&1 ++ effs))
      {s, ctx} = body(ctx, mod, Map.delete(env3, :__lets__), last)
      {wrap_lets(env2, s), ctx}
    else
      split_body(ctx, mod, env, stmts)
    end
  end
  defp body_stmts(ctx, mod, env, stmts), do: split_body(ctx, mod, env, stmts)

  defp split_body(ctx, mod, env, stmts) do
    case Enum.split_while(stmts, fn s -> not blocking_call?(s) end) do
      {before, [call | rest]} when rest != [] -> cps_split(ctx, mod, env, before, call, rest)
      {_, [_]} -> fail("a blocking call must be followed by the rest of the body")
      _ ->
        # statements before a final if/case run in every branch
        case List.last(stmts) do
          {f, _, _} = last when f in [:if, :case] and length(stmts) > 1 -> body(ctx, mod, env, prepend_stmts(Enum.drop(stmts, -1), last))
          _ -> plain_body(ctx, mod, env, stmts)
        end
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
    mod in ctx.ets && fail("#{mod}: a blocking call in a module that creates ETS tables is not supported")
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
    pre_effs = Map.get(env, :__pre_effects__, [])
    {send_strs, ctx, env_after} = sends(ctx, Map.put(env, :__mod__, mod), before)
    this = wrap_lets(env_after, "(.#{await}#{cap_str}, [#{Enum.join(pre_effs ++ send_strs ++ [req], ", ")}])")
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
            init = child_state(c, e, child, arg, cctor, visible_fields(c, child, cfields)) <> spawn_hidden(c, child)
            e = bind_fresh(e, v)
            # the child's init/1 subscriptions, on behalf of the child's pid
            subs = for {sf, topic} <- Map.get(c.init_subs, child, []), do: ".#{sf} #{paren_or(e[{:alias, Atom.to_string(v)}])} #{topic}"
            {Enum.join([if(f == :start_link, do: ".spawnLink (#{init})", else: ".spawn (#{init})") | subs], ", "), {c, e}}
          {:=, _, [lhs, {f, _, [{:__aliases__, _, [child]}, fname, [arg]]}]} when f in [:spawn, :spawn_link, :spawn_monitor] ->
            v =
              case {f, lhs} do
                {:spawn_monitor, {{v, _, nil}, {ref, _, nil}}} when is_atom(v) and is_atom(ref) -> v
                {_, {v, _, nil}} when f != :spawn_monitor and is_atom(v) -> v
                _ -> fail("unsupported spawn binding #{Macro.to_string(s)}")
              end
            Map.get(c.loops, child) == fname || fail("#{child}.#{fname} is not the receive loop of #{child}")
            {cctor, cfields} = List.keyfind(c.st_ctors, ctor_name(child), 0) || fail("unknown module #{child}")
            init = state_expr(c, e, arg, cctor, visible_fields(c, child, cfields)) <> spawn_hidden(c, child)
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
          # `v = :ets.new(..)`: a fresh opaque reference, no effect the model
          # can see. The state carries the hidden counter `ets`; the k-th
          # table this body creates is `Term.mk (ets + k)` and the continuing
          # state advances the counter (`hidden_next`).
          {:=, _, [{v, _, nil}, {{:., _, [:ets, :new]}, _, _}]} when is_atom(v) ->
            k = Map.get(e, :__ets__, 0)
            ref = if k == 0, do: "(Term.mk ets)", else: "(Term.mk (ets + #{k}))"
            e = e |> Map.put(:__ets__, k + 1) |> bind_local(v, ref, "Term")
            {"", {c, e}}
          {f, _, args} when f in [:raise, :throw] and is_list(args) ->
            fail("#{f} is only supported as the last statement of a body (it exits the process): #{Macro.to_string(s)}")
          # `{_, q} = :queue.out(q0)`: the queue without its oldest element
          # (`:queue.out` of an empty queue gives it back unchanged, as `tail` does)
          {:=, _, [{{:_, _, nil}, {v, _, nil}}, {{:., _, [:queue, :out]}, _, [q]}]} when is_atom(v) ->
            {nil, {c, let_bind(e, v, "List.tail #{paren_or(expr(e, q, type_of(e, q)))}", type_of(e, q))}}
          # A pure local binding `v = e` is a `let` around the clause result.
          # A binding that reuses a name already in scope -- a state field the
          # clause pattern bound, as `refs = Map.put(refs, k, v)` does -- is
          # not let-bound but substituted at its uses, because the `let` would
          # shadow the part the rest of the clause reads.
          {:=, _, [{v, _, nil}, rhs]} when is_atom(v) ->
            t = type_of(e, rhs) || expr_type(e, rhs)
            struct_state_of_type(t) && fail("#{v} = #{Macro.to_string(rhs)}: a whole state value cannot be bound; bind its fields or return it")
            if Map.has_key?(e, lean_ident(Atom.to_string(v))) do
              {"", {c, bind_local(e, v, paren_or(expr(e, rhs, t)), t)}}
            else
              {nil, {c, let_bind(e, v, expr(e, rhs, t), t)}}
            end
          # A pattern binding `{a, b} = e`, `%Mod{f: p} = e`: the Lean
          # `let <pattern> := e` of `bind_pat_let`, wrapped around the clause
          # result like any other let. Only a pattern that is total at its
          # type can be bound (there is nothing to fall through to). An atom
          # on the left is not a binding but a match on a result, as in
          # `:ok = Phoenix.PubSub.subscribe(..)`, and falls through below.
          {:=, _, [lhs, rhs]} when not is_atom(lhs) ->
            {ls, e} = bind_pat_let(e, lhs, rhs)
            {nil, {c, Map.update(e, :__lets__, [ls], &(&1 ++ [ls]))}}
          other ->
            case pubsub_call(c, Map.get(e, :__mod__), other) do
              {:subscribe, topic, nil} -> {".subscribe me #{topic}", {c, e}}
              {:unsubscribe, topic, nil} -> {".unsubscribe me #{topic}", {c, e}}
              {:broadcast, topic, m} -> {".broadcast #{topic} #{paren_or(msg_expr(c, e, m))}", {c, e}}
              nil -> fail("unsupported statement #{Macro.to_string(other)}")
            end
        end
      end)
    {Enum.reject(strs, &(is_nil(&1) or &1 == "")), c, e}
  end

  # a local binding: the name renders as `s` wherever the body uses it
  defp bind_local(env, v, s, t) do
    name = Atom.to_string(v)
    env = Map.put(env, {:alias, name}, s)
    if t, do: Map.put(env, lean_ident(name), t), else: env
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
    # the effects of the statements that ran before the enclosing if/case
    pre_effs = Map.get(env, :__pre_effects__, [])
    {send_strs, ctx, env} = sends(ctx, Map.put(env, :__mod__, mod), sends)
    send_strs = pre_effs ++ send_strs
    # a continuing state of a loop with `after` re-enters the receive at the
    # next generation (an exit, raise or throw keeps the whole state instead)
    next_state = fn e -> state_expr(ctx, env, e, ctor, visible_fields(ctx, mod, fields)) <> hidden_next(ctx, mod, env) end
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
    # The probe pass (`reply_probe`) only wants the type this expression has
    # here, in its own clause environment; it renders nothing.
    if Process.get(:to_lean_reply_probe, false) do
      Process.put(:to_lean_reply_types, [type_of(env, r) | Process.get(:to_lean_reply_types, [])])
      send_str(ctx, from, ".reply probe")
    else
      # Untyped mode infers `term()` for a reply that is not a literal. If the
      # expression does have a type in the model, the opaque reply constructor
      # cannot carry it, and Lean would reject the generated file: say so here
      # instead, naming the declaration that fixes it.
      if ctx.reply_type == "Term" do
        case type_of(env, r) do
          nil -> :ok
          "Term" -> :ok
          rt -> fail("the reply #{Macro.to_string(r)} has type #{rt}, but the reply type was inferred as the opaque term(); declare @type reply :: ...")
        end
      end
      send_str(ctx, from, ".reply #{paren_or(expr(env, r, ctx.reply_type))}")
    end
  end

  # the current state rebuilt from the clause's state pattern (for exit/1, raise, throw)
  defp whole_state(env, ctor, _fields) do
    case env[:__sparts__] do
      nil -> fail("exit/raise/throw needs the state bound by the pattern")
      parts -> if parts == [], do: ".#{ctor}", else: ".#{ctor} " <> Enum.join(parts, " ")
    end
  end

  defp guess_type(env, {v, _, nil}) when is_atom(v), do: Map.get(env, Atom.to_string(v)) || fail("untyped scrutinee #{v}")
  defp guess_type(env, {{:., _, [{v, _, nil}, f]}, _, []} = e) when is_atom(v) and is_atom(f), do: var_type(env, e) || fail("untyped scrutinee #{Macro.to_string(e)}")
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

  # the Lean type of a variable bound by the patterns (or a local binding),
  # of a record field `s.f`, or nil
  defp var_type(env, {v, _, nil}) when is_atom(v), do: Map.get(env, lean_ident(Atom.to_string(v)))
  defp var_type(env, {{:., _, [{v, _, nil}, f]}, _, []}) when is_atom(v) and is_atom(f) do
    case Map.get(env, {:field, lean_ident(Atom.to_string(v)), f}) do
      nil -> nil
      part -> Map.get(env, part)
    end
  end
  defp var_type(_env, _), do: nil

  # the Lean type of a local binding's right-hand side, when it can be told
  # from the source: a variable or field, a Map call (the map's own type,
  # or the value's), `:ets.new` (a Term), a literal
  defp expr_type(env, {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, [m | _]}) when f in [:put, :delete, :filter, :reject], do: var_type(env, m)
  defp expr_type(env, {{:., _, [{:__aliases__, _, [:Map]}, :get]}, _, [m, _, _]}), do: with({_, vt} <- map_type(var_type(env, m)), do: vt)
  defp expr_type(env, {{:., _, [{:__aliases__, _, [:Map]}, f]}, _, [m, _]}) when f in [:get, :fetch], do: with({_, vt} <- map_type(var_type(env, m)), do: "Option " <> paren_or(vt))
  defp expr_type(_env, {{:., _, [:ets, :new]}, _, _}), do: "Term"
  defp expr_type(_env, n) when is_integer(n), do: "Int"
  defp expr_type(_env, b) when is_boolean(b), do: "Bool"
  defp expr_type(_env, s) when is_binary(s), do: "String"
  defp expr_type(_env, {:<<>>, _, _}), do: "String"
  defp expr_type(_env, {:<>, _, [_, _]}), do: "String"
  defp expr_type(env, e) when is_tuple(e) and tuple_size(e) == 3 do
    case remote_action(e) do
      {:const, _, ct} -> ct
      {:fun, _, _, rt} -> rt
      _ -> var_type(env, e)
    end
  end
  defp expr_type(env, e), do: var_type(env, e)

  # the record keys of a state constructor, or nil for a positional state
  defp record_keys(ctx, ctor), do: Enum.find_value(ctx.records, fn {mod, keys} -> ctor_name(mod) == ctor && keys end)

  # rebuild the state constructor from an expression of the state type
  # a record update `%{s | f: e, ..}`: the parts of `s` with those fields replaced
  defp state_expr(ctx, env, {:%{}, _, [{:|, _, [{v, _, nil}, ups]}]} = e, ctor, fields)
       when is_atom(v) and is_list(ups) do
    name = lean_ident(Atom.to_string(v))
    # a struct-shaped state takes the same syntax, and is rebuilt by state_expr/4
    if record_keys(ctx, ctor) == nil do
      state_expr(env, e, ctor, fields)
    else
      record_update_expr(env, e, v, name, ups, ctor, fields)
    end
  end

  defp state_expr(ctx, env, e, ctor, fields) do
    case record_keys(ctx, ctor) do
      nil -> state_expr(env, e, ctor, fields)
      keys ->
        case e do
          # a record literal `%{f: e, ..}`: every field must be given
          {:%{}, _, pairs} when is_list(pairs) ->
            Keyword.keyword?(pairs) || fail("#{Macro.to_string(e)}: a record state literal needs atom keys")
            Enum.each(pairs, fn {k, _} -> k in keys || fail("#{Macro.to_string(e)}: #{k} is not a field of the state") end)
            ".#{ctor} " <>
              Enum.map_join(Enum.zip(keys, fields), " ", fn {k, {_, t}} ->
                case List.keyfind(pairs, k, 0) do
                  {_, x} -> paren_or(expr(env, x, t))
                  nil -> fail("#{Macro.to_string(e)}: the state literal must give every field, #{k} is missing")
                end
              end)
          # the whole-state variable: an alias from a fallthrough, or the parts it binds
          {v, _, nil} when is_atom(v) ->
            case Map.get(env, {:alias, Atom.to_string(v)}) do
              nil ->
                parts = Map.get(env, "__whole__" <> lean_ident(Atom.to_string(v))) || fail("whole-state variable #{v} not bound by a pattern")
                ".#{ctor} " <> Enum.join(parts, " ")
              s -> s
            end
          _ -> fail("state expression #{Macro.to_string(e)} does not fit the record state %{#{Enum.join(keys, ", ")}}")
        end
    end
  end

  defp record_update_expr(env, e, v, name, ups, ctor, fields) do
    keys = Map.get(env, {:record, name}) || fail("#{Macro.to_string(e)}: #{v} is not the whole-state variable of the record state")
    parts = Map.fetch!(env, "__whole__" <> name)
    Enum.each(ups, fn {k, _} -> k in keys || fail("#{Macro.to_string(e)}: #{k} is not a field of the state") end)
    ".#{ctor} " <>
      Enum.map_join(Enum.zip([keys, parts, fields]), " ", fn {k, part, {_, t}} ->
        case List.keyfind(ups, k, 0) do
          {_, x} -> paren_or(expr(env, x, t))
          nil -> (part != "_" && part) || fail("#{Macro.to_string(e)}: field #{k} of #{v} is not bound (translator bug)")
        end
      end)
  end
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

  # the Kernel type tests the model can decide (see `type_test`)
  @type_tests [:is_nil, :is_pid, :is_list, :is_map, :is_integer, :is_atom,
               :is_boolean, :is_number, :is_float, :is_tuple, :is_binary]

  # expression -> Lean, with an expected type used only to insert some/none
  defp expr(_env, nil, "Option " <> _), do: "none"
  defp expr(_env, nil, nil), do: "none"
  # a call to a function defined in the same module (see "module-local functions")
  defp expr(env, {:__local_call__, _, [id | args]}, t), do: local_call_str(env, id, args, t)
  # ---- control forms: an if/case/block is an expression (see `ctl_expr`) ----
  # These come before the Option clause so that each branch is wrapped in
  # `some`/`none` on its own, rather than the whole `if`.
  defp expr(env, {f, _, _} = e, t) when f in [:if, :case, :__block__, :=], do: ctl_expr(env, e, t)
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
  # `s.f`: the field of a record-shaped state bound by the whole variable `s`,
  # the part a flattened struct state bound, or the projection of a struct value
  defp expr(env, {{:., _, [{v, _, nil}, f]}, _, []} = e, _t) when is_atom(v) and is_atom(f) do
    name = lean_ident(Atom.to_string(v))
    if Map.has_key?(env, {:record, name}) do
      Map.get(env, {:field, name, f}) || fail("#{Macro.to_string(e)}: #{f} is not a field of the state (translator bug if it is)")
    else
      case state_field(env, v, f) do
        {part, _} -> part
        nil ->
          st = Map.get(env, name) || fail("#{Macro.to_string(e)}: the type of #{v} is not known")
          struct_fields(st) || fail("#{Macro.to_string(e)}: #{v} is not a struct (#{st})")
          field_type(st, f)
          "#{name}.#{f}"
      end
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
  # ---- binaries: Lean Strings (Leanactors/Str.lean) ----
  defp expr(_env, s, "Term") when is_binary(s),
    do: fail("the string #{inspect(s)} is used at an opaque Term position; declare the type (@type) so the field becomes a String")
  defp expr(_env, s, t) when is_binary(s) do
    t in [nil, "String"] || fail("the string #{inspect(s)} is used at type #{t}")
    str_lit(s)
  end
  defp expr(env, {:<<>>, _, parts}, t) do
    t in [nil, "String"] || fail("an interpolated binary is used at type #{t}")
    interp(env, parts)
  end
  defp expr(env, {:<>, _, [a, b]}, t) do
    t in [nil, "String"] || fail("`<>` builds a binary, used at type #{t}")
    "(#{expr(env, a, "String")} ++ #{expr(env, b, "String")})"
  end
  defp expr(env, {f, _, [_ | _]} = e, t) when f in [:inspect, :to_string] do
    t in [nil, "String"] || fail("#{Macro.to_string(e)} is a binary, used at type #{t}")
    "Str.toStr " <> paren_or(expr(env, strip_to_string(e), nil))
  end
  # ---- a module name as a value, and the @remote table ----
  defp expr(_env, {:__aliases__, _, segs}, t) do
    t in [nil, "Module"] || fail("the module name #{Enum.join(segs, ".")} is used at type #{t}")
    module_ctor(segs)
  end
  defp expr(env, {{:., _, [{:__aliases__, _, _}, _]}, _, args} = e, t) when is_list(args) do
    case remote_action(e) do
      nil -> fail("unsupported expression #{Macro.to_string(e)}")
      action -> remote_expr(env, e, action, args, t)
    end
  end
  defp expr(env, {{:., _, [Access, _]}, _, args} = e, t) when is_list(args) do
    case remote_action(e) do
      nil -> fail("unsupported expression #{Macro.to_string(e)}")
      action -> remote_expr(env, e, action, args, t)
    end
  end
  defp expr(env, {:not, _, [a]}, _t), do: "(¬ #{expr(env, a, nil)})"
  defp expr(_env, b, _t) when is_boolean(b), do: "#{b}"
  defp expr(_env, a, "Term") when is_atom(a) and a not in [nil, true, false],
    do: fail("the atom #{inspect(a)} is used at an opaque Term position; declare the type (@type) so it becomes an enum")
  defp expr(_env, a, "Atom") when is_atom(a) and a not in [nil, true, false], do: atom_ctor(a)
  defp expr(_env, a, _t) when is_atom(a) and a not in [nil, true, false], do: ".#{a}"
  defp expr(_env, n, _t) when is_integer(n), do: "#{n}"
  defp expr(_env, [], _t), do: "[]"
  defp expr(env, xs, t) when is_list(xs) do
    if kw_list?(xs, t),
      do: kw_lit(env, xs, t),
      else: "[" <> Enum.map_join(xs, ", ", &expr(env, &1, elem_type(t))) <> "]"
  end
  defp expr(env, {v, _, nil}, _t) when is_atom(v), do: Map.get(env, {:alias, Atom.to_string(v)}, lean_ident(Atom.to_string(v)))
  # ---- Kernel guards and functions, on the types the model has ----
  # A type test is decided statically: a value of the model has exactly one
  # type, so `is_pid(p)` on a `Pid` is `true` and `is_list(p)` on it is
  # `false`. The tests that cannot be decided are errors rather than guesses:
  # an opaque `Term` holds a value whose BEAM type the model does not know,
  # a tagged union has both atom and tuple alternatives, and there are no
  # binaries.
  defp expr(env, {f, _, [a]}, _t) when f in @type_tests, do: type_test(env, f, a)
  # `elem/2` and `tuple_size/1` on the one tuple the model has as a value, the
  # pair of a map entry (`K × V`); a tagged tuple is a constructor, whose
  # fields are reached by matching, not by index.
  defp expr(env, {:elem, _, [tup, i]}, _t) when is_integer(i) do
    t = type_of(env, tup) || fail("elem/2: the type of #{Macro.to_string(tup)} is not known")
    prod_type(t) || fail("elem/2 at #{t}: only a pair (a map entry) is indexable; match a tagged tuple instead")
    i in [0, 1] || fail("elem/2: a pair has no element #{i}")
    "#{paren_or(expr(env, tup, t))}.#{i + 1}"
  end
  defp expr(env, {:tuple_size, _, [tup]}, _t) do
    t = type_of(env, tup) || fail("tuple_size/1: the type of #{Macro.to_string(tup)} is not known")
    prod_type(t) || fail("tuple_size/1 at #{t}: only a pair (a map entry) is a tuple value in the model")
    "2"
  end
  # `abs/1` through `Int.natAbs`; `min`/`max` are Lean's. `div`/`rem` are `/`
  # and `%` on Nat only: Elixir's `div` truncates toward zero, which Lean's
  # integer division does not, so an Int operand is an error rather than a
  # silent difference.
  defp expr(env, {:abs, _, [a]}, t) do
    case type_of(env, a) || t do
      "Nat" -> paren_or(expr(env, a, "Nat"))
      "Int" -> "(Int.ofNat #{paren_or(expr(env, a, "Int"))}.natAbs)"
      other -> fail("abs/1 at #{other || "an unknown type"}: only integer() and non_neg_integer()")
    end
  end
  defp expr(env, {f, _, [a, b]}, t) when f in [:min, :max] do
    at = type_of(env, a) || type_of(env, b) || t
    at in ["Nat", "Int"] || fail("#{f}/2 at #{at || "an unknown type"}: only integer() and non_neg_integer()")
    "(#{f} #{paren_or(expr(env, a, at))} #{paren_or(expr(env, b, at))})"
  end
  defp expr(env, {f, _, [a, b]}, t) when f in [:div, :rem] do
    at = type_of(env, a) || type_of(env, b) || t
    at == "Nat" ||
      fail("#{f}/2 at #{at || "an unknown type"}: only non_neg_integer() (Elixir's div truncates toward zero, Lean's integer division does not)")
    "(#{expr(env, a, "Nat")} #{if f == :div, do: "/", else: "%"} #{expr(env, b, "Nat")})"
  end
  # `x in list` is list membership
  defp expr(env, {:in, _, [x, l]}, _t) do
    lt = type_of(env, l) || list_of(type_of(env, x))
    "(#{expr(env, x, elem_type(lt))} ∈ #{paren_or(expr(env, l, lt))})"
  end
  # ---- the boolean and comparison operators Elixir spells differently ----
  # `&&`/`||` are the `and`/`or` of the model: a non-boolean operand is
  # Elixir truthiness, which no value of the model has.
  defp expr(env, {op, _, [a, b]}, _t) when op in [:&&, :||] do
    for x <- [a, b], xt = type_of(env, x), xt != "Bool",
      do: fail("`#{op}` with the non-boolean operand #{Macro.to_string(x)} : #{xt} is not supported (Elixir truthiness has no value in the model)")
    "(#{expr(env, a, "Bool")} #{if op == :&&, do: "∧", else: "∨"} #{expr(env, b, "Bool")})"
  end
  # `===`/`!==` are `==`/`!=`: the modelled types have no boxed-value identity
  defp expr(env, {op, _, [a, b]}, t) when op in [:*, :===, :!==] do
    lop = case op do
      :* -> "*"
      :=== -> "="
      :!== -> "≠"
    end
    at = if op == :*, do: t, else: nil
    "(#{expr(env, a, at)} #{lop} #{expr(env, b, at)})"
  end
  defp expr(env, {:!, _, [a]}, _t), do: "(¬ #{expr(env, a, nil)})"
  defp expr(env, {:-, _, [a]}, t) do
    at = type_of(env, a) || t
    at in [nil, "Int"] || fail("unary `-` at #{at}: only integer()")
    "(-#{paren_or(expr(env, a, at))})"
  end
  defp expr(env, {:+, _, [a]}, t), do: expr(env, a, t)
  defp expr(env, {op, _, [a, b]} = e, t) when op in [:+, :-, :++, :<=, :>=, :<, :>, :==, :!=, :and, :or] do
    # an Instant has equality and nothing else: refuse an order or an
    # arithmetic on one here rather than let Lean fail on a missing instance
    if op in [:+, :-, :<=, :>=, :<, :>] and "Instant" in [type_of(env, a), type_of(env, b)],
      do: fail("`#{op}` in #{Macro.to_string(e)}: the model has no clock, so an Instant has equality and nothing else")
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
        {name, ts} =
          case union_ctors(t) do
            nil -> {Atom.to_string(tag), List.duplicate(nil, length(args))}
            ctors -> union_ctor(ctors, tag, length(args)) || fail("#{tag}/#{length(args)} is not an alternative of #{t}")
          end
        "(.#{name}" <> Enum.map_join(Enum.zip(args, ts), "", fn {a, at} -> " " <> paren_or(expr(env, a, at)) end) <> ")"
      true -> fail("unsupported expression #{Macro.to_string(e)}" <> if(t, do: " at type #{t}", else: ""))
    end
  end
  defp expr(_env, e, _t), do: fail("unsupported expression #{Macro.to_string(e)}")

  # A Kernel type test, decided from the modelled type of its argument. At an
  # Option type the value is the argument or nil, so the test is `isNone` for
  # `is_nil` and `isSome` (or `false`) for the others.
  defp type_test(env, f, a) do
    t = type_of(env, a) || fail("#{f}/1: the type of #{Macro.to_string(a)} is not known")
    s = paren_or(expr(env, a, t))
    case {f, t} do
      {:is_nil, "Option " <> _} -> "#{s}.isNone"
      {_, "Option " <> inner} -> if test_of(f, unparen(inner)) == "true", do: "#{s}.isSome", else: "false"
      _ -> test_of(f, t)
    end
  end

  # the value of a type test at a modelled type
  defp test_of(f, t) do
    t == "Term" &&
      fail("#{f}/1 at term(): the model does not know the BEAM type behind an opaque value; declare a @type for it")
    mixed = fn ->
      union_ctors(t) == nil ||
        fail("#{f}/1 at the tagged union #{t}: its alternatives are both atoms and tuples, so the test is not decidable")
    end
    v =
      case f do
        :is_nil -> false
        :is_pid -> t == "Pid"
        :is_integer -> t in ["Int", "Nat"]
        :is_number -> t in ["Int", "Nat"]
        :is_float -> false
        # a binary is a Lean String (Leanactors/Str.lean): the test is
        # decidable once there is a string type to decide it against
        :is_binary -> t == "String"
        :is_boolean -> t == "Bool"
        # `true` and `false` are atoms on the BEAM, and so is every
        # alternative of an enum; a struct and the model's map are maps
        :is_atom -> mixed.() && (t == "Bool" or enum_type?(t))
        :is_tuple -> mixed.() && prod_type(t) != nil
        :is_list -> mixed.() && String.starts_with?(t, "List ") and map_type(t) == nil
        :is_map -> mixed.() && (map_type(t) != nil or struct_fields(t) != nil)
      end
    "#{v}"
  end

  defp list_of(nil), do: nil
  defp list_of(t), do: "List " <> paren(t)

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

  # ---------- values: binaries, keyword lists, sets, instants, module names ----------
  #
  # The value families the @remote table at the top of this file leans on.
  # Two of them need a per-file inductive -- `Atom` for the keys of keyword
  # lists, `Module` for module names used as values -- and both are built
  # from what the rendering actually used: every key and every module name
  # that reaches `expr/3` or `pat/5` registers itself here, and `render/2`
  # emits the declarations once the clauses are rendered.

  # An Elixir binary is a Lean String (Leanactors/Str.lean).
  defp str_lit(s) do
    esc =
      s
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")
      |> String.replace("\t", "\\t")
      |> String.replace("\r", "\\r")
    "\"" <> esc <> "\""
  end

  # `"a#{e}b"` is `"a" ++ Str.toStr e ++ "b"`. An interpolated `inspect(e)`
  # or `to_string(e)` is the same rendering: `Str.toStr` is what the model
  # has for "render this value as a binary", and for a value with no
  # printable model it is the derived `Repr` (see Leanactors/Str.lean).
  defp interp(env, parts) do
    pieces =
      for part <- parts, s = interp_part(env, part), s != "\"\"", do: s
    case pieces do
      [] -> "\"\""
      [one] -> one
      many -> "(" <> Enum.join(many, " ++ ") <> ")"
    end
  end

  defp interp_part(_env, s) when is_binary(s), do: str_lit(s)
  # `#{e}` where e is already a binary needs no rendering; anything else,
  # and an explicit `inspect(e)`/`to_string(e)`, goes through `Str.toStr`
  defp interp_part(env, {:"::", _, [{{:., _, [Kernel, :to_string]}, _, [inner]}, {:binary, _, nil}]}) do
    e = strip_to_string(inner)
    if e == inner and type_of(env, e) == "String",
      do: paren_or(expr(env, e, "String")),
      else: "Str.toStr " <> paren_or(expr(env, e, nil))
  end
  defp interp_part(env, {:"::", _, [inner, {:binary, _, nil}]}),
    do: "Str.toStr " <> paren_or(expr(env, strip_to_string(inner), nil))
  defp interp_part(_env, other), do: fail("unsupported part of a binary: #{Macro.to_string(other)}")

  defp strip_to_string({{:., _, [Kernel, :to_string]}, _, [e]}), do: strip_to_string(e)
  defp strip_to_string({:to_string, _, [e]}), do: strip_to_string(e)
  defp strip_to_string({:inspect, _, [e]}), do: strip_to_string(e)
  defp strip_to_string({:inspect, _, [e, _]}), do: strip_to_string(e)
  defp strip_to_string(e), do: e

  # A keyword list `[k: v, ..]` is the association list `List (Atom × V)`,
  # so `Keyword` and `Access` are the `AssocList` a map already uses. The
  # catch is that `[ok: 1]` and `[{:ok, 1}]` are the same AST: at a known
  # type the type decides, and at an unknown one a key that is an
  # alternative of one of the file's tagged unions keeps the old reading
  # (a list of that union's values).
  defp kw_list?([], _t), do: false
  defp kw_list?(xs, t) do
    Enum.all?(xs, &match?({k, _} when is_atom(k) and k not in [nil, true, false], &1)) and
      case map_type(t) do
        {"Atom", _} -> true
        nil -> t == nil and not Enum.any?(xs, fn {k, _} -> union_alt?(k) end)
        _ -> false
      end
  end

  # is `tag` an alternative of arity 1 of some tagged union of this file?
  defp union_alt?(tag) do
    Process.get(:to_lean_unions, %{})
    |> Map.values()
    |> Enum.any?(fn ctors -> Enum.any?(ctors, fn {t, ts} -> t == tag and length(ts) == 1 end) end)
  end

  defp kw_lit(env, xs, t) do
    vt = with({_, v} <- map_type(t), do: v)
    "[" <> Enum.map_join(xs, ", ", fn {k, v} -> "(#{atom_ctor(k)}, #{expr(env, v, vt)})" end) <> "]"
  end

  # register an atom key and return its constructor
  defp atom_ctor(k) do
    name = lean_atom_name(k)
    Process.put(:to_lean_atoms, Enum.uniq(Process.get(:to_lean_atoms, []) ++ [name]))
    "." <> name
  end

  defp lean_atom_name(k) do
    s = Atom.to_string(k)
    Regex.match?(~r/^[a-zA-Z_][a-zA-Z0-9_'?!]*$/, s) ||
      fail("the atom #{inspect(k)} has no Lean constructor name; it cannot be a keyword-list key here")
    lean_ident(s)
  end

  # A module name used as a value is a constant of the file's `Module`
  # inductive: it can be stored, sent and compared, which is all the
  # modules this translates ever do with one (a child module in a spec, an
  # implementation module in a registry). Nothing can be called on it.
  defp module_ctor(segs) do
    name = Enum.map_join(segs, "_", &Atom.to_string/1)
    Process.put(:to_lean_mods, Enum.uniq(Process.get(:to_lean_mods, []) ++ [name]))
    "." <> name
  end

  # ---------- the @remote table, applied ----------

  # `Mod.f(args)` -> its row's action, or nil when there is no row
  defp remote_action({{:., _, [{:__aliases__, _, segs}, f]}, _, args}) when is_list(args),
    do: remote_row(segs, f, length(args))
  defp remote_action({{:., _, [Access, f]}, _, args}) when is_list(args),
    do: remote_row([:Access], f, length(args))
  defp remote_action(_), do: nil

  defp remote_row(segs, f, arity) do
    case Enum.find(@remote, fn {m, ff, a, _} -> m == segs and ff == f and a == arity end) do
      {_, _, _, action} -> action
      nil -> nil
    end
  end

  # a statement with no effect in the model, dropped before translation
  defp remote_noop?(e), do: remote_action(e) == :noop

  # `Mod.f(args)` as an expression, per its row
  defp remote_expr(_env, e, :noop, _args, _t),
    do: fail("#{Macro.to_string(e)} has no value in the model: it is dropped as a statement, so it cannot be used as an expression")
  defp remote_expr(_env, e, {:error, why}, _args, _t),
    do: fail("#{Macro.to_string(e)} is not supported: #{why}")
  defp remote_expr(_env, e, {:const, lean, ct}, _args, t) do
    (t == nil or ct == nil or t == ct) || fail("#{Macro.to_string(e)} is a #{ct}, used at type #{t}")
    lean
  end
  defp remote_expr(env, e, {:fun, lean, ats, rt}, args, t) do
    (t == nil or rt == nil or t == rt) || fail("#{Macro.to_string(e)} is a #{rt}, used at type #{t}")
    lean <> Enum.map_join(Enum.zip(args, ats), "", fn {a, at} -> " " <> paren_or(expr(env, a, at)) end)
  end
  defp remote_expr(env, e, {:assoc, op}, args, t), do: kw_call(env, e, op, args, t)
  defp remote_expr(env, _e, {:set, fun}, [m | rest], t) do
    mt = (map_set_type(t) || type_of(env, m)) |> map_set_type()
    at = if fun in ~w(SetList.union SetList.difference SetList.intersection), do: mt, else: elem_type(mt)
    fun <> " " <> paren_or(expr(env, m, mt)) <> Enum.map_join(rest, "", &(" " <> paren_or(expr(env, &1, at))))
  end

  # a set type is a list type; anything else is unknown
  defp map_set_type("List " <> _ = t), do: t
  defp map_set_type(_), do: nil

  # `Keyword.f(..)`, `Access.get(..)` and `opts[:k]` over the association
  # list. Everything but `fetch!/2` is exactly the `Map` rendering, so one
  # keyword list behaves like one map; `fetch!/2` raises on the BEAM, which
  # an expression here cannot, so it is the lookup at the value type's
  # default, like `hd/1`.
  defp kw_call(env, e, op, args, t) do
    # the key is an Atom whichever way the list is typed, so register it
    case args do
      [_, k | _] when is_atom(k) and k not in [nil, true, false] -> atom_ctor(k)
      _ -> nil
    end
    case {op, args} do
      {:fetch!, [m, k]} ->
        mt = map_type(var_type(env, m))
        {kt, vt} = mt || {"Atom", t}
        vt || fail("#{Macro.to_string(e)}: the value type of #{Macro.to_string(m)} is not known; declare it (@type)")
        ms = paren_or(expr(env, m, mt && "List (#{kt} × #{vt})"))
        "(AssocList.get? #{ms} #{paren_or(expr(env, k, kt))}).getD #{paren_or(default_expr(vt))}"
      _ ->
        map_call(env, op, args, t)
    end
  end

  # ---------- the per-file Atom and Module declarations ----------

  defp value_decls(all_types) do
    atoms = Process.get(:to_lean_atoms, [])
    mods = Process.get(:to_lean_mods, [])
    mentions = fn n -> Enum.any?(all_types, &Regex.match?(~r/\b#{n}\b/, &1)) end
    if atoms == [] and mentions.("Atom"),
      do: fail("a type of this file is a keyword list, but no atom key is used anywhere: the Atom type would be empty")
    if mods == [] and mentions.("Module"),
      do: fail("a type of this file is module(), but no module name is used as a value: the Module type would be empty")
    decl = fn name, ctors, doc ->
      if ctors == [],
        do: [],
        else: ["-- #{doc}\ninductive #{name}\n" <> Enum.map_join(ctors, "\n", &"  | #{&1}") <> "\n  deriving Repr, DecidableEq\n"]
    end
    decl.("Atom", atoms, "The atoms this file uses as keyword-list keys.") ++
      decl.("Module", mods, "The module names this file uses as values.")
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
      t == "String" -> "\"\""
      t == "Instant" -> "Instant.now"
      t == "Term" -> "(Term.mk 0)"
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
  defp type_of(env, {{:., _, [{v, _, nil}, f]}, _, []} = e) when is_atom(v) and is_atom(f) do
    case state_field(env, v, f) do
      {_, t} -> t
      nil ->
        case struct_fields(Map.get(env, lean_ident(Atom.to_string(v)))) do
          nil -> var_type(env, e)
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
  defp type_of(_env, {:__local_call__, _, [id | _]}) do
    case Process.get(:to_lean_local_sigs, %{})[id] do
      nil -> nil
      sig -> sig.rtype
    end
  end
  defp type_of(env, {op, _, [a, b]}) when op in [:+, :-], do: type_of(env, a) || type_of(env, b)
  # control forms: the type of a branch (they all have the same one)
  defp type_of(env, {:if, _, [_, blocks]}) when is_list(blocks),
    do: Enum.find_value(blocks, fn {_, b} -> type_of(env, b) end)
  defp type_of(env, {:case, _, [_, [do: arms]]}),
    do: Enum.find_value(arms, fn {:->, _, [_, b]} -> type_of(env, b) end)
  defp type_of(env, {:__block__, _, xs}) when xs != [], do: type_of(env, List.last(xs))
  # the Kernel guards and operators
  defp type_of(_env, {f, _, [_]}) when f in @type_tests, do: "Bool"
  defp type_of(_env, {op, _, [_, _]}) when op in [:&&, :||, :in, :===, :!==], do: "Bool"
  defp type_of(_env, {:!, _, [_]}), do: "Bool"
  defp type_of(_env, {:tuple_size, _, [_]}), do: "Nat"
  defp type_of(env, {:abs, _, [a]}), do: type_of(env, a)
  defp type_of(env, {:-, _, [a]}), do: type_of(env, a)
  defp type_of(env, {:+, _, [a]}), do: type_of(env, a)
  defp type_of(env, {op, _, [a, b]}) when op in [:*, :min, :max, :div, :rem], do: type_of(env, a) || type_of(env, b)
  defp type_of(env, {:elem, _, [tup, i]}) when is_integer(i) do
    case prod_type(type_of(env, tup)) do
      {kt, vt} -> if i == 0, do: kt, else: vt
      nil -> nil
    end
  end
  # a pair of two typed expressions is the model's one tuple value, `A × B`
  # (this is what lets `{a, b} = if .. do {x, y} else {u, v} end` bind)
  defp type_of(env, {a, b}) do
    with ta when ta != nil <- type_of(env, a),
         tb when tb != nil <- type_of(env, b),
      do: "#{paren(ta)} × #{paren(tb)}", else: (_ -> nil)
  end
  # ---- values (binaries, the @remote table) ----
  defp type_of(_env, s) when is_binary(s), do: "String"
  defp type_of(_env, {:<<>>, _, _}), do: "String"
  defp type_of(_env, {:<>, _, [_, _]}), do: "String"
  defp type_of(_env, {f, _, [_ | _]}) when f in [:inspect, :to_string], do: "String"
  # a @remote row: a constant names its Lean type (a clock read), and a
  # keyword lookup has the type its list gives it (so `opts[:k]` may be a
  # `case` scrutinee, exactly as `Map.get/2` is)
  defp type_of(env, e) when is_tuple(e) and tuple_size(e) == 3 do
    case {remote_action(e), e} do
      {{:const, _, ct}, _} -> ct
      {{:fun, _, _, rt}, _} -> rt
      {{:assoc, op}, {_, _, [m | _] = args}} -> assoc_type(env, op, m, length(args))
      _ -> nil
    end
  end
  defp type_of(_env, _), do: nil

  defp assoc_type(env, op, m, arity) do
    mt = map_type(var_type(env, m))
    case {op, arity, mt} do
      {op, 2, {_, vt}} when op in [:get, :fetch] -> opt_type(vt)
      {:get, 3, {_, vt}} -> vt
      {:fetch!, 2, {_, vt}} -> vt
      {op, _, _} when op in [:put, :delete] -> var_type(env, m)
      {:has_key?, 2, _} -> "Bool"
      {:keys, 1, {kt, _}} -> "List " <> paren(kt)
      {:values, 1, {_, vt}} -> "List " <> paren(vt)
      _ -> nil
    end
  end

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
    # during the dry pass that infers the local helpers' signatures (see
    # `collect_local_uses`) an error is not final: the real pass reports it.
    if Process.get(:to_lean_dry) do
      throw({:to_lean_dry, msg})
    else
      IO.puts(:stderr, "error: " <> msg)
      System.halt(2)
    end
  end
end

ToLean.main(System.argv())
