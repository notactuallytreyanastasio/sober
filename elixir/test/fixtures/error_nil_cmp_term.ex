# expect: error nil is not a value of that type
# A comparison with nil at an opaque `term()`. The model has no nil except
# at an Option type, so the question `v != nil` asks is about a value this
# type does not have; rendering it as `none` would be Lean the elaborator
# refuses, and rendering it as `true` would be a claim about a BEAM value
# the model does not know. It is an error, the same rule `is_nil/1` follows.
#
# The payload is `term()` because the module DECLARES it: the inference that
# reads a nil test as `term() | nil` only runs for a module that declares no
# @type msg, where the test is the only evidence there is.
defmodule Tag do
  use GenServer

  @type msg :: {:set, term()}
  @type state :: boolean()

  def handle_cast({:set, v}, _s), do: {:noreply, v != nil}
end
