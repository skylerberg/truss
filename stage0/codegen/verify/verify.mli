(* Checks every instance's LIR must pass, and every build's instances must
   pass together, so that a mistake in lowering or in a pass is a compiler
   bug reported here, with the instance it is in, rather than C that is
   wrong in a way the C compiler cannot see: each instance is its own C
   file, which declares its callees from its own side. *)

(* One instance, once its passes have run:
   - every block a terminator goes to and every local a place names exists,
     and every place fits the type it projects from
   - no [yield] is left
   - nothing is moved out of a constant's static data
   - a function with a result returns one on every [return], and one
     without returns none
   - a call gives its target as many arguments as the target's signature
     takes, and writes a large result to a place it does not also pass by
     address, since every pointer a callee is given is [restrict]
   - a value that has a size is built as a record or a variant its type
     has, with fields the type has
   - a call of a nested function, or a function value made of one, names it
     with the signature it has *)
val instance : Memory_layout.env -> Lir.t -> unit
