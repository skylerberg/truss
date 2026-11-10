(* Drop elaboration: deciding, at each point, which places still own a
   value, and dropping exactly those.

   Lowering writes [drop(place)] wherever an owned local goes out of scope,
   on every path out of that scope, including [return] and [?]: it means
   "drop whatever this place still owns here". This pass works out, by a
   dataflow analysis over the function's moves, what that is:

   - nothing, where the place was moved out on every path, and the drop is
     removed
   - all of it, where nothing was moved out
   - its remaining fields, each dropped on its own, where a field was moved
     out with [own], and the block of an [indirect] variant once its fields
     are gone
   - something only on some paths, and a drop flag, a [Bool] local set
     where the place is given a value and cleared where it is moved, decides
     at run time

   A write gives a place a value and drops nothing: whatever replaces a
   value drops it first, with a [drop] of its own, which is removed where
   the place holds nothing. So that this holds, and so that nothing is
   leaked, the pass checks what it is given, and a failure is a compiler
   bug:

   - no write is to a place that may still own a value
   - where the function returns, none of its locals owns a value still

   A [borrowed] local holds a value something else owns, and is left
   alone. Drops of types with nothing to drop are removed. A [yield]'s
   [stop] edge is an edge like any other, so a loop that stops at a
   [yield] drops what the method owns there. *)

val elaborate :
  Memory_layout.env ->
  needs_drop:(Ground.ty -> bool) ->
  environment:(int -> (string * Lir.ty) list) ->
  Lir.function_ ->
  Lir.function_
