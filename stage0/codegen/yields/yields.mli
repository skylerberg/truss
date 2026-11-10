(* Yield lowering: turning a yielding method's LIR, with its [yield]
   terminators, into code with none.

   A method that is looped over takes the caller's loop body as its last
   parameter, a function value that returns whether to go on. A method that
   is pulled becomes a state machine: a [next] function over a cursor that
   holds the state number, the parameters, and the locals that are live
   across a [yield], and a drop function that ends the method at the [yield]
   it stopped at. Run this after drop elaboration, so the drops on a
   [yield]'s [stop] path are already in place. *)

(* The loop form. [body] is the type of the caller's loop body, whose result
   is a [Bool]: true to go on. A lending method's [yield] has no [stop], so
   it calls the body and always goes on. *)
val loop_form : Memory_layout.env -> body:Ground.function_type -> Lir.function_ -> Lir.function_

(* The fields of a cursor over the method: its state, a [UInt32], then each
   parameter, named as [Convention.cursor_parameter] names it, and each
   local live where a [yield] resumes or stops, named [local] and its
   number. This is the shape of the method's [Cursor] type. *)
val cursor_fields : Memory_layout.env -> Lir.function_ -> (string * Memory_layout.member) list

(* [next]: takes a writable pointer to the cursor, of type [cursor], and
   returns [result], the method's [Option] of what it yields, whose
   variants are [Some], with the field [value], and [None]. *)
val cursor_next :
  Memory_layout.env -> cursor:Ground.ty -> result:Ground.ty -> Lir.function_ -> Lir.function_

(* The cursor's drop function: in each state, the [stop] path of the
   [yield] the method stopped at; before it starts, a drop of each
   parameter in [owned]; once it has ended, nothing. *)
val cursor_drop :
  Memory_layout.env -> cursor:Ground.ty -> owned:Lir.local list -> Lir.function_ -> Lir.function_
