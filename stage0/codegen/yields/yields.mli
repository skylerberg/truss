(* Yield lowering: turning a yielding method's LIR, with its [yield]
   terminators, into code with none.

   A method that is looped over takes the caller's loop body as its last
   parameter, a function value that returns whether to continue. A method that
   is pulled becomes a state machine: a [next] function over a cursor that
   holds the state number, the parameters, and the locals that are live
   across a [yield], and a drop function that ends the method at the [yield]
   it stopped at. Lowering has written the drops on a [yield]'s [stop]
   path. *)

(* The loop form. [body] is the type of the caller's loop body, whose result
   is a [Bool]: true to continue. A lending method's [yield] has no [stop], so
   it calls the body and always continues. *)

(* The fields of a cursor over the method: its state, a [UInt32], then each
   parameter that is not in [evidence], named as
   [Convention.cursor_parameter] names it, and each local live where a
   [yield] resumes or stops, named [local] and its number. This is the
   shape of the method's [Cursor] type. [evidence] is the method's
   parameters that are evidence, which a cursor does not hold. *)
val cursor_fields :
  Memory_layout.env ->
  evidence:Lir.local list ->
  Lir.function_ ->
  (string * Memory_layout.member) list

(* [next]: takes a writable pointer to the cursor, of type [cursor], then
   the method's evidence, and returns [result], the method's [Option] of
   its yield type, whose variants are [Some], with the field [value], and
   [None]. *)
val cursor_next :
  Memory_layout.env ->
  cursor:Ground.ty ->
  result:Ground.ty ->
  evidence:Lir.local list ->
  Lir.function_ ->
  Lir.function_

(* The cursor's drop function: in each state, the [stop] path of the
   [yield] the method stopped at; before it starts, a drop of each
   parameter in [owned]; once it has ended, nothing. A parameter in
   [owned] with a mask's local and a bit is one with a default: its
   argument is there, to drop, only when the mask has that bit. *)
val cursor_drop :
  Memory_layout.env ->
  cursor:Ground.ty ->
  owned:(Lir.local * (Lir.local * int) option) list ->
  evidence:Lir.local list ->
  Lir.function_ ->
  Lir.function_

module For_testing : sig
  val loop_form : Memory_layout.env -> body:Ground.function_type -> Lir.function_ -> Lir.function_
end
