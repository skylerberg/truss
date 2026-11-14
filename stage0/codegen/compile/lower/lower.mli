(* A valid program stage0 cannot lower yet: the construct, and its position
   if one is known. It is not a compiler bug: the driver reports it as a
   limit of stage0. *)
type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

(* Lowering's inputs, each one of the type checker's queries or code
   generation's own tables. *)
type context

val env : context -> Memory_layout.env
val glue : context -> Glue.t
val monomorphic : context -> Monomorphic.context

val context :
  ?checks:bool ->
  constant:(context -> Path.t -> Lowered.static_value option) ->
  Query.context ->
  Memory_layout.target ->
  context

(* The C of an instance of a function, a method, an [impl]'s method, or a
   test. *)
val instance : context -> Instance.key -> Emit_c.Builder.instance

(* A constant's static data, where its value folds: literals, operators on
   numbers and on [Bool], other constants that fold, and records, variants,
   strings, lists, and arrays of parts that fold. Otherwise the type of the
   value its [Evaluator] computes. Folding gives exactly the result running
   would, and anything it does not know is run. *)
type constant = Folded of Lowered.data | Run of Ground.ty

val constant : context -> Path.t -> constant

(* The [Evaluator] of a constant: its value computed and written out in
   its binary form. *)
val evaluator : context -> Path.t -> Emit_c.Builder.instance

(* A capability [impl]'s table of entries. *)
val table : context -> Instance.key -> Lowered.table

(* The table of an [any] value of a type and trait. *)
val any_table : context -> Instance.key -> Lowered.table

(* A capability's locking table, whose entries lock a mutex around the
   implementation's entries. *)
val locked_table : context -> Instance.key -> capability:Path.t -> Lowered.table

(* The key of a test's instance. *)
val test_key : Path.t -> Instance.key

val template_check :
  context -> Instance.key -> from_template:Path.t -> texts:string list -> Emit_c.Builder.instance

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check evaluates, in order. *)
val template_checked : context -> Path.t -> int list

(* Code run while compiling, for a call whose arguments are known: the
   function, which is not generic, called with each argument a constant, an
   integer or a [Bool] as 0 or 1, and its result written out. *)
val call_evaluation :
  context -> Instance.key -> function_:Path.t -> arguments:Z.t list -> Emit_c.Builder.instance

module For_testing : sig
  val constant_value : context -> Path.t -> Lowered.static_value option
  (** Another constant's value, where it folds. *)
end
