(* Lowering: the core form of one instance to its LIR.

   Lowering reads a definition's core form, which gives every node's
   meaning, and writes LIR with every choice made:
   which instance each call reaches, how each argument is passed, which
   values move and which are copied, and where each owned local goes out of
   scope, on every path. It writes a [drop] wherever an owned value leaves
   its scope; drop elaboration then decides each one's remaining ownership. *)

(* A valid program stage0 cannot lower yet: the construct, and its position
   if one is known. It is not a compiler bug: the driver reports it as a
   limit of stage0. *)
type unsupported = { construct : string; at : Lir.site option }

exception Unsupported of unsupported

(* Lowering's inputs, each one of the type checker's queries or code
   generation's own tables. *)
type context

val env : context -> Memory_layout.env
val glue : context -> Glue.t
val monomorphic : context -> Monomorphic.context

val context :
  ?checks:bool ->
  ?cursor_fields:(context -> Ground.yielding -> (string * Memory_layout.member) list) ->
  ?constant:(context -> Path.t -> Lir.static_value option) ->
  Query.context ->
  Memory_layout.target ->
  context
(** The driver gives [cursor_fields], a pulled method's cursor fields, from its pulled lowering, and
    [constant] from whatever keeps each constant's lowering, so that each is made once and its
    readers are known. *)

(* The LIR of an instance of a function, a method, an [impl]'s method, or a
   test, before drop elaboration. *)
val instance : context -> Instance.key -> Lir.t

(* A constant's static data, where its value folds: literals, operators on
   numbers and on [Bool], other constants that fold, and records, variants,
   strings, lists, and arrays of parts that fold. Otherwise the type of the
   value its [Evaluator] computes. Folding gives exactly the result running
   would, and anything it does not know is run. *)
type constant = Folded of Lir.data | Run of Ground.ty

val constant : context -> Path.t -> constant

(* The [Evaluator] of a constant: its value computed and written out in
   its binary form. *)
val evaluator : context -> Path.t -> Lir.t

(* The pulled version of a yielding method, before drop elaboration: its
   body with each [yield] left in place for yield lowering, and the values a
   cursor that has not started owns, as [Yields.cursor_drop] takes it. *)
val pulled :
  context -> Ground.yielding -> Lir.function_ * (Lir.local * (Lir.local * int) option) list

(* A cursor's [next] result type: an [Option] of the method's yield type. *)
val cursor_result : context -> Ground.yielding -> Ground.ty

(* The parameters of the pulled version that are evidence, which are its
   last. A cursor does not hold them: its [next] takes them. *)
val pulled_evidence : context -> Ground.yielding -> Lir.function_ -> Lir.local list

(* A capability [impl]'s table of entries. *)
val table : context -> Instance.key -> Lir.table

(* The table of an [any] value of a type and trait. *)
val any_table : context -> Instance.key -> Lir.table

(* A capability's locking table, whose entries lock a mutex around the
   implementation's entries. *)
val locked_table : context -> Instance.key -> capability:Path.t -> Lir.table

(* The key of a test's instance. *)
val test_key : Path.t -> Instance.key

(* Code run while compiling, for a tagged template's check: a template of
   the literal texts and no parts, given to the tag's [from_template]'s
   clauses that can run, each evaluated and written out as a [Bool], in
   order. A clause that reads the template's parts is not asked of it; the
   prover asks only those that read its literals. *)
val template_check : context -> Instance.key -> from_template:Path.t -> texts:string list -> Lir.t

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check evaluates, in order. *)
val template_checked : context -> Path.t -> int list

(* Code run while compiling, for a call whose arguments are known: the
   function, which is not generic, called with each argument a constant, an
   integer or a [Bool] as 0 or 1, and its result written out. *)
val call_evaluation : context -> Instance.key -> function_:Path.t -> arguments:Z.t list -> Lir.t

module For_testing : sig
  val constant_value : context -> Path.t -> Lir.static_value option
  (** Another constant's value, where it folds. *)
end
