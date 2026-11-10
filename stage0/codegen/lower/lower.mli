(* Lowering: the checked form of one instance to its LIR.

   Lowering reads a definition's syntax tree with its checked form's tables,
   which say what every node means, and writes LIR with every choice made:
   which instance each call reaches, how each argument is passed, which
   values move and which are copied, and where each owned local goes out of
   scope, on every path. It writes a [drop] wherever an owned value leaves
   its scope; drop elaboration then decides what each still owns. *)

(* What lowering reads, each one of the type checker's queries or code
   generation's own tables. *)
type context = {
  database : Query.context;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  cursor_fields : (Ground.yielding -> (string * Memory_layout.member) list) ref;
      (** The fields of a pulled method's cursor, which the driver gives from its pulled lowering *)
  checks : bool;
      (** Whether the program checks at run time what the prover would prove: [requires] clauses,
          integer overflow, and division *)
  evaluate : (Path.t -> Ground.ty -> Lir.static_value) ref;
      (** A constant's value, worked out by running its [Evaluator], which the driver builds and
          runs, for a constant whose value is not folded while compiling *)
}

val context : ?checks:bool -> Query.context -> Memory_layout.target -> context

(* The LIR of an instance of a function, a method, an [impl]'s method, or a
   test, before drop elaboration. *)
val instance : context -> Instance.key -> Lir.t

(* A constant's static data: its value worked out exactly from its
   constant expression, or by running its [Evaluator] through the context's
   [evaluate]. *)
val constant : context -> Path.t -> Lir.data

(* The [Evaluator] of a constant: its value worked out and written out in
   its binary form. *)
val evaluator : context -> Path.t -> Lir.t

(* The pulled version of a yielding method, before drop elaboration: its
   body with each [yield] left in place for yield lowering, and what a
   cursor that has not started owns, as [Yields.cursor_drop] takes it. *)
val pulled :
  context -> Ground.yielding -> Lir.function_ * (Lir.local * (Lir.local * int) option) list

(* What a cursor's [next] returns: an [Option] of what the method yields. *)
val cursor_result : context -> Ground.yielding -> Ground.ty

(* A capability [impl]'s table of entries. *)
val table : context -> Instance.key -> Lir.table

(* The table of an [any] value of a type and trait. *)
val any_table : context -> Instance.key -> Lir.table

(* The evidence for the real implementation of a standard capability. *)
val real_evidence : context -> Path.t -> Lir.evidence

(* The key of a test's instance. *)
val test_key : Path.t -> Instance.key

(* Code run while compiling, for a tagged template's check: a template of
   the literal texts and no parts, given to the tag's [from_template]'s
   clauses that can run, each worked out and written out as a [Bool]. *)
val template_check : context -> Instance.key -> from_template:Path.t -> texts:string list -> Lir.t

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check works out, in order. *)
val template_checked : context -> Path.t -> int list
