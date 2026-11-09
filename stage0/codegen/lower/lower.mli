(* Lowering: the checked form of one instance to its LIR. See CODEGEN.md,
   "Lowering expressions".

   Lowering reads a definition's syntax tree with its checked form's tables,
   which say what every node means, and writes LIR with every choice made:
   which instance each call reaches, how each argument is passed, which
   values move and which are copied, and where each owned local goes out of
   scope, on every path. It writes a [drop] wherever an owned value leaves
   its scope; drop elaboration then decides what each still owns. *)

(* What lowering reads, each one of the type checker's queries or code
   generation's own tables. *)
type context = {
  database : Query.database;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
}

val context : Query.database -> Memory_layout.target -> context

(* The LIR of an instance of a function, a method, an [impl]'s method, or a
   test, before drop elaboration. Raises [Invalid_argument] for an instance
   that is not code from source. *)
val instance : context -> Instance.key -> Lir.t

(* A constant's static data: its value worked out exactly from its
   constant expression. *)
val constant : context -> Path.t -> Lir.data

(* A capability [impl]'s table of entries. *)
val table : context -> Instance.key -> Lir.table

(* The evidence for the real implementation of a standard capability. *)
val real_evidence : context -> Path.t -> Lir.evidence

(* The key of a test's instance. *)
val test_key : Path.t -> Instance.key
