val test : string -> (unit -> unit) -> unit
val list_fragment_diagnostics : Database.t -> Path.file -> Diagnostic.t list
val fail : ('a, unit, string, unit) format4 -> 'a
val expect_string : expected:String.t -> String.t -> unit
val expect_int : expected:int -> int -> unit
val render_records : Backend.Test_report.record list -> string
val definition : string -> Path.t
val named : ?arguments:Ground.argument list -> string -> Ground.ty
val int64 : Ground.ty
val bool : Ground.ty
val character : Ground.ty
val unit : Ground.ty
val text : Ground.ty
val pair : Ground.ty
val float64 : Ground.ty
val uint8 : Ground.ty
val option : Ground.ty -> Ground.ty
val list : Ground.ty -> Ground.ty
val array : Ground.ty -> int -> Ground.ty
val host : Libc.system
val field : 'a -> Ground.ty -> 'a * Memory_layout.member

val variant :
  ?indirect:bool -> string -> (string * Memory_layout.member) list -> Memory_layout.variant_shape

val compute_shape : (string * Memory_layout.shape) list -> Ground.ty -> Memory_layout.shape
val lay_out : ?extra:(string * Memory_layout.shape) list -> Ground.ty -> Memory_layout.t
val describe : ?extra:(string * Memory_layout.shape) list -> Ground.ty -> string
val int32 : Ground.ty
val uint64 : Ground.ty

type local_info
type block
type function_
type program_fragment = Memory_layout.env -> Emit_c.fragment

val local : ?name:string -> Lowered.ty -> local_info
val value : Ground.ty -> Lowered.ty
val at : ?projections:Lowered.projection list -> Lowered.local -> Lowered.place
val copy : ?projections:Lowered.projection list -> Lowered.local -> Lowered.operand
val constant_int32 : int -> Lowered.operand
val constant_int64 : int -> Lowered.operand
val block : Lowered.statement list -> Lowered.terminator -> block

val function_ :
  ?parameters:Lowered.local list ->
  ?result:Lowered.ty ->
  ?environment:(string * Lowered.ty) list ->
  local_info list ->
  block list ->
  function_

val code_item : string -> Lowered.Item.t
val define_function : ?nested:function_ list -> string -> function_ -> program_fragment
val entry : ?nested:function_ list -> local_info list -> block list -> program_fragment
val make_program_fragment : Emit_c.fragment -> program_fragment

val call :
  string ->
  ?result:Lowered.ty option ->
  ?parameters:Lowered.ty list ->
  Lowered.operand list ->
  Lowered.place option ->
  Lowered.statement

val make_shape_env : ?extra:(string * Memory_layout.shape) list -> unit -> Memory_layout.env
val scratch : string lazy_t
val c_compiler : C_compiler.t lazy_t
val counter : int ref
val list_worker_counts : unit -> int list

val run_program :
  ?extra:(string * Memory_layout.shape) list ->
  ?env:Memory_layout.env ->
  ?input:string ->
  program_fragment list ->
  int * string * string

val expect_status :
  ?extra:(string * Memory_layout.shape) list -> int -> program_fragment list -> unit

val example : Path.module_
val example_file : Path.file
val make_database : Project.package list -> Database.t
val make_example_package : (Path.file * string) list -> Project.package list

val make_backend :
  ?results:Backend.results ->
  ?evaluation_time_limit_ms:int ->
  ?profile:Backend.profile ->
  Database.t ->
  Backend.t

val load_files :
  ?results:Backend.results ->
  ?roots:Lowered.Item.t list ->
  ?profile:Backend.profile ->
  (Path.file * string) list ->
  Database.t * Backend.t

val load :
  ?results:Backend.results ->
  ?roots:Lowered.Item.t list ->
  ?profile:Backend.profile ->
  string ->
  Database.t * Backend.t

val list_tests_in : Database.t -> Path.module_ -> Path.t list
val list_tests : Database.t -> Path.t list
val run_source : string -> string
val expect_output : string -> String.t -> unit
val expect_pass : string -> string -> unit
val run_main : ?arguments:string list -> ?input:string -> string -> int * string * string
val drop_shapes : (string * Memory_layout.shape) list
val standard_context : Monomorphic.context
val make_standard_type : string -> string -> ?arguments:Ground.argument list -> unit -> Ground.ty
val show_standard_layout : Ground.ty -> string
