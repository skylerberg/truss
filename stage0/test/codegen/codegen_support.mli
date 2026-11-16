val test : string -> (unit -> unit) -> unit
val diagnostics : Database.t -> Path.file -> Diagnostic.t list
val fail : ('a, unit, string, unit) format4 -> 'a
val expect_string : expected:String.t -> String.t -> unit
val contains : string -> string -> bool
val expect_int : expected:int -> int -> unit
val render_records : Compile.record list -> string
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

val shapes : (string * Memory_layout.shape) list -> Ground.ty -> Memory_layout.shape
val computed_env : Libc.system -> (Ground.ty -> Memory_layout.shape) -> Memory_layout.env
val layout : ?extra:(string * Memory_layout.shape) list -> Ground.ty -> Memory_layout.t
val describe : ?extra:(string * Memory_layout.shape) list -> Ground.ty -> string
val int32 : Ground.ty
val uint64 : Ground.ty

type local_info
type block
type function_
type instance = Memory_layout.env -> Emit_c.Builder.instance

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
  ?returns:bool ->
  ?environment:(string * Lowered.ty) list ->
  local_info list ->
  block list ->
  function_

val key : string -> Instance.key
val instance : ?nested:function_ list -> string -> function_ -> instance
val entry : ?nested:function_ list -> local_info list -> block list -> instance
val printed : Emit_c.Builder.instance -> instance

val call :
  string ->
  ?result:Lowered.ty option ->
  ?parameters:Lowered.ty list ->
  Lowered.operand list ->
  Lowered.place option ->
  Lowered.statement

val shape_env : ?extra:(string * Memory_layout.shape) list -> unit -> Memory_layout.env
val scratch : string lazy_t
val compiler : Toolchain.t lazy_t
val strict : string list lazy_t
val counter : int ref
val cache : Build.cache lazy_t
val settings : Build.settings lazy_t
val worker_counts : int list

val run_program :
  ?extra:(string * Memory_layout.shape) list ->
  ?env:Memory_layout.env ->
  ?input:string ->
  instance list ->
  int * string * string

val expect_status : ?extra:(string * Memory_layout.shape) list -> int -> instance list -> unit
val example : Path.module_
val example_file : Path.file
val database : Project.package list -> Database.t
val example_package : (Path.file * string) list -> Project.package list
val compile : ?results:Compile.results -> ?evaluation_time_limit_ms:int -> Database.t -> Compile.t

val load_files :
  ?results:Compile.results ->
  ?roots:Instance.key list ->
  (Path.file * string) list ->
  Database.t * Compile.t

val load : ?results:Compile.results -> ?roots:Instance.key list -> string -> Database.t * Compile.t
val tests_in : Database.t -> Path.module_ -> Path.t list
val tests_of : Database.t -> Path.t list
val run_source : string -> string
val expect_output : string -> String.t -> unit
val passes : string -> string -> unit
val run_main : ?arguments:string list -> ?input:string -> string -> int * string * string
val drop_shapes : (string * Memory_layout.shape) list
val standard_context : Monomorphic.context
val standard : string -> string -> ?arguments:Ground.argument list -> unit -> Ground.ty
val standard_layout : Ground.ty -> string
