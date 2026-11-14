val test : string -> (unit -> unit) -> unit
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
val target_64 : Memory_layout.target
val target_32 : Memory_layout.target
val field : 'a -> Ground.ty -> 'a * Memory_layout.member

val variant :
  ?indirect:bool -> string -> (string * Memory_layout.member) list -> Memory_layout.variant_shape

val shapes : (string * Memory_layout.shape) list -> Ground.ty -> Memory_layout.shape

val layout :
  ?target:Memory_layout.target ->
  ?extra:(string * Memory_layout.shape) list ->
  Ground.ty ->
  Memory_layout.t

val describe :
  ?target:Memory_layout.target -> ?extra:(string * Memory_layout.shape) list -> Ground.ty -> string

val int32 : Ground.ty
val usize : Ground.ty

(* A function written by hand, and an instance written as C once the
   layouts it is printed with are known. *)
type local_info
type block
type function_
type instance = Memory_layout.env -> Emit_c.Builder.instance

val local : ?name:string -> Lir.ty -> local_info
val value : Ground.ty -> Lir.ty
val at : ?projections:Lir.projection list -> Lir.local -> Lir.place
val copy : ?projections:Lir.projection list -> Lir.local -> Lir.operand
val constant_int32 : int -> Lir.operand
val constant_int64 : int -> Lir.operand
val block : Lir.statement list -> Lir.terminator -> block

val function_ :
  ?parameters:Lir.local list ->
  ?result:Lir.ty ->
  ?returns:bool ->
  ?environment:(string * Lir.ty) list ->
  local_info list ->
  block list ->
  function_

val key : string -> Instance.key
val instance : ?nested:function_ list -> string -> function_ -> instance
val entry : ?nested:function_ list -> local_info list -> block list -> instance

(* An instance already written as C. *)
val printed : Emit_c.Builder.instance -> instance

val call :
  string ->
  ?result:Lir.ty option ->
  ?parameters:Lir.ty list ->
  Lir.operand list ->
  Lir.place option ->
  Lir.statement

val shape_env : ?extra:(string * Memory_layout.shape) list -> unit -> Memory_layout.env
val scratch : string lazy_t
val compiler : Toolchain.t lazy_t
val strict : string list
val counter : int ref
val cache : Build.cache lazy_t
val settings : Build.settings
val worker_counts : int list

val run_program :
  ?extra:(string * Memory_layout.shape) list ->
  ?env:Memory_layout.env ->
  ?anchors:Positions.anchor list ->
  ?input:string ->
  instance list ->
  int * string * string

val expect_status :
  ?extra:(string * Memory_layout.shape) list ->
  ?anchors:Positions.anchor list ->
  int ->
  instance list ->
  unit

val example : Path.module_
(** The root module of the package [example]. *)

val example_file : Path.file
(** [example/main.truss], the file {!load} gives its text. *)

val checked_standard : Engine.t lazy_t
val load_files : ?results:Compile.results -> (Path.file * string) list -> Query.context * Compile.t
val load : ?results:Compile.results -> string -> Query.context * Compile.t
val tests_in : Query.context -> Path.module_ -> Path.t list
val tests_of : Query.context -> Path.t list
val run_source : string -> string
val expect_output : string -> String.t -> unit
val passes : string -> string -> unit

val run_main :
  ?arguments:string list -> ?input:string -> ?in_order:bool -> string -> int * string * string

val drop_shapes : (string * Memory_layout.shape) list
val standard_context : Monomorphic.context
val standard : string -> string -> ?arguments:Ground.argument list -> unit -> Ground.ty
val standard_layout : Ground.ty -> string
