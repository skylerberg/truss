val resolve_impl :
  Lowering.state ->
  trait:Types.trait_reference ->
  self_type:Types.ty ->
  evidence:Core.evidence ->
  Path.t * Ground.argument list

val trait_method_key :
  Lowering.state ->
  trait:Types.trait_reference ->
  name:string ->
  receiver:Path.receiver ->
  self_type:Types.ty ->
  type_arguments:Types.argument list ->
  evidence:Core.evidence ->
  Instance.key

val pass : Lowering.state -> Types.mode -> Ground.ty -> Lir.place -> Lir.operand option
val capability_method : Definitions.context -> Path.t -> string -> int * Types.signature
val entry_signature : Definitions.context -> Types.signature -> Lir.signature * Convention.result
val any_methods : Definitions.context -> Path.t -> Types.trait_method list
val dynamic_slot : Definitions.context -> Path.t -> string -> int * Types.signature

val any_entry_signature :
  Definitions.context ->
  any:Types.trait_reference ->
  trait:Path.t ->
  Types.signature ->
  Lir.signature * Convention.result * Path.t list

val implementation_evidence :
  Lowering.state ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  implementation:Lir.operand ->
  Lir.operand

val evidence_of : Lowering.state -> Path.t -> Lir.operand
val cursor_evidence : Definitions.context -> Ground.yielding -> Path.t list

val cursor_into :
  Lowering.state ->
  path:Path.t ->
  type_arguments:Ground.argument list ->
  signature:Types.signature ->
  arguments:(Types.mode * Ground.ty * Lir.place) list ->
  mask:int ->
  Lir.place ->
  unit

val nested_function :
  Lowering.state ->
  function_type:Ground.function_type ->
  output:Types.result option ->
  captures:('key * Lir.place * Ground.ty) list ->
  bind_capture:(Lowering.state -> 'key -> Lir.place -> unit) ->
  body:(Lowering.state -> (Lir.place * Ground.mode * Ground.ty) list -> unit) ->
  Lir.place ->
  unit

val call_indirect :
  Lowering.state ->
  function_type:Ground.function_type ->
  value:Lir.place ->
  Lir.place list ->
  Lir.place ->
  unit

val call_through_any :
  Lowering.state ->
  any_type:Types.trait_reference ->
  trait:Path.t ->
  name:string ->
  any:Lir.place ->
  arguments:(Types.mode * Ground.ty * Lir.place) list ->
  Lir.place ->
  unit

val in_type_definition : Lowering.state -> Ground.ty -> (unit -> 'a) -> 'a
val echo : Lowering.state -> Lir.place -> Ground.ty -> site:Lir.site -> unit

val any_into :
  Lowering.state ->
  any_ty:Ground.ty ->
  inner_ty:Ground.ty ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  value:Lir.place ->
  Lir.place ->
  unit

val provided_evidence :
  Lowering.state ->
  implementation:Lir.operand ->
  ('a * Path.t * Types.substitution) list ->
  ('a * Lir.operand) list

val call_instance :
  Lowering.state ->
  Instance.key ->
  signature:Types.signature ->
  substitution:Types.substitution ->
  arguments:(Types.mode * Ground.ty * Lir.place) list ->
  ?mask:int ->
  destination:Lir.place ->
  unit ->
  unit

type literal = Integer_value of Z.t | Float_value of float

val constant_of : Lowering.state -> Ground.ty -> literal -> Lir.operand
val string_literal : Lowering.state -> Ground.ty -> string -> destination:Lir.place -> unit
val static_constant : Lowering.state -> Path.t -> Lir.place

val list_parts : Monomorphic.context -> Ground.ty -> string * Ground.ty * Ground.ty
(** A [List]'s storage field, the storage's type, and the element type. *)

val template_value :
  Lowering.state ->
  Ground.ty ->
  string list ->
  site:Lir.site ->
  parts:(Lir.place -> unit) list ->
  Lir.place

val yielded_type : Lowering.state -> Path.t -> Ground.argument list -> Ground.ty
val cursor_result : Definitions.context -> Ground.yielding -> Ground.ty
val call_next : Lowering.state -> Ground.yielding -> Lir.place -> Lir.place -> unit

val pull_loop :
  Lowering.state ->
  option:Ground.ty ->
  call_next:(Lir.place -> unit) ->
  body:(Lir.place -> unit) ->
  unit

val boxed_cursor : Lowering.state -> Ground.yielding -> Lir.place
