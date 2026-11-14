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

val pass : Lowering.state -> Types.mode -> Ground.ty -> Lowered.place -> Lowered.operand option
val capability_method : Definitions.context -> Path.t -> string -> int * Types.signature

val entry_signature :
  Definitions.context -> Types.signature -> Lowered.signature * Convention.result

val any_methods : Definitions.context -> Path.t -> Types.trait_method list
val dynamic_slot : Definitions.context -> Path.t -> string -> int * Types.signature

val any_entry_signature :
  Definitions.context ->
  any:Types.trait_reference ->
  trait:Path.t ->
  Types.signature ->
  Lowered.signature * Convention.result * Path.t list

val implementation_evidence :
  Lowering.state ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  implementation:Lowered.operand ->
  Lowered.operand

val evidence_of : Lowering.state -> Path.t -> Lowered.operand

val nested_function :
  Lowering.state ->
  function_type:Ground.function_type ->
  output:Types.result option ->
  captures:(Lowered.place * Ground.ty) list ->
  body:
    (Lowering.state ->
    captures:Lowered.place list ->
    (Lowered.place * Ground.mode * Ground.ty) list ->
    unit) ->
  Lowered.place ->
  unit

val call_indirect :
  Lowering.state ->
  function_type:Ground.function_type ->
  value:Lowered.place ->
  Lowered.place list ->
  Lowered.place ->
  unit

val call_through_any :
  Lowering.state ->
  any_type:Types.trait_reference ->
  trait:Path.t ->
  name:string ->
  any:Lowered.place ->
  arguments:(Types.mode * Ground.ty * Lowered.place) list ->
  Lowered.place ->
  unit

val in_type_definition : Lowering.state -> Ground.ty -> (unit -> 'a) -> 'a
val echo : Lowering.state -> Lowered.place -> Ground.ty -> site:Lowered.site -> unit

val any_into :
  Lowering.state ->
  any_ty:Ground.ty ->
  inner_ty:Ground.ty ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  value:Lowered.place ->
  Lowered.place ->
  unit

val provided_evidence :
  Lowering.state ->
  implementation:Lowered.operand ->
  ('a * Path.t * Types.substitution) list ->
  ('a * Lowered.operand) list

val call_instance :
  Lowering.state ->
  Instance.key ->
  signature:Types.signature ->
  substitution:Types.substitution ->
  arguments:(Types.mode * Ground.ty * Lowered.place) list ->
  ?mask:int ->
  destination:Lowered.place ->
  unit ->
  unit

type literal = Integer_value of Z.t | Float_value of float

val constant_of : Lowering.state -> Ground.ty -> literal -> Lowered.operand
val string_literal : Lowering.state -> Ground.ty -> string -> destination:Lowered.place -> unit
val static_constant : Lowering.state -> Path.t -> Lowered.place

val list_parts : Monomorphic.context -> Ground.ty -> string * Ground.ty * Ground.ty
(** A [List]'s storage field, the storage's type, and the element type. *)

val template_value :
  Lowering.state ->
  Ground.ty ->
  string list ->
  site:Lowered.site ->
  parts:(Lowered.place -> unit) list ->
  Lowered.place

val pull_loop :
  Lowering.state ->
  option:Ground.ty ->
  call_next:(Lowered.place -> unit) ->
  body:(Lowered.place -> unit) ->
  unit
