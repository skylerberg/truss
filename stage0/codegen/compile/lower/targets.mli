val resolve_impl :
  Definitions.context ->
  Types.substitution ->
  trait:Types.trait_reference ->
  self_type:Types.ty ->
  evidence:Core.evidence ->
  Path.t * Ground.argument list

val make_trait_method_key :
  Definitions.context ->
  Types.substitution ->
  trait:Types.trait_reference ->
  name:string ->
  receiver:Path.receiver ->
  self_type:Types.ty ->
  type_arguments:Types.argument list ->
  evidence:Core.evidence ->
  Instance.key

val pass : Lowering.state -> Types.mode -> Ground.ty -> Lowered.place -> Lowered.operand option
val lookup_capability_method : Definitions.context -> Path.t -> string -> int * Types.signature

val make_entry_signature :
  Definitions.context -> Types.signature -> Lowered.signature * Convention.result

val list_any_methods : Definitions.context -> Path.t -> Types.trait_method list
val lookup_dynamic_method : Definitions.context -> Path.t -> string -> int * Types.signature
val is_copyable_any : Definitions.context -> Types.trait_reference -> bool

val make_any_entry_signature :
  Definitions.context ->
  any:Types.trait_reference ->
  trait:Path.t ->
  Types.signature ->
  Lowered.signature * Convention.result * Path.t list

val lower_implementation_evidence :
  Lowering.state ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  implementation:Lowered.operand ->
  Lowered.operand

val lookup_evidence : Lowering.state -> Path.t -> Lowered.operand

val lower_nested_function :
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

val lower_indirect_call :
  Lowering.state ->
  function_type:Ground.function_type ->
  value:Lowered.place ->
  Lowered.place list ->
  Lowered.place ->
  unit

val lower_call_through_any :
  Lowering.state ->
  any_type:Types.trait_reference ->
  trait:Path.t ->
  name:string ->
  any:Lowered.place ->
  arguments:(Types.mode * Ground.ty * Lowered.place) list ->
  ?lending:Lowered.operand list ->
  Lowered.place ->
  unit

val make_any_substitution :
  Definitions.context -> any:Types.trait_reference -> Path.t -> Types.substitution

val run_in_type_definition :
  Lowering.state -> source:Resolve.Names.key -> Ground.ty -> (unit -> 'a) -> 'a

val begin_output : Lowering.state -> Lowered.place
val echo : Lowering.state -> Lowered.place -> Ground.ty -> site:Lowered.site -> unit

val lower_any_into :
  Lowering.state ->
  any_ty:Ground.ty ->
  inner_ty:Ground.ty ->
  impl:Path.t ->
  type_arguments:Ground.argument list ->
  value:Lowered.place ->
  Lowered.place ->
  unit

val lower_provided_evidence :
  Lowering.state ->
  implementation:Lowered.operand ->
  ('a * Path.t * Types.substitution) list ->
  ('a * Lowered.operand) list

val lower_instance_call :
  Lowering.state ->
  Instance.key ->
  signature:Types.signature ->
  substitution:Types.substitution ->
  arguments:(Types.mode * Ground.ty * Lowered.place) list ->
  ?mask:int ->
  ?lending:Lowered.operand list ->
  destination:Lowered.place ->
  unit ->
  unit

type literal = Integer_value of Z.t | Float_value of float

val lower_literal : Lowering.state -> Ground.ty -> literal -> Lowered.operand
val lower_literal_place : Lowering.state -> Ground.ty -> string -> Lowered.place
val lower_static_constant : Lowering.state -> Path.t -> Lowered.place
val read_list_parts : Monomorphic.context -> Ground.ty -> string * Ground.ty * Ground.ty

val lower_template_value :
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
