val read_impl :
  Definitions.context ->
  Types.substitution ->
  trait:Types.trait_reference ->
  self_type:Types.ty ->
  evidence:Types.evidence ->
  Path.t * Ground.argument list

val find_trait_method :
  Definitions.context ->
  Types.substitution ->
  trait:Types.trait_reference ->
  name:string ->
  receiver:Path.receiver ->
  self_type:Types.ty ->
  instantiation:Types.instantiation ->
  evidence:Types.evidence ->
  (Path.t * Ground.instantiation) option

val pass : Lowering.state -> Language.Mode.t -> Ground.ty -> Lowered.place -> Lowered.operand option
val raise_lending_capability_method : Path.t -> string -> 'a
val lookup_capability_method : Definitions.context -> Path.t -> string -> int * Types.signature

val make_entry_signature :
  Definitions.context -> Types.signature -> Lowered.signature * Convention.result

val list_any_slots :
  Definitions.context ->
  self:Types.ty ->
  Types.trait_reference ->
  (Types.trait_reference * Types.trait_method) list

val lookup_dynamic_method :
  Definitions.context ->
  any:Types.trait_reference ->
  Path.t ->
  string ->
  Path.receiver ->
  int * Types.signature

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
  site:Lowered.site option ->
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
    (Lowered.place * Language.Mode.t * Ground.ty) list ->
    unit) ->
  Lowered.place ->
  unit

val lower_indirect_call :
  Lowering.state ->
  function_type:Ground.function_type ->
  value:Lowered.place ->
  site:Lowered.site option ->
  Lowered.place list ->
  Lowered.place ->
  unit

val lower_call_through_any :
  Lowering.state ->
  any_type:Types.trait_reference ->
  trait:Path.t ->
  name:string ->
  receiver:Path.receiver ->
  any:Lowered.place ->
  arguments:(Language.Mode.t * Ground.ty * Lowered.place) list ->
  ?lending:Lowered.operand list ->
  site:Lowered.site option ->
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
  site:Lowered.site option ->
  ('a * Path.t * Types.substitution) list ->
  ('a * Lowered.operand) list

val lower_item_call :
  Lowering.state ->
  Lowered.Item.t ->
  signature:Types.signature ->
  substitution:Types.substitution ->
  arguments:(Language.Mode.t * Ground.ty * Lowered.place) list ->
  ?lending:Lowered.operand list ->
  destination:Lowered.place ->
  site:Lowered.site option ->
  unit ->
  unit

type literal = Integer_value of Z.t | Float_value of float

val lower_literal : Lowering.state -> Ground.ty -> literal -> Lowered.operand

val make_static_literal :
  Monomorphic.context -> Ground.ty -> Language.Literal.t -> Lowered.static_value

val lower_literal_place : Lowering.state -> Ground.ty -> Language.Literal.t -> Lowered.place

val lower_owner_of_view :
  Lowering.state -> owner:Ground.ty -> view:Ground.ty -> Lowered.place -> Lowered.place -> unit

val lower_slice :
  Lowering.state ->
  element:Ground.ty ->
  buffer:Lowered.operand ->
  length:Lowered.operand ->
  Lowered.place

val lower_static_constant : Lowering.state -> Path.t -> Lowered.place
val read_list_parts : Monomorphic.context -> Ground.ty -> string * Ground.ty * Ground.ty

val pull_loop :
  Lowering.state ->
  option:Ground.ty ->
  call_next:(Lowered.place -> unit) ->
  body:(Lowered.place -> unit) ->
  unit
