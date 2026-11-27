type local = Syntax.id

type trait_method = {
  trait : Types.trait_reference;
  name : string;
  receiver : Path.receiver;
  self_type : Types.ty;
  instantiation : Types.instantiation;
}

type callee =
  | Function of { path : Path.t; instantiation : Types.instantiation }
  | Trait_method of trait_method
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Indirect
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }

type argument = {
  expression : Syntax.expression;
  core_argument_index : int;
  mode : Language.Mode.t;
}

type call = {
  callee : callee;
  arguments : argument list;
  omitted_defaults : string list;
  callee_result : Types.ty;
  lends : Language.Mode.t option;
}

type resolution =
  | Local_value of local
  | Global of { path : Path.t; instantiation : Types.instantiation }
  | Trait_method_value of trait_method
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

val show_resolution : resolution -> string

type literal = Integer_value of Z.t | Float_value of float
type element_access = Sequence_element | Lent_by_call of call

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Elements of { count : call; element : element_access; lends : Language.Mode.t }
  | Pulled of {
      cursor : Types.ty;
      cursor_call : call option;
      remaining : (Types.condition * call) option;
    }

type pattern =
  | Variant_pattern of {
      type_ : Types.ty;
      variant : string;
      fields : (string * Syntax.pattern) list;
    }
  | Record_pattern of { type_ : Types.ty; fields : (string * Syntax.pattern) list }
  | Binding_pattern of { local : Syntax.id; is_var : bool; mode : Language.Mode.t }
  | Constant_pattern of Path.t
  | Literal_pattern of Z.t

type template =
  | Interpolated of { displays : call list }
  | Tagged of {
      from_template : call;
      interpolation_type : Types.ty;
      conversions : call option list;
    }

type conversion =
  | From_never
  | Array_as_list
  | To_view
  | Function_widening
  | To_integer
  | From_integer

type specification_call =
  | Old
  | Identical
  | Final
  | Specification_function of Core.specification_function
  | Method_cost of {
      metric : Language.Metric.t;
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
    }

type literal_elements =
  | List_element of Types.ty
  | Map_entry of { key : Types.ty; value : Types.ty }

type elaboration =
  | Literal of literal
  | Template of template
  | Call of call
  | Specification_call of specification_call
  | Converted_literal of { elements : literal_elements; call : call }
  | Record_update of { paths : (Syntax.id * string list) list }
  | Lambda of { captures : (Syntax.id * Core.local) list }
  | Loop of loop
  | Discarded

type published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  scrutinee_types : Types.ty option array;
  resolutions : resolution option array;
  conversions : (conversion * Types.ty) list array;
  conditions : Types.condition option array;
  patterns : pattern option array;
  elaborations : elaboration option array;
}

val create : int -> t

val make_method_call :
  ?lends:Language.Mode.t ->
  Types.trait_reference ->
  Well_known.method_ ->
  self_type:Types.ty ->
  result:Types.ty ->
  (Syntax.expression * Language.Mode.t) list ->
  call

val find_call : t -> Syntax.id -> call option

val map :
  map_type:(Types.ty -> Types.ty) ->
  map_argument:(Types.argument -> Types.argument) ->
  map_capabilities:(Types.capability_set -> Types.capability_set) ->
  t ->
  t

val list_arguments_at : t -> Syntax.id -> Types.argument list
val exists_type : (Types.ty -> bool) -> t -> bool
val publish : t -> published
