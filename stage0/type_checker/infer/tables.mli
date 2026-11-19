type local = Syntax.id

type callee =
  | Function of { path : Path.t; instantiation : Types.instantiation }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      instantiation : Types.instantiation;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Indirect
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Built_in_operator

type argument = { expression : Syntax.id; core_argument_index : int; mode : Language.Mode.t }

type call = {
  callee : callee;
  arguments : argument list;
  omitted_defaults : string list;
  callee_result : Types.ty;
}

type resolution =
  | Local_value of local
  | Global of { path : Path.t; instantiation : Types.instantiation }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

val show_resolution : resolution -> string

type literal = Integer_value of Z.t | Float_value of float

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Elements of { count : call; element : call; lends : Language.Mode.t }
  | Pulled of { cursor : Types.ty; cursor_call : call option; remaining : call option }

type pattern =
  | Variant_pattern of { type_ : Types.ty; variant : string }
  | Record_pattern of { type_ : Types.ty }
  | Constant_pattern of Path.t
  | Literal_pattern of literal
  | Other_pattern

type template = {
  from_template : call option;
  part_conversions : call option list;
  interpolated : bool;
}

type published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  calls : call option array;
  literals : literal option array;
  patterns : pattern option array;
  scrutinee_types : Types.ty option array;
  loops : loop option array;
  templates : template option array;
  lend_modes : Language.Mode.t option array;
}

val create : int -> t
val copy : t -> t
val publish : t -> published
