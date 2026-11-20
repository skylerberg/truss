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
  | Literal_pattern of literal
  | Other_pattern

type template = {
  from_template : call option;
  part_conversions : call option list;
  interpolated : bool;
  part : Types.ty option;
}

type conversion =
  | From_never
  | Owned_to_view
  | View_to_owned
  | Function_widening
  | To_integer
  | From_integer

type specification_call =
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
  conditions : Types.condition option array;
  conversions : (conversion * Types.ty) list array;
  update_paths : (Syntax.id * string list) list option array;
  specification_calls : specification_call option array;
  captures : (Syntax.id * Core.local) list option array;
  literal_elements : literal_elements option array;
  discarded : bool array;
}

val create : int -> t
val copy : t -> t
val publish : t -> published
