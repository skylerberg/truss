type local = Syntax.id

type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }
  | Bound of Types.parameter
  | Dynamic
  | Built_in

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Function_value
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Built_in_operator

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

type argument = {
  expression : Syntax.id;
  parameter : int;
  mode : Types.mode;
  conversion : conversion option;
}

type call = {
  callee : callee;
  arguments : argument list;
  defaults_left_out : string list;
  uses : Types.capability list;
  capability_arguments : (Types.parameter * Types.capability list) list;
  result : Types.ty;
}

type meaning =
  | Local_value of local
  | Global of { path : Path.t; type_arguments : Types.argument list }
  | Field_read of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Generic_value of Types.parameter
  | Specification_value

type literal = Integer_value of Z.t | Float_value of float

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Yielding of { call : call; mode : Types.mode }
  | Pulled of { cursor : Types.ty }

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

type obligation =
  | Disjoint of { first : Syntax.id; second : Syntax.id }
  | Integer_fits of { expression : Syntax.id; type_ : Types.ty }
  | Costs_imply of {
      expression : Syntax.id;
      given : Types.function_type;
      expected : Types.function_type;
    }
  | Guards_cover of { match_ : Syntax.id }

type provide = { implementations : (Syntax.id * (Path.t * Path.t) list) list }

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  meanings : meaning option array;
  calls : call option array;
  literals : literal option array;
  patterns : pattern option array;
  pattern_types : Types.ty option array;
  loops : loop option array;
  templates : template option array;
  captures : local list option array;
  own_operator : bool array;
  provides : provide option array;
  obligations : obligation list;
}

let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    meanings = Array.make size None;
    calls = Array.make size None;
    literals = Array.make size None;
    patterns = Array.make size None;
    pattern_types = Array.make size None;
    loops = Array.make size None;
    templates = Array.make size None;
    captures = Array.make size None;
    own_operator = Array.make size false;
    provides = Array.make size None;
    obligations = [];
  }

let show_meaning = function
  | Local_value local -> Printf.sprintf "local %d" local
  | Global { path; _ } -> Path.show path
  | Field_read { field; _ } -> "field " ^ field
  | Variant_value { variant; _ } -> "variant " ^ variant
  | Type_name type_ -> "type " ^ Types.show type_
  | Generic_value parameter -> "generic " ^ parameter.name
  | Specification_value -> "specification"
