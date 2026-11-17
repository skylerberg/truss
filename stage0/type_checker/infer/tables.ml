type local = Syntax.id

type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }
  | Bound
  | Dynamic
  | Built_in

type callee =
  | Function of {
      path : Path.t;
      type_arguments : Types.argument list;
      capability_arguments : Types.capability_set list;
    }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      capability_arguments : Types.capability_set list;
      evidence : evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Indirect
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Built_in_operator

type argument = { expression : Syntax.id; core_argument_index : int; mode : Types.mode }

type call = {
  callee : callee;
  arguments : argument list;
  omitted_defaults : string list;
  callee_result : Types.ty;
}

type resolution =
  | Local_value of local
  | Global of {
      path : Path.t;
      type_arguments : Types.argument list;
      capability_arguments : Types.capability_set list;
    }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

let show_resolution = function
  | Local_value local -> Printf.sprintf "local %d" local
  | Global { path; _ } -> Path.show path
  | Field_access { field; _ } -> "field " ^ field
  | Variant_value { variant; _ } -> "variant " ^ variant
  | Type_name type_ -> "type " ^ Types.show type_
  | Value_parameter parameter -> "generic " ^ parameter.name
  | Specification_value -> "specification"

type literal = Integer_value of Z.t | Float_value of float

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Elements of { count : call; element : call; lends : Types.mode }
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
  lend_modes : Types.mode option array;
}

let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    resolutions = Array.make size None;
    calls = Array.make size None;
    literals = Array.make size None;
    patterns = Array.make size None;
    scrutinee_types = Array.make size None;
    loops = Array.make size None;
    templates = Array.make size None;
    lend_modes = Array.make size None;
  }

let copy tables =
  {
    types = Array.copy tables.types;
    local_types = Array.copy tables.local_types;
    resolutions = Array.copy tables.resolutions;
    calls = Array.copy tables.calls;
    literals = Array.copy tables.literals;
    patterns = Array.copy tables.patterns;
    scrutinee_types = Array.copy tables.scrutinee_types;
    loops = Array.copy tables.loops;
    templates = Array.copy tables.templates;
    lend_modes = Array.copy tables.lend_modes;
  }

let publish (tables : t) : published =
  {
    types = tables.types;
    local_types = tables.local_types;
    resolutions = tables.resolutions;
    callees =
      Array.map
        (function Some { callee = Function { path; _ }; _ } -> Some path | _ -> None)
        tables.calls;
  }
