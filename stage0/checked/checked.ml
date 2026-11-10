type local = Syntax.id

type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }
  | Bound
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

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  meanings : meaning option array;
  calls : call option array;
}

let show_meaning = function
  | Local_value local -> Printf.sprintf "local %d" local
  | Global { path; _ } -> Path.show path
  | Field_read { field; _ } -> "field " ^ field
  | Variant_value { variant; _ } -> "variant " ^ variant
  | Type_name type_ -> "type " ^ Types.show type_
  | Generic_value parameter -> "generic " ^ parameter.name
  | Specification_value -> "specification"
