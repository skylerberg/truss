type mode = Read | Mut | Own
type parameter = { owner : Path.t; name : string }
type literal_kind = Integer_literal | Float_literal

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Parameter of parameter
  | Projection of { base : ty; trait : trait_reference; name : string }
  | Function of function_type
  | Any of trait_reference
  | Cursor of { method_ : Path.t; arguments : argument list }
  | Never
  | Integer
  | Variable of int
  | Literal of literal_kind * int
  | Hole
  | Error

and argument = Type of ty | Value of value | Capabilities of capability list
and value = Known of Z.t | Value_parameter of parameter | Value_variable of int

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;
}

and function_type = {
  inputs : (mode * ty) list;
  output : result;
  uses : capability list;
  costs : cost list;
}

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty
and capability = Capability of Path.t | Capability_parameter of parameter
and cost = { amortized : bool; resource : string; bound : cost_bound }

(* A function type's parameters have no names, so its bounds are
   constants: the number, when it is written as one. *)
and cost_bound = Finite_cost | Order_of | No_more_than of Z.t option | Exactly_cost of Z.t option

let builtin builtin = Named { path = Intrinsic.builtin_path builtin; arguments = [] }
let unit = builtin Unit
let bool = builtin Bool
let named path arguments = Named { path; arguments = List.map (fun type_ -> Type type_) arguments }

let builtin_of = function
  | Named { path; arguments = [] } -> Intrinsic.builtin_of_path path
  | Named { path; _ } -> (
      match Intrinsic.builtin_of_path path with
      | Some (Array | Storage | View) as found -> found
      | _ -> None)
  | _ -> None

let is_builtin wanted type_ = builtin_of type_ = Some wanted

let integer_types : Intrinsic.builtin list =
  [ Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; USize; ISize ]

let float_types : Intrinsic.builtin list = [ Float32; Float64 ]

let is_integer_type type_ =
  match builtin_of type_ with Some found -> List.mem found integer_types | None -> false

let is_signed type_ =
  match builtin_of type_ with Some (Int8 | Int16 | Int32 | Int64 | ISize) -> true | _ -> false

let is_float_type type_ =
  match builtin_of type_ with Some found -> List.mem found float_types | None -> false

(* Substitution *)

type substitution = (parameter * argument) list

let rec substitute substitution type_ =
  if substitution = [] then type_
  else
    match type_ with
    | Named { path; arguments } ->
        Named { path; arguments = List.map (substitute_argument substitution) arguments }
    | Parameter parameter -> (
        match List.assoc_opt parameter substitution with
        | Some (Type replacement) -> replacement
        | Some (Value _ | Capabilities _) | None -> type_)
    | Projection { base; trait; name } -> (
        let base = substitute substitution base and trait = substitute_trait substitution trait in
        match List.assoc_opt name trait.associated with
        | Some fixed -> fixed
        | None -> Projection { base; trait; name })
    | Function function_type -> Function (substitute_function substitution function_type)
    | Any trait -> Any (substitute_trait substitution trait)
    | Cursor { method_; arguments } ->
        Cursor { method_; arguments = List.map (substitute_argument substitution) arguments }
    | Never | Integer | Variable _ | Literal _ | Hole | Error -> type_

and substitute_argument substitution = function
  | Type type_ -> Type (substitute substitution type_)
  | Value (Value_parameter parameter) as value -> (
      match List.assoc_opt parameter substitution with
      | Some (Value _ as replacement) -> replacement
      | _ -> value)
  | Value _ as value -> value
  | Capabilities capabilities -> Capabilities (substitute_capabilities substitution capabilities)

(* A capability parameter stands for the set it is bound to. *)
and substitute_capabilities substitution capabilities =
  List.sort_uniq compare
    (List.concat_map
       (function
         | Capability_parameter parameter as capability -> (
             match List.assoc_opt parameter substitution with
             | Some (Capabilities replacement) -> replacement
             | _ -> [ capability ])
         | capability -> [ capability ])
       capabilities)

and substitute_trait substitution (trait : trait_reference) =
  {
    trait = trait.trait;
    trait_arguments = List.map (substitute_argument substitution) trait.trait_arguments;
    associated =
      List.map (fun (name, type_) -> (name, substitute substitution type_)) trait.associated;
  }

and substitute_function substitution (function_type : function_type) =
  let result = function
    | Returns type_ -> Returns (substitute substitution type_)
    | Yields (mode, type_) -> Yields (mode, substitute substitution type_)
    | Lends (mode, type_) -> Lends (mode, substitute substitution type_)
  in
  {
    inputs =
      List.map (fun (mode, type_) -> (mode, substitute substitution type_)) function_type.inputs;
    output = result function_type.output;
    uses = substitute_capabilities substitution function_type.uses;
    costs = function_type.costs;
  }

let rec map f type_ =
  match f type_ with
  | Some replacement -> replacement
  | None -> (
      let argument = function Type type_ -> Type (map f type_) | value -> value in
      let trait (reference : trait_reference) =
        {
          reference with
          trait_arguments = List.map argument reference.trait_arguments;
          associated = List.map (fun (name, type_) -> (name, map f type_)) reference.associated;
        }
      in
      match type_ with
      | Named { path; arguments } -> Named { path; arguments = List.map argument arguments }
      | Projection { base; trait = reference; name } ->
          Projection { base = map f base; trait = trait reference; name }
      | Function function_type ->
          Function
            {
              function_type with
              inputs = List.map (fun (mode, type_) -> (mode, map f type_)) function_type.inputs;
              output =
                (match function_type.output with
                | Returns type_ -> Returns (map f type_)
                | Yields (mode, type_) -> Yields (mode, map f type_)
                | Lends (mode, type_) -> Lends (mode, map f type_));
            }
      | Any reference -> Any (trait reference)
      | Cursor { method_; arguments } -> Cursor { method_; arguments = List.map argument arguments }
      | Parameter _ | Never | Integer | Variable _ | Literal _ | Hole | Error -> type_)

let equal left right = left = right

let rec contains_unsolved = function
  | Variable _ | Literal _ | Hole -> true
  | Named { arguments; _ } | Cursor { arguments; _ } -> List.exists argument_unsolved arguments
  | Projection { base; trait; _ } -> contains_unsolved base || trait_unsolved trait
  | Function { inputs; output; _ } -> (
      List.exists (fun (_, type_) -> contains_unsolved type_) inputs
      ||
      match output with
      | Returns type_ | Yields (_, type_) | Lends (_, type_) -> contains_unsolved type_)
  | Any trait -> trait_unsolved trait
  | Parameter _ | Never | Integer | Error -> false

and argument_unsolved = function
  | Type type_ -> contains_unsolved type_
  | Value (Value_variable _) -> true
  | Value _ | Capabilities _ -> false

and trait_unsolved trait =
  List.exists argument_unsolved trait.trait_arguments
  || List.exists (fun (_, type_) -> contains_unsolved type_) trait.associated

let terminates (function_type : function_type) =
  List.exists (fun (cost : cost) -> cost.resource = "time") function_type.costs

(* Showing *)

let path_name = function Path.Top { name; _ } -> name | path -> Path.show path

let rec show = function
  | Named { path; arguments = [] } -> path_name path
  | Named { path; arguments } ->
      Printf.sprintf "%s[%s]" (path_name path)
        (String.concat ", " (List.map show_argument arguments))
  | Parameter { name; _ } -> name
  | Projection { base; name; _ } -> show base ^ "." ^ name
  | Function function_type -> show_function function_type
  | Any trait -> "any " ^ show_trait trait
  | Cursor { method_; _ } -> Printf.sprintf "the cursor of %s" (Path.show method_)
  | Never -> "Never"
  | Integer -> "Integer"
  | Variable _ -> "_"
  | Literal (Integer_literal, _) -> "an integer"
  | Literal (Float_literal, _) -> "a float"
  | Hole -> "an undecided type"
  | Error -> "_"

and show_argument = function
  | Type type_ -> show type_
  | Value (Known value) -> Z.to_string value
  | Value (Value_parameter { name; _ }) -> name
  | Value (Value_variable _) -> "_"
  | Capabilities capabilities ->
      "{"
      ^ String.concat ", "
          (List.map
             (function
               | Capability path -> path_name path | Capability_parameter { name; _ } -> name)
             capabilities)
      ^ "}"

and show_trait trait =
  let arguments = List.map show_argument trait.trait_arguments in
  let associated = List.map (fun (name, type_) -> name ^ " = " ^ show type_) trait.associated in
  match arguments @ associated with
  | [] -> path_name trait.trait
  | all -> Printf.sprintf "%s[%s]" (path_name trait.trait) (String.concat ", " all)

and show_function (function_type : function_type) =
  let mode = function Read -> "" | Mut -> "mut " | Own -> "own " in
  let inputs =
    String.concat ", "
      (List.map (fun (written, type_) -> mode written ^ show type_) function_type.inputs)
  in
  let output =
    match function_type.output with
    | Returns type_ when type_ = unit -> ""
    | Returns type_ -> " -> " ^ show type_
    | Yields (written, type_) -> " yields " ^ mode written ^ show type_
    | Lends (written, type_) -> " lends " ^ mode written ^ show type_
  in
  let base = Printf.sprintf "fn(%s)%s" inputs output in
  let uses =
    List.map
      (function Capability path -> path_name path | Capability_parameter { name; _ } -> name)
      function_type.uses
  in
  let costs =
    List.map
      (fun (cost : cost) ->
        let bound =
          match cost.bound with
          | Finite_cost -> "finite"
          | Order_of -> "O(...)"
          | No_more_than (Some value) -> "<= " ^ Z.to_string value
          | No_more_than None -> "<= ..."
          | Exactly_cost (Some value) -> "== " ^ Z.to_string value
          | Exactly_cost None -> "== ..."
        in
        "cost " ^ cost.resource ^ " " ^ bound)
      function_type.costs
  in
  match (uses, costs) with
  | [], [] -> base
  | _ ->
      Printf.sprintf "(%s%s%s)" base
        (if uses = [] then "" else " uses " ^ String.concat ", " uses)
        (String.concat "" (List.map (fun cost -> " " ^ cost) costs))

(* Interfaces *)

type generic_kind = Type_generic of trait_reference list | Value_generic | Capability_generic
type generic = { generic : parameter; kind : generic_kind }
type parameter_info = { name : string; mode : mode; type_ : ty; has_default : bool }

type signature = {
  generics : generic list;
  receiver : (Path.receiver * ty) option;
  parameters : parameter_info list;
  output : result;
  uses : capability list;
  terminates : bool;
  specification_only : bool;
  stores_functions : string list;
}

let function_type_of (signature : signature) =
  let receiver =
    match signature.receiver with
    | Some (Static, _) | None -> []
    | Some (Read, type_) -> [ (Read, type_) ]
    | Some (Mut, type_) -> [ (Mut, type_) ]
    | Some (Own, type_) -> [ (Own, type_) ]
  in
  {
    inputs =
      receiver @ List.map (fun parameter -> (parameter.mode, parameter.type_)) signature.parameters;
    output = signature.output;
    uses = signature.uses;
    costs =
      (if signature.terminates then
         [ { amortized = false; resource = "time"; bound = Finite_cost } ]
       else []);
  }

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type
  | Builtin_type of Intrinsic.builtin
  | Error_shape

type type_interface = {
  type_generics : generic list;
  shape : shape;
  opaque : bool;
  derives : Path.t list;
}

type associated_type = { associated_name : string; associated_bounds : trait_reference list }

type trait_method = {
  method_name : string;
  method_receiver : Path.receiver;
  method_signature : signature;
  provided : bool;
}

type trait_interface = {
  trait_generics : generic list;
  requires : trait_reference list;
  associated_types : associated_type list;
  methods : trait_method list;
  is_capability : bool;
  broken_methods : string list;
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;
  for_type : ty;
  impl_uses : capability list;
  impl_methods : (string * Path.receiver * signature) list;
  impl_broken : bool;
}

type constant_interface = { constant_type : ty }
