type mode = Read | Mut | Own
type parameter = { owner : Path.t; name : string }
type literal_kind = Integer_literal | Float_literal

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Parameter of parameter
  | Projection of { base : ty; trait : trait_reference; name : string }
  | Function of function_type
  | Any of trait_reference
  | Never
  | Integer
  | Variable of int
  | Literal of literal_kind * int
  | Hole
  | Error of Diagnostic.reported

and argument = Type of ty | Value of value | Capabilities of capability_set
and value = Known of Z.t | Value_parameter of parameter | Value_variable of int

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;
}

and function_type = {
  inputs : (mode * ty) list;
  output : result;
  uses : capability_set;
  costs : cost list;
}

and result = Returns of ty | Lends of mode * ty

and capability =
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_projection of { base : ty; trait : trait_reference; name : string }
  | Capability_variable of int

and capability_set = capability list
and cost = { amortized : bool; resource : resource; bound : cost_bound }

and resource =
  | Time
  | Allocations
  | Allocated_bytes
  | Calls of { capability : Path.t; method_ : string option }

(* A function type's parameters have no names, so its bounds are
   constants: the number, when it is written as one. *)
and cost_bound = Finite_cost | Order_of | No_more_than of Z.t option | Exactly_cost of Z.t option

let capability_set capabilities : capability_set = List.sort_uniq compare capabilities
let no_capabilities : capability_set = []
let capability_union (left : capability_set) (right : capability_set) = capability_set (left @ right)

let capability_subset (smaller : capability_set) (larger : capability_set) =
  List.for_all (fun capability -> List.mem capability larger) smaller

let capability_difference (left : capability_set) (right : capability_set) =
  List.filter (fun capability -> not (List.mem capability right)) left

let flat_map_capabilities f (set : capability_set) = capability_set (List.concat_map f set)
let builtin builtin = Named { path = Intrinsic.builtin_path builtin; arguments = [] }
let unit = builtin Unit
let bool = builtin Bool
let named path arguments = Named { path; arguments = List.map (fun type_ -> Type type_) arguments }

let builtin_of = function
  | Named { path; arguments = [] } -> Intrinsic.builtin_of_path path
  | Named { path; _ } -> (
      match Intrinsic.builtin_of_path path with
      | Some (Array | Storage | View | Shared) as builtin -> builtin
      | _ -> None)
  | _ -> None

let is_builtin wanted type_ = builtin_of type_ = Some wanted
let is_well_known wanted = function Named { path; _ } -> Well_known.is wanted path | _ -> false

(* The built-in integer types, which an integer literal can fill. *)
let integer_types : Intrinsic.builtin list =
  [ Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; USize; ISize ]

let float_types : Intrinsic.builtin list = [ Float32; Float64 ]

let is_integer_type type_ =
  match builtin_of type_ with Some builtin -> List.mem builtin integer_types | None -> false

let integer_bits ?(usize_bits = 64) type_ =
  match builtin_of type_ with
  | Some Int8 -> Some (8, true)
  | Some Int16 -> Some (16, true)
  | Some Int32 -> Some (32, true)
  | Some Int64 -> Some (64, true)
  | Some ISize -> Some (usize_bits, true)
  | Some UInt8 -> Some (8, false)
  | Some UInt16 -> Some (16, false)
  | Some UInt32 -> Some (32, false)
  | Some UInt64 -> Some (64, false)
  | Some USize -> Some (usize_bits, false)
  | _ -> None

let integer_range ?usize_bits type_ =
  Option.map
    (fun (bits, signed) ->
      if signed then (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
      else (Z.zero, Z.pred (Z.shift_left Z.one bits)))
    (integer_bits ?usize_bits type_)

let is_signed type_ = match integer_bits type_ with Some (_, signed) -> signed | None -> false

let is_float_type type_ =
  match builtin_of type_ with Some builtin -> List.mem builtin float_types | None -> false

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
    | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> type_

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
  flat_map_capabilities
    (function
      | Capability_parameter parameter as capability -> (
          match List.assoc_opt parameter substitution with
          | Some (Capabilities replacement) -> (replacement :> capability list)
          | _ -> [ capability ])
      | Capability_projection { base; trait; name } ->
          [
            Capability_projection
              {
                base = substitute substitution base;
                trait = substitute_trait substitution trait;
                name;
              };
          ]
      | (Capability _ | Capability_variable _) as capability -> [ capability ])
    capabilities

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
    | Lends (mode, type_) -> Lends (mode, substitute substitution type_)
  in
  {
    inputs =
      List.map (fun (mode, type_) -> (mode, substitute substitution type_)) function_type.inputs;
    output = result function_type.output;
    uses = substitute_capabilities substitution function_type.uses;
    costs = function_type.costs;
  }

let result_type = function Returns type_ | Lends (_, type_) -> type_
let show_mode = function Read -> "" | Mut -> "mut " | Own -> "own "

let rec map ?(capabilities = Fun.id) transform type_ =
  match transform type_ with
  | Some replacement -> replacement
  | None -> (
      let map = map ~capabilities transform in
      let argument = function
        | Type type_ -> Type (map type_)
        | Capabilities set -> Capabilities (capabilities set)
        | Value _ as value -> value
      in
      let trait (reference : trait_reference) =
        {
          reference with
          trait_arguments = List.map argument reference.trait_arguments;
          associated = List.map (fun (name, type_) -> (name, map type_)) reference.associated;
        }
      in
      match type_ with
      | Named { path; arguments } -> Named { path; arguments = List.map argument arguments }
      | Projection { base; trait = reference; name } ->
          Projection { base = map base; trait = trait reference; name }
      | Function function_type ->
          Function
            {
              function_type with
              inputs = List.map (fun (mode, type_) -> (mode, map type_)) function_type.inputs;
              output =
                (match function_type.output with
                | Returns type_ -> Returns (map type_)
                | Lends (mode, type_) -> Lends (mode, map type_));
              uses = capabilities function_type.uses;
            }
      | Any reference -> Any (trait reference)
      | Parameter _ | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> type_)

let rec exists ?(resolve = Fun.id) transform type_ =
  let type_ = resolve type_ in
  let exists = exists ~resolve transform in
  let argument = function Type type_ -> exists type_ | Value _ | Capabilities _ -> false in
  let trait (reference : trait_reference) =
    List.exists argument reference.trait_arguments
    || List.exists (fun (_, type_) -> exists type_) reference.associated
  in
  transform type_
  ||
  match type_ with
  | Named { arguments; _ } -> List.exists argument arguments
  | Projection { base; trait = reference; _ } -> exists base || trait reference
  | Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> exists type_) inputs || exists (result_type output)
  | Any reference -> trait reference
  | Parameter _ | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> false

let has_capability_variable capabilities =
  List.exists (function Capability_variable _ -> true | _ -> false) capabilities

let equal left right = left = right
let is_error = function Error _ -> true | _ -> false

let rec contains_unsolved = function
  | Variable _ | Literal _ | Hole -> true
  | Named { arguments; _ } -> List.exists argument_unsolved arguments
  | Projection { base; trait; _ } -> contains_unsolved base || trait_unsolved trait
  | Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> contains_unsolved type_) inputs
      || contains_unsolved (result_type output)
  | Any trait -> trait_unsolved trait
  | Parameter _ | Never | Integer | Error _ -> false

and argument_unsolved = function
  | Type type_ -> contains_unsolved type_
  | Value (Value_variable _) -> true
  | Value _ | Capabilities _ -> false

and trait_unsolved trait =
  List.exists argument_unsolved trait.trait_arguments
  || List.exists (fun (_, type_) -> contains_unsolved type_) trait.associated

let capabilities_unsolved capabilities =
  List.exists
    (function
      | Capability_variable _ -> true
      | Capability_projection { base; _ } -> contains_unsolved base
      | Capability _ | Capability_parameter _ -> false)
    capabilities

let terminates (function_type : function_type) =
  List.exists (fun (cost : cost) -> cost.resource = Time) function_type.costs

let same_clauses (left : function_type) (right : function_type) =
  left.uses = right.uses && List.sort_uniq compare left.costs = List.sort_uniq compare right.costs

let bound_implies (provided : cost_bound) (required : cost_bound) =
  match (provided, required) with
  | _, Finite_cost -> true
  | (Order_of | No_more_than _ | Exactly_cost _), Order_of -> true
  | (No_more_than (Some provided) | Exactly_cost (Some provided)), No_more_than (Some required) ->
      Z.leq provided required
  | Exactly_cost (Some provided), Exactly_cost (Some required) -> Z.equal provided required
  | _ -> false

let costs_imply ~(provided : cost list) ~(required : cost list) =
  List.for_all
    (fun (required : cost) ->
      List.exists
        (fun (provided : cost) ->
          provided.resource = required.resource
          && (required.amortized || not provided.amortized)
          && bound_implies provided.bound required.bound)
        provided)
    required

let path_name = function Path.Top { name; _ } -> name | path -> Path.show path

let show_resource = function
  | Time -> "time"
  | Allocations -> "allocations"
  | Allocated_bytes -> "allocated_bytes"
  | Calls { capability; method_ } ->
      Printf.sprintf "calls(%s%s)" (path_name capability)
        (match method_ with Some method_ -> "." ^ method_ | None -> "")

let rec show_capability = function
  | Capability path -> path_name path
  | Capability_parameter { name; _ } -> name
  | Capability_projection { base; name; _ } -> show base ^ "." ^ name
  | Capability_variable _ -> "_"

and show = function
  | Named { path; arguments = [] } -> path_name path
  | Named { path; arguments } ->
      Printf.sprintf "%s[%s]" (path_name path)
        (String.concat ", " (List.map show_argument arguments))
  | Parameter { name; _ } -> name
  | Projection { base; name; _ } -> show base ^ "." ^ name
  | Function function_type -> show_function function_type
  | Any trait -> "any " ^ show_trait trait
  | Never -> "Never"
  | Integer -> "Integer"
  | Variable _ -> "_"
  | Literal (Integer_literal, _) -> "an integer"
  | Literal (Float_literal, _) -> "a float"
  | Hole -> "an undecided type"
  | Error _ -> "_"

and show_argument = function
  | Type type_ -> show type_
  | Value (Known value) -> Z.to_string value
  | Value (Value_parameter { name; _ }) -> name
  | Value (Value_variable _) -> "_"
  | Capabilities capabilities ->
      "{" ^ String.concat ", " (List.map show_capability capabilities) ^ "}"

and show_trait trait =
  let arguments = List.map show_argument trait.trait_arguments in
  let associated = List.map (fun (name, type_) -> name ^ " = " ^ show type_) trait.associated in
  match arguments @ associated with
  | [] -> path_name trait.trait
  | all -> Printf.sprintf "%s[%s]" (path_name trait.trait) (String.concat ", " all)

and show_output = function
  | Returns type_ when type_ = unit -> ""
  | Returns type_ -> " -> " ^ show type_
  | Lends (written, type_) -> " lends " ^ show_mode written ^ show type_

and show_function (function_type : function_type) =
  let inputs =
    String.concat ", "
      (List.map (fun (written, type_) -> show_mode written ^ show type_) function_type.inputs)
  in
  let base = Printf.sprintf "fn(%s)%s" inputs (show_output function_type.output) in
  let uses = List.map show_capability function_type.uses in
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
        "cost " ^ show_resource cost.resource ^ " " ^ bound)
      function_type.costs
  in
  match (uses, costs) with
  | [], [] -> base
  | _ ->
      Printf.sprintf "(%s%s%s)" base
        (if uses = [] then "" else " uses " ^ String.concat ", " uses)
        (String.concat "" (List.map (fun cost -> " " ^ cost) costs))

type generic_kind = Type_generic of trait_reference list | Value_generic | Capability_generic
type generic = { generic : parameter; kind : generic_kind }

let generic_arguments generics =
  List.map
    (fun generic ->
      match generic.kind with
      | Value_generic -> Value (Value_parameter generic.generic)
      | Type_generic _ -> Type (Parameter generic.generic)
      | Capability_generic -> Capabilities [ Capability_parameter generic.generic ])
    generics

let bounds_of generics parameter =
  List.concat_map
    (fun generic ->
      match generic.kind with
      | Type_generic bounds when generic.generic = parameter -> bounds
      | _ -> [])
    generics

let substitution_of (generics : generic list) arguments : substitution option =
  if List.length generics = List.length arguments then
    Some (List.combine (List.map (fun generic -> generic.generic) generics) arguments)
  else None

type parameter_info = { name : string; mode : mode; type_ : ty; has_default : bool }

type signature = {
  generics : generic list;
  receiver : (Path.receiver * ty) option;
  parameters : parameter_info list;
  output : result;
  uses : capability_set;
  terminates : bool;
  specification_only : bool;
  stores_functions : string list;
}

let body_is_definition (signature : signature) =
  signature.terminates && signature.uses = []
  && (match signature.receiver with Some (Mut, _) -> false | _ -> true)
  && List.for_all (fun (parameter : parameter_info) -> parameter.mode <> Mut) signature.parameters
  && match signature.output with Returns _ -> true | Lends _ -> false

let map_signature transform (signature : signature) =
  {
    signature with
    receiver = Option.map (fun (receiver, type_) -> (receiver, transform type_)) signature.receiver;
    parameters =
      List.map
        (fun (parameter : parameter_info) -> { parameter with type_ = transform parameter.type_ })
        signature.parameters;
    output =
      (match signature.output with
      | Returns type_ -> Returns (transform type_)
      | Lends (mode, type_) -> Lends (mode, transform type_));
  }

let substitute_signature substitution (signature : signature) =
  let signature = map_signature (substitute substitution) signature in
  {
    signature with
    generics =
      List.map
        (fun (generic : generic) ->
          match generic.kind with
          | Type_generic bounds ->
              { generic with kind = Type_generic (List.map (substitute_trait substitution) bounds) }
          | Value_generic | Capability_generic -> generic)
        signature.generics;
    uses = substitute_capabilities substitution signature.uses;
  }

let method_in_impl ~impl_generics ~impl_uses (signature : signature) =
  {
    signature with
    generics = impl_generics @ signature.generics;
    uses = capability_union signature.uses impl_uses;
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
      (if signature.terminates then [ { amortized = false; resource = Time; bound = Finite_cost } ]
       else []);
  }

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type
  | Builtin_type of Intrinsic.builtin
  | Error_shape of Diagnostic.reported

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
  associated_capabilities : string list;
  methods : trait_method list;
  laws : (string * (string * ty) list) list;
  is_capability : bool;
  broken_methods : (string * Diagnostic.reported) list;
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;
  for_type : ty;
  impl_uses : capability_set;
  capability_sets : (string * capability_set) list;
  impl_methods : (string * Path.receiver * signature) list;
  impl_broken : bool;
}

type constant_interface = { constant_type : ty }
