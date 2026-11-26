type parameter = { owner : Path.t; name : string }

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Parameter of parameter
  | Projection of { base : ty; trait : trait_reference; name : string }
  | Function of function_type
  | Never
  | Integer
  | Variable of int
  | Hole
  | Error of Diagnostic.reported

and argument = Type of ty | Value of value

and value =
  | Known of Z.t
  | Value_parameter of parameter
  | Value_variable of int
  | Value_error of Diagnostic.reported

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;
}

and function_type = {
  inputs : (Language.Mode.t * ty) list;
  output : ty;
  uses : capability_set;
  costs : cost list;
}

and result = Returns of ty | Lends of Language.Mode.t * ty

and capability =
  | Built_in of Language.Builtin_capability.t
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_projection of { base : ty; trait : trait_reference; name : string }
  | Capability_variable of int
  | Capability_error of Diagnostic.reported
  | Capability_unless of { capability : capability; unless : condition }
  | Capability_unless_values of capability

and condition = bound_condition list
and bound_condition = { subject : ty; bound : trait_reference }
and capability_set = capability list
and cost = { amortized : bool; resource : resource; bound : cost_bound }

and resource =
  | Metric of Language.Metric.t
  | Calls of { capability : Path.t; method_ : string option }

and cost_bound = Order_of | No_more_than of Z.t | Exactly_cost of Z.t

type associated_kind = Associated_type | Associated_capability_set

type application =
  | Type_application of ty
  | Trait_application of trait_reference
  | Associated_application of {
      base : ty;
      bounds : trait_reference list;
      name : string;
      kind : associated_kind;
    }

let make_condition (condition : condition) : condition = List.sort_uniq compare condition

let rec make_unless capability unless =
  match capability with
  | Capability_unless { capability; unless = inner } -> make_unless capability (inner @ unless)
  | _ -> (
      match make_condition unless with
      | [] -> None
      | unless -> Some (Capability_unless { capability; unless }))

let find_base = function
  | Capability_unless { capability; _ } | Capability_unless_values capability -> capability
  | capability -> capability

let make_capability_set capabilities : capability_set =
  let capabilities = List.sort_uniq compare capabilities in
  let unconditional =
    List.filter
      (function Capability_unless _ | Capability_unless_values _ -> false | _ -> true)
      capabilities
  in
  let unless_values =
    List.filter
      (function
        | Capability_unless_values capability -> not (List.mem capability unconditional)
        | _ -> false)
      capabilities
  in
  let conditional =
    List.fold_left
      (fun merged capability ->
        match capability with
        | Capability_unless { capability; unless } when not (List.mem capability unconditional) -> (
            match List.assoc_opt capability merged with
            | Some earlier -> (capability, earlier @ unless) :: List.remove_assoc capability merged
            | None -> (capability, unless) :: merged)
        | _ -> merged)
      [] capabilities
  in
  List.sort_uniq compare
    (unconditional @ unless_values
    @ List.filter_map (fun (capability, unless) -> make_unless capability unless) conditional)

let no_capabilities : capability_set = []

let union_capabilities (left : capability_set) (right : capability_set) =
  make_capability_set (left @ right)

let make_capability path =
  match Well_known.find_builtin_capability path with
  | Some builtin_capability -> Built_in builtin_capability
  | None -> Capability path

let has_capability capability (set : capability_set) = List.mem capability set

let may_use capability (set : capability_set) =
  List.exists (fun used -> find_base used = capability) set

let find_unless capability (set : capability_set) =
  List.find_map
    (function
      | Capability_unless { capability = used; unless } when used = capability -> Some unless
      | _ -> None)
    set

let exists_capability predicate (set : capability_set) =
  List.exists (fun capability -> predicate (find_base capability)) set

let list_capabilities (set : capability_set) : capability list = set
let terminates set = not (may_use (Built_in Run_forever) set)

let terminates_when ~implies (premise : condition) (set : capability_set) =
  (not (has_capability (Built_in Run_forever) set))
  &&
  match find_unless (Built_in Run_forever) set with
  | Some unless -> implies premise unless
  | None -> true

let contains_capability_error (capabilities : capability_set) =
  List.exists
    (fun capability -> match find_base capability with Capability_error _ -> true | _ -> false)
    capabilities

let is_covered ~implies (available : capability_set) capability =
  let has_base base =
    List.exists
      (function
        | Capability_unless_values covering -> covering = base | covering -> covering = base)
      available
  in
  match capability with
  | Capability_unless { capability = base; unless } ->
      has_base base
      || List.exists
           (function
             | Capability_unless { capability = covering; unless = covering_unless } ->
                 covering = base && implies covering_unless unless
             | _ -> false)
           available
  | Capability_unless_values base -> has_base base
  | _ -> has_base capability

let subtract_capabilities ~implies (left : capability_set) (right : capability_set) =
  List.filter (fun capability -> not (is_covered ~implies right capability)) left

let is_capability_subset ~implies (smaller : capability_set) (larger : capability_set) =
  contains_capability_error smaller || contains_capability_error larger
  || subtract_capabilities ~implies smaller larger = []

let intersect_capabilities ~implies (sets : capability_set list) : capability_set =
  make_capability_set
    (List.filter
       (fun capability -> List.for_all (fun set -> is_covered ~implies set capability) sets)
       (List.concat sets))

let compute_missing_capabilities ~implies ~(required : capability_set) ~(available : capability_set)
    =
  if contains_capability_error required || contains_capability_error available then no_capabilities
  else subtract_capabilities ~implies required available

let replace_capabilities find_replacement (set : capability_set) =
  make_capability_set
    (List.concat_map
       (fun capability ->
         match capability with
         | Capability_unless { capability = base; unless } ->
             List.filter_map
               (fun replacement -> make_unless replacement unless)
               (Option.value ~default:[ base ] (find_replacement base))
         | _ -> Option.value ~default:[ capability ] (find_replacement capability))
       set)

let map_conditions transform (set : capability_set) =
  make_capability_set
    (List.filter_map
       (function
         | Capability_unless { capability; unless } -> make_unless capability (transform unless)
         | capability -> Some capability)
       set)

let make_builtin ?(arguments = []) builtin =
  Named { path = Well_known.make_builtin_type_path builtin; arguments }

let unit = make_builtin Unit
let bool = make_builtin Bool
let make_self_parameter trait = { owner = trait; name = "Self" }
let is_self_parameter parameter = parameter.name = "Self"

let make_named path arguments =
  Named { path; arguments = List.map (fun type_ -> Type type_) arguments }

let find_builtin = function
  | Named { path; arguments = [] } -> Well_known.find_builtin_type path
  | Named { path; _ } -> (
      match Well_known.find_builtin_type path with
      | Some (Array | Storage | View | Shared) as builtin -> builtin
      | _ -> None)
  | _ -> None

let is_builtin wanted type_ = find_builtin type_ = Some wanted
let is_well_known wanted = function Named { path; _ } -> Well_known.is wanted path | _ -> false

let find_viewed = function
  | Named { path; arguments = [ Type viewed ] } when Well_known.find_builtin_type path = Some View
    ->
      Some viewed
  | _ -> None

let strip_view type_ = Option.value ~default:type_ (find_viewed type_)
let is_view type_ = Option.is_some (find_viewed type_)

let make_view viewed =
  if is_view viewed then viewed else make_builtin View ~arguments:[ Type viewed ]

let is_viewable type_ =
  is_well_known List type_ || is_well_known String type_ || is_builtin Storage type_

let signed_integer_types : Language.Builtin_type.t list = [ Int8; Int16; Int32; Int64 ]
let unsigned_integer_types : Language.Builtin_type.t list = [ UInt8; UInt16; UInt32; UInt64 ]
let integer_types = signed_integer_types @ unsigned_integer_types

let sealed_traits : Well_known.t list =
  [ Fixed_width_integer; Signed_integer; Unsigned_integer; Floating_point ]

let find_integer_implementors trait =
  if Well_known.is Signed_integer trait then Some signed_integer_types
  else if Well_known.is Unsigned_integer trait then Some unsigned_integer_types
  else if Well_known.is Fixed_width_integer trait then Some integer_types
  else None

let find_bound_integer_implementors bounds =
  List.fold_left
    (fun implementors (bound : trait_reference) ->
      match (implementors, find_integer_implementors bound.trait) with
      | Some implementors, Some these ->
          Some (List.filter (fun builtin -> List.mem builtin these) implementors)
      | None, these | these, None -> these)
    None bounds

let float_types : Language.Builtin_type.t list = [ Float32; Float64 ]
let number_types = integer_types @ float_types @ [ Language.Builtin_type.Integer ]

let find_sealed_implementors trait =
  if Well_known.is Floating_point trait then Some float_types else find_integer_implementors trait

let is_integer_type type_ =
  match find_builtin type_ with Some builtin -> List.mem builtin integer_types | None -> false

let list_scalar_members = function
  | Integer -> [ Language.Builtin_type.Integer ]
  | type_ ->
      List.filter
        (fun scalar -> is_builtin scalar type_)
        ((Language.Builtin_type.Character :: integer_types) @ float_types)

let find_integer_bits type_ =
  match find_builtin type_ with
  | Some Int8 -> Some (8, true)
  | Some Int16 -> Some (16, true)
  | Some Int32 -> Some (32, true)
  | Some Int64 -> Some (64, true)
  | Some UInt8 -> Some (8, false)
  | Some UInt16 -> Some (16, false)
  | Some UInt32 -> Some (32, false)
  | Some UInt64 -> Some (64, false)
  | _ -> None

let find_integer_range type_ =
  Option.map
    (fun (bits, signed) ->
      if signed then (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
      else (Z.zero, Z.pred (Z.shift_left Z.one bits)))
    (find_integer_bits type_)

let list_fitting_integer_types number =
  List.filter
    (fun builtin ->
      match find_integer_range (make_builtin builtin) with
      | Some (low, high) -> Z.leq low number && Z.leq number high
      | None -> false)
    integer_types

let is_float_type type_ =
  match find_builtin type_ with Some builtin -> List.mem builtin float_types | None -> false

type property = Copyable | Plain | View | Holds_function

type substitution = {
  arguments : (parameter * argument) list;
  capability_arguments : (parameter * capability_set) list;
}

let no_substitution = { arguments = []; capability_arguments = [] }
let is_empty_substitution substitution = substitution = no_substitution

let combine_substitutions left right =
  {
    arguments = left.arguments @ right.arguments;
    capability_arguments = left.capability_arguments @ right.capability_arguments;
  }

let bind_argument parameter argument substitution =
  { substitution with arguments = (parameter, argument) :: substitution.arguments }

let find_argument parameter substitution = List.assoc_opt parameter substitution.arguments

let list_type_arguments substitution =
  List.filter_map
    (function parameter, Type ty -> Some (parameter, ty) | _, Value _ -> None)
    substitution.arguments

let rec substitute substitution type_ =
  if is_empty_substitution substitution then type_
  else
    match type_ with
    | Named { path; arguments } ->
        Named { path; arguments = List.map (substitute_argument substitution) arguments }
    | Parameter parameter -> (
        match find_argument parameter substitution with
        | Some (Type replacement) -> replacement
        | Some (Value _) | None -> type_)
    | Projection { base; trait; name } -> (
        let base = substitute substitution base and trait = substitute_trait substitution trait in
        match List.assoc_opt name trait.associated with
        | Some fixed -> fixed
        | None -> Projection { base; trait; name })
    | Function function_type -> Function (substitute_function substitution function_type)
    | Never | Integer | Variable _ | Hole | Error _ -> type_

and substitute_argument substitution = function
  | Type type_ -> Type (substitute substitution type_)
  | Value (Value_parameter parameter) as value -> (
      match find_argument parameter substitution with
      | Some (Value _ as replacement) -> replacement
      | _ -> value)
  | Value _ as value -> value

and substitute_capabilities substitution capabilities =
  replace_capabilities
    (function
      | Capability_parameter parameter -> List.assoc_opt parameter substitution.capability_arguments
      | Capability_projection { base; trait; name } ->
          Some
            [
              Capability_projection
                {
                  base = substitute substitution base;
                  trait = substitute_trait substitution trait;
                  name;
                };
            ]
      | Built_in _ | Capability _ | Capability_variable _ | Capability_error _ | Capability_unless _
      | Capability_unless_values _ ->
          None)
    (map_conditions (substitute_condition substitution) capabilities)

and substitute_condition substitution (condition : condition) =
  map_condition_types (substitute substitution) (substitute_trait substitution) condition

and map_condition_types map_type map_trait (condition : condition) =
  List.map
    (fun (bound : bound_condition) ->
      { subject = map_type bound.subject; bound = map_trait bound.bound })
    condition

and substitute_trait substitution (trait : trait_reference) =
  {
    trait = trait.trait;
    trait_arguments = List.map (substitute_argument substitution) trait.trait_arguments;
    associated =
      List.map (fun (name, type_) -> (name, substitute substitution type_)) trait.associated;
  }

and substitute_function substitution (function_type : function_type) =
  {
    inputs =
      List.map (fun (mode, type_) -> (mode, substitute substitution type_)) function_type.inputs;
    output = substitute substitution function_type.output;
    uses = substitute_capabilities substitution function_type.uses;
    costs = function_type.costs;
  }

let map_substitution ~argument ~capabilities substitution =
  {
    arguments =
      List.map (fun (parameter, bound) -> (parameter, argument bound)) substitution.arguments;
    capability_arguments =
      List.map
        (fun (parameter, bound) -> (parameter, capabilities bound))
        substitution.capability_arguments;
  }

let substitute_substitution outer =
  map_substitution ~argument:(substitute_argument outer)
    ~capabilities:(substitute_capabilities outer)

type evidence =
  | Impl of { impl : Path.t; substitution : substitution }
  | Derived_for_view of { viewed : Path.t; substitution : substitution }
  | Bound

let substitute_evidence outer = function
  | Impl { impl; substitution } ->
      Impl { impl; substitution = substitute_substitution outer substitution }
  | Derived_for_view { viewed; substitution } ->
      Derived_for_view { viewed; substitution = substitute_substitution outer substitution }
  | Bound -> Bound

let extract_result_type = function Returns type_ | Lends (_, type_) -> type_
let find_lent_mode = function Lends (mode, _) -> Some mode | Returns _ -> None
let map_argument map = function Type type_ -> Type (map type_) | Value _ as value -> value

let map_trait map (reference : trait_reference) =
  {
    reference with
    trait_arguments = List.map (map_argument map) reference.trait_arguments;
    associated = List.map (fun (name, type_) -> (name, map type_)) reference.associated;
  }

let map_capability_types map_type map_trait capabilities =
  replace_capabilities
    (function
      | Capability_projection { base; trait; name } ->
          Some [ Capability_projection { base = map_type base; trait = map_trait trait; name } ]
      | _ -> None)
    (map_conditions (map_condition_types map_type map_trait) capabilities)

let rec map ?(map_capabilities = Fun.id) transform type_ =
  match transform type_ with
  | Some replacement -> replacement
  | None -> (
      let map = map ~map_capabilities transform in
      match type_ with
      | Named { path; arguments } ->
          Named { path; arguments = List.map (map_argument map) arguments }
      | Projection { base; trait = reference; name } ->
          Projection { base = map base; trait = map_trait map reference; name }
      | Function function_type ->
          Function
            {
              function_type with
              inputs = List.map (fun (mode, type_) -> (mode, map type_)) function_type.inputs;
              output = map function_type.output;
              uses = map_capabilities function_type.uses;
            }
      | Parameter _ | Never | Integer | Variable _ | Hole | Error _ -> type_)

let rec erase_views type_ = map (fun type_ -> Option.map erase_views (find_viewed type_)) type_
let erase_argument_views argument = map_argument erase_views argument
let erase_trait_views (trait : trait_reference) = map_trait erase_views trait
let substitute_erased substitution type_ = erase_views (substitute substitution type_)

let substitute_argument_erased substitution argument =
  erase_argument_views (substitute_argument substitution argument)

let substitute_trait_erased substitution trait =
  erase_trait_views (substitute_trait substitution trait)

let rec exists ?(resolve = Fun.id) transform type_ =
  let type_ = resolve type_ in
  let exists = exists ~resolve transform in
  let argument_exists = function Type type_ -> exists type_ | Value _ -> false in
  let trait_exists (reference : trait_reference) =
    List.exists argument_exists reference.trait_arguments
    || List.exists (fun (_, type_) -> exists type_) reference.associated
  in
  transform type_
  ||
  match type_ with
  | Named { arguments; _ } -> List.exists argument_exists arguments
  | Projection { base; trait = reference; _ } -> exists base || trait_exists reference
  | Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> exists type_) inputs || exists output
  | Parameter _ | Never | Integer | Variable _ | Hole | Error _ -> false

let is_specification_only = function
  | Integer -> true
  | Named { path = Top { module_; _ }; _ } -> module_ = Well_known.specification
  | _ -> false

let find_specification_only_type type_ =
  let specification_type = ref None in
  ignore
    (exists
       (fun part ->
         if is_specification_only part then specification_type := Some part;
         is_specification_only part)
       type_);
  !specification_type

let contains_capability_variable capabilities =
  List.exists
    (fun capability -> match find_base capability with Capability_variable _ -> true | _ -> false)
    capabilities

let equal left right = left = right
let is_error : ty -> bool = function Error _ -> true | _ -> false
let is_open_type : ty -> bool = function Error _ | Variable _ | Hole -> true | _ -> false

let rec contains_unsolved = function
  | Variable _ | Hole -> true
  | Named { arguments; _ } -> List.exists is_unsolved_argument arguments
  | Projection { base; trait; _ } -> contains_unsolved base || is_unsolved_trait trait
  | Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> contains_unsolved type_) inputs || contains_unsolved output
  | Parameter _ | Never | Integer | Error _ -> false

and is_unsolved_argument = function
  | Type type_ -> contains_unsolved type_
  | Value (Value_variable _) -> true
  | Value _ -> false

and is_unsolved_trait trait =
  List.exists is_unsolved_argument trait.trait_arguments
  || List.exists (fun (_, type_) -> contains_unsolved type_) trait.associated

let rec is_unsolved_capability = function
  | Capability_variable _ -> true
  | Capability_projection { base; _ } -> contains_unsolved base
  | Capability_unless { capability; unless } ->
      is_unsolved_capability capability
      || List.exists
           (fun (bound : bound_condition) ->
             contains_unsolved bound.subject || is_unsolved_trait bound.bound)
           unless
  | Capability_unless_values capability -> is_unsolved_capability capability
  | Built_in _ | Capability _ | Capability_parameter _ | Capability_error _ -> false

let has_unsolved_capabilities capabilities = List.exists is_unsolved_capability capabilities

let has_same_clauses (left : function_type) (right : function_type) =
  left.uses = right.uses && List.sort_uniq compare left.costs = List.sort_uniq compare right.costs

let bound_implies (provided : cost_bound) (required : cost_bound) =
  match (provided, required) with
  | (Order_of | No_more_than _ | Exactly_cost _), Order_of -> true
  | (No_more_than provided | Exactly_cost provided), No_more_than required ->
      Z.leq provided required
  | Exactly_cost provided, Exactly_cost required -> Z.equal provided required
  | Order_of, (No_more_than _ | Exactly_cost _) | No_more_than _, Exactly_cost _ -> false

let costs_imply ~(provided : cost list) ~(required : cost list) =
  List.for_all
    (fun (required : cost) ->
      List.exists
        (fun (provided : cost) ->
          provided.resource = required.resource
          && provided.amortized = required.amortized
          && bound_implies provided.bound required.bound)
        provided)
    required

let show_resource = function
  | Metric metric -> Language.Metric.show metric
  | Calls { capability; method_ } ->
      Printf.sprintf "calls(%s%s)" (Path.show_name capability)
        (match method_ with Some method_ -> "." ^ method_ | None -> "")

let rec show_capability = function
  | Built_in builtin_capability -> Language.Builtin_capability.show builtin_capability
  | Capability path -> Path.show_name path
  | Capability_parameter { name; _ } -> "generic " ^ name
  | Capability_projection { base; name; _ } -> show base ^ "." ^ name
  | Capability_variable _ | Capability_error _ -> "_"
  | Capability_unless { capability; unless } ->
      show_capability capability ^ " unless " ^ show_condition unless
  | Capability_unless_values capability ->
      show_capability capability ^ " unless a condition on its arguments"

and show_condition condition =
  String.concat " && "
    (List.map
       (fun (bound : bound_condition) -> show bound.subject ^ ": " ^ show_trait bound.bound)
       condition)

and show = function
  | Named { path; arguments = [ Type viewed ] } when Well_known.find_builtin_type path = Some View
    ->
      "view " ^ show viewed
  | Named { path; arguments = [] } -> Path.show_name path
  | Named { path; arguments } ->
      Printf.sprintf "%s[%s]" (Path.show_name path)
        (String.concat ", " (List.map show_argument arguments))
  | Parameter { name; _ } -> name
  | Projection { base; name; _ } -> show base ^ "." ^ name
  | Function function_type -> show_function function_type
  | Never -> "Never"
  | Integer -> "Integer"
  | Variable _ | Hole | Error _ -> "_"

and show_argument = function
  | Type type_ -> show type_
  | Value (Known value) -> Z.to_string value
  | Value (Value_parameter { name; _ }) -> name
  | Value (Value_variable _ | Value_error _) -> "_"

and show_capabilities capabilities =
  let names =
    List.fold_left
      (fun names name -> if List.mem name names then names else names @ [ name ])
      []
      (List.map show_capability capabilities)
  in
  "{" ^ String.concat ", " names ^ "}"

and show_trait trait =
  let arguments = List.map show_argument trait.trait_arguments in
  let associated = List.map (fun (name, type_) -> name ^ " = " ^ show type_) trait.associated in
  match arguments @ associated with
  | [] -> Path.show_name trait.trait
  | all -> Printf.sprintf "%s[%s]" (Path.show_name trait.trait) (String.concat ", " all)

and show_output = function
  | Returns type_ when type_ = unit -> ""
  | Returns type_ -> " -> " ^ show type_
  | Lends (written, type_) -> " lends " ^ Language.Mode.show_prefix written ^ show type_

and show_function (function_type : function_type) =
  let inputs =
    String.concat ", "
      (List.map
         (fun (written, type_) -> Language.Mode.show_prefix written ^ show type_)
         function_type.inputs)
  in
  let base = Printf.sprintf "fn(%s)%s" inputs (show_output (Returns function_type.output)) in
  let uses = List.map show_capability function_type.uses in
  let costs =
    List.map
      (fun (cost : cost) ->
        let bound =
          match cost.bound with
          | Order_of -> "O(1)"
          | No_more_than value -> "<= " ^ Z.to_string value
          | Exactly_cost value -> "== " ^ Z.to_string value
        in
        Printf.sprintf "cost %s%s %s"
          (if cost.amortized then "amortized " else "")
          (show_resource cost.resource) bound)
      function_type.costs
  in
  match (uses, costs) with
  | [], [] -> base
  | _ ->
      Printf.sprintf "(%s%s%s)" base
        (if uses = [] then "" else " uses " ^ String.concat ", " uses)
        (String.concat "" (List.map (fun cost -> " " ^ cost) costs))

type generic_kind = Type_generic of trait_reference list | Value_generic
type generic = { generic : parameter; kind : generic_kind }

let list_generic_arguments generics =
  List.map
    (fun generic ->
      match generic.kind with
      | Value_generic -> Value (Value_parameter generic.generic)
      | Type_generic _ -> Type (Parameter generic.generic))
    generics

let list_capability_arguments parameters =
  List.map
    (fun parameter -> (parameter.name, make_capability_set [ Capability_parameter parameter ]))
    parameters

let list_bounds generics parameter =
  List.concat_map
    (fun generic ->
      match generic.kind with
      | Type_generic bounds when generic.generic = parameter -> bounds
      | _ -> [])
    generics

let make_substitution (generics : generic list) arguments : substitution =
  if List.length generics = List.length arguments then
    {
      arguments = List.combine (List.map (fun generic -> generic.generic) generics) arguments;
      capability_arguments = [];
    }
  else
    Compiler_bug.raise_bug ~stage:"Types" "a substitution of %d arguments for %d generics"
      (List.length arguments) (List.length generics)

let make_capability_substitution (parameters : parameter list) arguments : substitution =
  {
    arguments = [];
    capability_arguments =
      List.filter_map
        (fun parameter ->
          Option.map
            (fun argument -> (parameter, argument))
            (List.assoc_opt parameter.name arguments))
        parameters;
  }

type parameter_info = { name : string; mode : Language.Mode.t; type_ : ty; has_default : bool }

let list_capture_free_parameters parameters =
  List.filter_map
    (fun parameter ->
      match (parameter.mode, parameter.type_) with
      | Own, Function _ -> Some parameter.name
      | _ -> None)
    parameters

let mentions_specification_only_type parameters output =
  List.exists
    (fun type_ -> Option.is_some (find_specification_only_type type_))
    (extract_result_type output :: List.map (fun parameter -> parameter.type_) parameters)

type modified = { position : int; field_path : string list; is_elements : bool }

type signature = {
  generics : generic list;
  capability_parameters : parameter list;
  receiver : (Language.Mode.t * ty) option;
  parameters : parameter_info list;
  output : result;
  uses : capability_set;
  costs : cost list;
  modifies : modified list;
  specification_only : bool;
  is_update_step : bool;
  capture_free_parameters : string list;
}

let rec is_field_path_prefix prefix fields =
  match (prefix, fields) with
  | [], _ -> true
  | field :: prefix, other :: fields -> field = other && is_field_path_prefix prefix fields
  | _ :: _, [] -> false

let find_parameter_position (signature : signature) name =
  match signature.receiver with
  | Some _ when name = "self" -> Some 0
  | _ ->
      let offset = match signature.receiver with Some _ -> 1 | None -> 0 in
      Option.map
        (fun index -> index + offset)
        (List.find_index
           (fun (parameter : parameter_info) -> parameter.name = name)
           signature.parameters)

let read_parameter_at (signature : signature) position =
  match signature.receiver with
  | Some (mode, type_) when position = 0 -> { name = "self"; mode; type_; has_default = false }
  | _ -> (
      let offset = match signature.receiver with Some _ -> 1 | None -> 0 in
      match List.nth_opt signature.parameters (position - offset) with
      | Some parameter -> parameter
      | None ->
          Compiler_bug.raise_bug ~stage:"Types" "a parameter at position %d of a signature of %d"
            position
            (List.length signature.parameters))

let add_receiver (signature : signature) receiver =
  match (signature.receiver, receiver) with
  | None, Some _ ->
      {
        signature with
        receiver;
        modifies =
          List.map (fun part -> { part with position = part.position + 1 }) signature.modifies;
      }
  | _ -> { signature with receiver }

let list_modified_parts (signature : signature) position =
  match List.filter (fun modified -> modified.position = position) signature.modifies with
  | [] -> None
  | entries -> Some entries

let is_part_within ~(container : modified) (part : modified) =
  container.position = part.position
  && is_field_path_prefix container.field_path part.field_path
  && ((not container.is_elements) || (part.is_elements && container.field_path = part.field_path))

let show_modified_part ~root (part : modified) =
  String.concat "." (root :: part.field_path) ^ if part.is_elements then "[..]" else ""

type instantiation = {
  type_arguments : argument list;
  capability_arguments : (string * capability_set) list;
}

let no_instantiation = { type_arguments = []; capability_arguments = [] }

let substitute_instantiation substitution instantiation =
  {
    type_arguments = List.map (substitute_argument substitution) instantiation.type_arguments;
    capability_arguments =
      List.map
        (fun (name, argument) -> (name, substitute_capabilities substitution argument))
        instantiation.capability_arguments;
  }

let make_signature_substitution (signature : signature) instantiation =
  combine_substitutions
    (make_substitution signature.generics instantiation.type_arguments)
    (make_capability_substitution signature.capability_parameters instantiation.capability_arguments)

let make_trait_substitution generics ~self (reference : trait_reference) =
  bind_argument
    (make_self_parameter reference.trait)
    (Type self)
    (make_substitution generics reference.trait_arguments)

let map_bounds transform generics =
  List.map
    (fun generic ->
      match generic.kind with
      | Type_generic bounds -> { generic with kind = Type_generic (transform bounds) }
      | Value_generic -> generic)
    generics

let map_signature transform (signature : signature) =
  let transform_argument = function
    | Type type_ -> Type (transform type_)
    | Value _ as value -> value
  in
  {
    signature with
    generics =
      map_bounds
        (List.map (fun (bound : trait_reference) ->
             {
               bound with
               trait_arguments = List.map transform_argument bound.trait_arguments;
               associated = List.map (fun (name, type_) -> (name, transform type_)) bound.associated;
             }))
        signature.generics;
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
  {
    (map_signature (substitute substitution) signature) with
    generics = map_bounds (List.map (substitute_trait substitution)) signature.generics;
    uses = substitute_capabilities substitution signature.uses;
  }

let add_impl_generics_and_uses ~impl_generics ~impl_uses (signature : signature) =
  {
    signature with
    generics = impl_generics @ signature.generics;
    uses = union_capabilities signature.uses impl_uses;
  }

let make_function_type (signature : signature) =
  match signature.output with
  | Lends _ -> None
  | Returns output ->
      Some
        {
          inputs =
            Option.to_list signature.receiver
            @ List.map (fun parameter -> (parameter.mode, parameter.type_)) signature.parameters;
          output;
          uses =
            replace_capabilities
              (function Capability_unless_values capability -> Some [ capability ] | _ -> None)
              signature.uses;
          costs = signature.costs;
        }

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type
  | Builtin_type of Language.Builtin_type.t

type type_interface = {
  type_generics : generic list;
  shape : shape;
  opaque : bool;
  is_tuple : bool;
  derives : Path.t list;
  declares_potential : bool;
}

let substitute_fields interface arguments fields =
  let substitution = make_substitution interface.type_generics arguments in
  List.map
    (fun (field : field) -> { field with field_type = substitute substitution field.field_type })
    fields

let instantiate_fields interface arguments =
  match interface.shape with
  | Record fields -> Some (substitute_fields interface arguments fields)
  | Sum _ | Todo_type | Builtin_type _ -> None

let instantiate_variants interface arguments =
  match interface.shape with
  | Sum variants ->
      Some
        (List.map
           (fun (variant : variant) ->
             {
               variant with
               fields = Option.map (substitute_fields interface arguments) variant.fields;
             })
           variants)
  | Record _ | Todo_type | Builtin_type _ -> None

let list_field_types interface =
  match interface.shape with
  | Record fields -> List.map (fun field -> field.field_type) fields
  | Sum variants ->
      List.concat_map
        (fun variant ->
          List.map (fun field -> field.field_type) (Option.value ~default:[] variant.fields))
        variants
  | Todo_type | Builtin_type _ -> []

type associated_type = { associated_name : string; associated_bounds : trait_reference list }
type trait_method = { method_name : string; method_receiver : Path.receiver; provided : bool }

type restated_method = {
  restated_name : string;
  restated_receiver : Path.receiver;
  declared_by : Path.t;
}

type trait_interface = {
  trait_generics : generic list;
  requires : trait_reference list;
  supertraits : trait_reference list;
  associated_types : associated_type list;
  associated_capabilities : string list;
  methods : trait_method list;
  restated : restated_method list;
  laws : (string * (string * ty) list) list;
  is_capability : bool;
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;
  for_type : ty;
  impl_uses : capability_set;
  capability_sets : (string * capability_set) list;
  impl_methods : (string * Path.receiver) list;
}

let is_implemented_by (trait : trait_interface) (declared : trait_method) ~name ~receiver =
  declared.method_name = name && (trait.is_capability || declared.method_receiver = receiver)

let find_implementing_receiver trait (impl : impl_interface) declared =
  Option.map snd
    (List.find_opt
       (fun (name, receiver) -> is_implemented_by trait declared ~name ~receiver)
       impl.impl_methods)

type constant_interface = { constant_type : ty }

let make_trait_reference ~arguments trait : trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Named { path = Well_known.make_path String; arguments = [] }

let find_sequence_element (sequence : ty) =
  match strip_view sequence with
  | Named { path; arguments = Type element :: _ }
    when Well_known.is List path || Well_known.find_builtin_type path = Some Array ->
      Some element
  | _ -> None

let find_list_of_array = function
  | Named { path; arguments = Type element :: _ }
    when Well_known.find_builtin_type path = Some Array ->
      Some (make_named (Well_known.make_path List) [ element ])
  | _ -> None

let find_specification_sequence_element (sequence : ty) =
  match sequence with
  | Named { path; arguments = [ Type element ] } when Well_known.is Sequence path -> Some element
  | _ -> None

module For_testing = struct
  let list_arguments substitution = substitution.arguments
end
