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

and argument = Type of ty | Value of value
and value = Known of Z.t | Value_parameter of parameter | Value_variable of int

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;
}

and function_type = {
  inputs : (mode * ty) list;
  output : ty;
  uses : capability_set;
  costs : cost list;
}

and result = Returns of ty | Lends of mode * ty

and capability =
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_projection of { base : ty; trait : trait_reference; name : string }
  | Capability_variable of int
  | Capability_error of Diagnostic.reported
  | Divergence of divergence

and divergence =
  | Always
  | Of_parameter of parameter
  | Of_impl_method of {
      self_type : ty;
      trait : trait_reference;
      name : string;
      receiver : Path.receiver;
    }
  | Of_variable of int

and capability_set = capability list
and cost = { amortized : bool; resource : resource; bound : cost_bound }
and resource = Metric of Metric.t | Calls of { capability : Path.t; method_ : string option }
and cost_bound = Order_of | No_more_than of Z.t option | Exactly_cost of Z.t option

let is_divergence = function Divergence _ -> true | _ -> false
let unconditional_divergence : capability = Divergence Always
let panic : capability = Capability (Well_known.make_path Panic)

let make_capability_set capabilities : capability_set =
  List.sort_uniq compare
    (if List.mem unconditional_divergence capabilities then
       unconditional_divergence
       :: List.filter (fun capability -> not (is_divergence capability)) capabilities
     else capabilities)

let no_capabilities : capability_set = []

let union_capabilities (left : capability_set) (right : capability_set) =
  make_capability_set (left @ right)

let list_divergence (set : capability_set) : capability_set = List.filter is_divergence set

let remove_divergence (set : capability_set) : capability_set =
  List.filter (fun capability -> not (is_divergence capability)) set

let terminates (set : capability_set) = not (List.mem unconditional_divergence set)

let has_capability_error (capabilities : capability_set) =
  List.exists (function Capability_error _ -> true | _ -> false) capabilities

let subtract_capabilities (left : capability_set) (right : capability_set) =
  let allows capability =
    List.mem capability right
    || (is_divergence capability && List.mem unconditional_divergence right)
  in
  List.filter (fun capability -> not (allows capability)) left

let is_capability_subset (smaller : capability_set) (larger : capability_set) =
  has_capability_error smaller || has_capability_error larger
  || subtract_capabilities smaller larger = []

let leave_divergence_to_parameters (uses : capability_set) : capability_set =
  let parameters =
    List.filter_map (function Capability_parameter parameter -> Some parameter | _ -> None) uses
  in
  make_capability_set
    (uses
    @
    match parameters with
    | [] -> [ unconditional_divergence ]
    | parameters -> List.map (fun parameter -> Divergence (Of_parameter parameter)) parameters)

let intersect_capabilities (sets : capability_set list) : capability_set =
  make_capability_set
    (List.filter
       (fun capability ->
         List.for_all (fun set -> subtract_capabilities [ capability ] set = []) sets)
       (List.concat sets))

let compute_missing_capabilities ~(required : capability_set) ~(available : capability_set) =
  if has_capability_error required || has_capability_error available then no_capabilities
  else subtract_capabilities required available

let flat_map_capabilities f (set : capability_set) = make_capability_set (List.concat_map f set)
let make_builtin builtin = Named { path = Intrinsic.make_builtin_path builtin; arguments = [] }
let unit = make_builtin Unit
let bool = make_builtin Bool
let make_self_parameter trait = { owner = trait; name = "Self" }
let is_self_parameter parameter = parameter.name = "Self"

let make_named path arguments =
  Named { path; arguments = List.map (fun type_ -> Type type_) arguments }

let find_builtin = function
  | Named { path; arguments = [] } -> Intrinsic.find_builtin path
  | Named { path; _ } -> (
      match Intrinsic.find_builtin path with
      | Some (Array | Storage | View | Shared) as builtin -> builtin
      | _ -> None)
  | _ -> None

let is_builtin wanted type_ = find_builtin type_ = Some wanted
let is_well_known wanted = function Named { path; _ } -> Well_known.is wanted path | _ -> false

let find_view = function
  | Named { path; arguments } when Well_known.is List path ->
      Some (Named { path = Well_known.make_path Slice; arguments })
  | Named { path; arguments = [] } when Well_known.is String path ->
      Some (Named { path = Well_known.make_path String_slice; arguments = [] })
  | Named { arguments = element :: _; _ } as array when is_builtin Array array ->
      Some (Named { path = Well_known.make_path Slice; arguments = [ element ] })
  | _ -> None

let signed_integer_types : Intrinsic.builtin list = [ Int8; Int16; Int32; Int64 ]
let unsigned_integer_types : Intrinsic.builtin list = [ UInt8; UInt16; UInt32; UInt64 ]
let integer_types = signed_integer_types @ unsigned_integer_types

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

let float_types : Intrinsic.builtin list = [ Float32; Float64 ]

let is_integer_type type_ =
  match find_builtin type_ with Some builtin -> List.mem builtin integer_types | None -> false

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

let is_signed type_ =
  match find_integer_bits type_ with Some (_, signed) -> signed | None -> false

let is_float_type type_ =
  match find_builtin type_ with Some builtin -> List.mem builtin float_types | None -> false

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
    | Any trait -> Any (substitute_trait substitution trait)
    | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> type_

and substitute_argument substitution = function
  | Type type_ -> Type (substitute substitution type_)
  | Value (Value_parameter parameter) as value -> (
      match find_argument parameter substitution with
      | Some (Value _ as replacement) -> replacement
      | _ -> value)
  | Value _ as value -> value

and substitute_capabilities substitution capabilities =
  flat_map_capabilities
    (function
      | Capability_parameter parameter as capability -> (
          match List.assoc_opt parameter substitution.capability_arguments with
          | Some replacement -> remove_divergence replacement
          | None -> [ capability ])
      | Divergence (Of_parameter parameter) as capability -> (
          match List.assoc_opt parameter substitution.capability_arguments with
          | Some replacement -> list_divergence replacement
          | None -> [ capability ])
      | Capability_projection { base; trait; name } ->
          [
            Capability_projection
              {
                base = substitute substitution base;
                trait = substitute_trait substitution trait;
                name;
              };
          ]
      | Divergence (Of_impl_method { self_type; trait; name; receiver }) ->
          [
            Divergence
              (Of_impl_method
                 {
                   self_type = substitute substitution self_type;
                   trait = substitute_trait substitution trait;
                   name;
                   receiver;
                 });
          ]
      | ( Capability _ | Capability_variable _ | Capability_error _
        | Divergence (Always | Of_variable _) ) as capability ->
          [ capability ])
    capabilities

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

let extract_result_type = function Returns type_ | Lends (_, type_) -> type_
let show_mode = function Read -> "" | Mut -> "mut " | Own -> "own "

let rec map ?(map_capabilities = Fun.id) transform type_ =
  match transform type_ with
  | Some replacement -> replacement
  | None -> (
      let map = map ~map_capabilities transform in
      let map_argument = function Type type_ -> Type (map type_) | Value _ as value -> value in
      let map_trait (reference : trait_reference) =
        {
          reference with
          trait_arguments = List.map map_argument reference.trait_arguments;
          associated = List.map (fun (name, type_) -> (name, map type_)) reference.associated;
        }
      in
      match type_ with
      | Named { path; arguments } -> Named { path; arguments = List.map map_argument arguments }
      | Projection { base; trait = reference; name } ->
          Projection { base = map base; trait = map_trait reference; name }
      | Function function_type ->
          Function
            {
              function_type with
              inputs = List.map (fun (mode, type_) -> (mode, map type_)) function_type.inputs;
              output = map function_type.output;
              uses = map_capabilities function_type.uses;
            }
      | Any reference -> Any (map_trait reference)
      | Parameter _ | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> type_)

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
  | Any reference -> trait_exists reference
  | Parameter _ | Never | Integer | Variable _ | Literal _ | Hole | Error _ -> false

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

let has_capability_variable capabilities =
  List.exists
    (function Capability_variable _ | Divergence (Of_variable _) -> true | _ -> false)
    capabilities

let may_panic capabilities =
  List.exists (function Capability path -> Well_known.is Panic path | _ -> false) capabilities

let equal left right = left = right
let is_error = function Error _ -> true | _ -> false
let is_open_type = function Error _ | Variable _ | Hole -> true | _ -> false

let rec contains_unsolved = function
  | Variable _ | Literal _ | Hole -> true
  | Named { arguments; _ } -> List.exists is_unsolved_argument arguments
  | Projection { base; trait; _ } -> contains_unsolved base || is_unsolved_trait trait
  | Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> contains_unsolved type_) inputs || contains_unsolved output
  | Any trait -> is_unsolved_trait trait
  | Parameter _ | Never | Integer | Error _ -> false

and is_unsolved_argument = function
  | Type type_ -> contains_unsolved type_
  | Value (Value_variable _) -> true
  | Value _ -> false

and is_unsolved_trait trait =
  List.exists is_unsolved_argument trait.trait_arguments
  || List.exists (fun (_, type_) -> contains_unsolved type_) trait.associated

let has_unsolved_capabilities capabilities =
  List.exists
    (function
      | Capability_variable _ | Divergence (Of_variable _) -> true
      | Capability_projection { base; _ } -> contains_unsolved base
      | Divergence (Of_impl_method { self_type; trait; _ }) ->
          contains_unsolved self_type || is_unsolved_trait trait
      | Capability _ | Capability_parameter _ | Capability_error _
      | Divergence (Always | Of_parameter _) ->
          false)
    capabilities

let has_same_clauses (left : function_type) (right : function_type) =
  left.uses = right.uses && List.sort_uniq compare left.costs = List.sort_uniq compare right.costs

let bound_implies (provided : cost_bound) (required : cost_bound) =
  match (provided, required) with
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

let show_path_name = function Path.Top { name; _ } -> name | path -> Path.show path

let show_resource = function
  | Metric metric -> Metric.show metric
  | Calls { capability; method_ } ->
      Printf.sprintf "calls(%s%s)" (show_path_name capability)
        (match method_ with Some method_ -> "." ^ method_ | None -> "")

let rec show_impl_method self_type (trait : trait_reference) name =
  Printf.sprintf "`%s`'s `impl` of `%s.%s`" (show self_type) (show_path_name trait.trait) name

and show_capability = function
  | Capability path -> show_path_name path
  | Capability_parameter { name; _ } | Divergence (Of_parameter { name; _ }) -> "generic " ^ name
  | Capability_projection { base; name; _ } -> show base ^ "." ^ name
  | Capability_variable _ | Capability_error _ | Divergence (Of_variable _) -> "_"
  | Divergence Always -> "may not terminate"
  | Divergence (Of_impl_method { self_type; name; _ }) ->
      Printf.sprintf "may not terminate where %s.%s may not" (show self_type) name

and show = function
  | Named { path; arguments = [] } -> show_path_name path
  | Named { path; arguments } ->
      Printf.sprintf "%s[%s]" (show_path_name path)
        (String.concat ", " (List.map show_argument arguments))
  | Parameter { name; _ } -> name
  | Projection { base; name; _ } -> show base ^ "." ^ name
  | Function function_type -> show_function function_type
  | Any trait -> "any " ^ show_trait trait
  | Never -> "Never"
  | Integer -> "Integer"
  | Variable _ | Literal _ | Hole | Error _ -> "_"

and show_argument = function
  | Type type_ -> show type_
  | Value (Known value) -> Z.to_string value
  | Value (Value_parameter { name; _ }) -> name
  | Value (Value_variable _) -> "_"

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
  | [] -> show_path_name trait.trait
  | all -> Printf.sprintf "%s[%s]" (show_path_name trait.trait) (String.concat ", " all)

and show_output = function
  | Returns type_ when type_ = unit -> ""
  | Returns type_ -> " -> " ^ show type_
  | Lends (written, type_) -> " lends " ^ show_mode written ^ show type_

and show_function (function_type : function_type) =
  let inputs =
    String.concat ", "
      (List.map (fun (written, type_) -> show_mode written ^ show type_) function_type.inputs)
  in
  let base = Printf.sprintf "fn(%s)%s" inputs (show_output (Returns function_type.output)) in
  let uses = List.map show_capability (remove_divergence function_type.uses) in
  let is_finite =
    list_divergence function_type.uses = []
    && not (List.exists (fun (cost : cost) -> cost.resource = Metric Time) function_type.costs)
  in
  let costs =
    (if is_finite then [ "cost time finite" ] else [])
    @ List.map
        (fun (cost : cost) ->
          let bound =
            match cost.bound with
            | Order_of -> "O(...)"
            | No_more_than (Some value) -> "<= " ^ Z.to_string value
            | No_more_than None -> "<= ..."
            | Exactly_cost (Some value) -> "== " ^ Z.to_string value
            | Exactly_cost None -> "== ..."
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

let describe = function
  | Literal (Integer_literal, _) -> "an integer"
  | Literal (Float_literal, _) -> "a float"
  | type_ -> "`" ^ show type_ ^ "`"

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
    (fun parameter ->
      ( parameter.name,
        make_capability_set [ Capability_parameter parameter; Divergence (Of_parameter parameter) ]
      ))
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

type parameter_info = { name : string; mode : mode; type_ : ty; has_default : bool }

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

type signature = {
  generics : generic list;
  capability_parameters : parameter list;
  receiver : (Path.receiver * ty) option;
  parameters : parameter_info list;
  output : result;
  uses : capability_set;
  costs : cost list;
  specification_only : bool;
  capture_free_parameters : string list;
}

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
  let receiver =
    match signature.receiver with
    | Some (Static, _) | None -> []
    | Some (Read, type_) -> [ (Read, type_) ]
    | Some (Mut, type_) -> [ (Mut, type_) ]
    | Some (Own, type_) -> [ (Own, type_) ]
  in
  match signature.output with
  | Lends _ -> None
  | Returns output ->
      Some
        {
          inputs =
            receiver
            @ List.map (fun parameter -> (parameter.mode, parameter.type_)) signature.parameters;
          output;
          uses = signature.uses;
          costs = signature.costs;
        }

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type
  | Builtin_type of Intrinsic.builtin

type type_interface = {
  type_generics : generic list;
  shape : shape;
  opaque : bool;
  derives : Path.t list;
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

type trait_interface = {
  trait_generics : generic list;
  requires : trait_reference list;
  associated_types : associated_type list;
  associated_capabilities : string list;
  methods : trait_method list;
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

module For_testing = struct
  let list_arguments substitution = substitution.arguments
end
