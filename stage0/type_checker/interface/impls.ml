module Names = Resolve.Names
open Environment

let head = function Types.Named { path; _ } -> Some path | _ -> None

let impls_for (lookups : Lookups.t) (type_ : Path.t) package =
  lookups.names.impls_of_type package type_

let impls_in lookups ~trait ~type_ package =
  List.filter_map
    (fun (indexed_trait, impl) -> if Path.equal indexed_trait trait then Some impl else None)
    (impls_for lookups type_ package)

let impls_of (lookups : Lookups.t) ~trait package =
  List.sort_uniq Path.compare (lookups.names.impls_of_trait package trait)

let cursor_trait = Well_known.path Cursor

let derived_interface lookups ~type_ ~trait =
  match (Definition.type_interface lookups type_, Definition.trait_interface lookups trait) with
  | Some type_interface, Some trait_interface ->
      let trait_reference : Types.trait_reference =
        { trait; trait_arguments = []; associated = [] }
      in
      let impl_generics =
        List.map
          (fun (generic : Types.generic) ->
            match generic.kind with
            | Type_generic bounds ->
                { generic with kind = Type_generic (bounds @ [ trait_reference ]) }
            | Value_generic | Capability_generic -> generic)
          type_interface.type_generics
      in
      let for_type =
        Types.Named
          { path = type_; arguments = Types.generic_arguments type_interface.type_generics }
      in
      Some
        {
          Types.impl_generics;
          implements = trait_reference;
          for_type;
          impl_uses = Types.no_capabilities;
          capability_sets = [];
          impl_methods =
            List.map
              (fun (method_ : Types.trait_method) -> (method_.method_name, method_.method_receiver))
              trait_interface.methods;
        }
  | _ -> None

let impl_interface (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Derived _ -> lookups.derived_interface path
  | _ -> Definition.impl_interface lookups path

let trait_substitution lookups (impl : Path.t) =
  Option.bind (impl_interface lookups impl) (fun (interface : Types.impl_interface) ->
      Option.map
        (fun trait ->
          Properties.trait_substitution trait ~self:interface.for_type interface.implements)
        (Definition.trait_interface lookups interface.implements.trait))

let open_type = function Types.Error _ | Types.Variable _ | Types.Hole -> true | _ -> false

let rec match_type ~variables (substitution : Types.substitution) pattern type_ =
  match (pattern, type_) with
  | Types.Parameter parameter, _ when List.mem parameter variables -> (
      match List.assoc_opt parameter substitution with
      | Some (Types.Type bound) ->
          if Types.equal bound type_ || open_type type_ then Some substitution else None
      | Some (Types.Value _ | Types.Capabilities _) -> None
      | None -> Some ((parameter, Types.Type type_) :: substitution))
  | _, argument_type when open_type argument_type -> Some substitution
  | Types.Named left, Types.Named right when Path.equal left.path right.path ->
      match_arguments ~variables substitution left.arguments right.arguments
  | _ -> if Types.equal pattern type_ then Some substitution else None

and match_arguments ~variables substitution patterns arguments =
  if List.length patterns <> List.length arguments then None
  else
    List.fold_left2
      (fun substitution pattern argument ->
        match substitution with
        | None -> None
        | Some substitution -> (
            match (pattern, argument) with
            | Types.Type pattern, Types.Type argument ->
                match_type ~variables substitution pattern argument
            | Types.Value (Types.Value_parameter parameter), Types.Value value
              when List.mem parameter variables -> (
                match List.assoc_opt parameter substitution with
                | Some (Types.Value bound) -> if bound = value then Some substitution else None
                | _ -> Some ((parameter, Types.Value value) :: substitution))
            | Types.Value left, Types.Value right -> (
                if left = right then Some substitution
                else match right with Types.Value_variable _ -> Some substitution | _ -> None)
            | _ -> None))
      (Some substitution) patterns arguments

type evidence =
  | From_impl of { impl : Path.t; substitution : Types.substitution }
  | From_bound
  | From_any
  | Built_in
  | Accepted of Types.ty

type through_any = Callable | Has_generics | Names_self

let through_any lookups ~(any : Types.trait_reference) ~(trait : Path.t)
    (method_ : Types.trait_method) : through_any =
  let self = Definition.make_self_parameter any.trait in
  let names_self type_ =
    let mentions_self = ref false in
    ignore
      (Types.map
         (function
           | Types.Projection { base = Types.Parameter base; _ } as projected when base = self ->
               Some projected
           | Types.Parameter parameter as named when parameter = self ->
               mentions_self := true;
               Some named
           | _ -> None)
         type_);
    !mentions_self
  in
  let reference =
    match
      List.find_opt
        (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
        (Properties.bound_closure lookups ~self:(Types.Parameter self) any)
    with
    | Some reference -> reference
    | None -> { trait; trait_arguments = []; associated = [] }
  in
  let substitution =
    match Definition.trait_interface lookups trait with
    | Some interface ->
        Properties.trait_substitution interface ~self:(Types.Parameter self) reference
    | None -> []
  in
  let signature =
    Types.substitute_signature substitution
      (Definition.method_signature lookups ~owner:trait method_)
  in
  let result = Types.result_type signature.output in
  if signature.generics <> [] then Has_generics
  else if
    List.exists (fun (info : Types.parameter_info) -> names_self info.type_) signature.parameters
    || names_self result
  then Names_self
  else Callable

let copyable_path = Properties.copyable_trait
let plain_path = Properties.plain_trait

type bounds = Types.parameter -> Types.trait_reference list

let no_bounds _ = []

let required (generics : Types.generic list) (substitution : Types.substitution) =
  List.concat_map
    (fun (generic : Types.generic) ->
      match (generic.kind, List.assoc_opt generic.generic substitution) with
      | Type_generic generic_bounds, Some (Types.Type argument) ->
          List.map
            (fun bound -> (argument, Types.substitute_trait substitution bound))
            generic_bounds
      | _ -> [])
    generics

let rec implements lookups ~(bounds : bounds) ?(depth = 0) ?(conditions = true) (type_ : Types.ty)
    (wanted : Types.trait_reference) : evidence option =
  let arguments_match actual_arguments =
    List.length actual_arguments = List.length wanted.trait_arguments
    && List.for_all2
         (fun wanted actual ->
           match (wanted, actual) with
           | Types.Type wanted, Types.Type actual ->
               open_type wanted || open_type actual
               || Types.equal (normalize lookups ~bounds wanted) (normalize lookups ~bounds actual)
           | Types.Value wanted, Types.Value actual -> wanted = actual
           | _ -> false)
         wanted.trait_arguments actual_arguments
  in
  let associated_match ~base fixed =
    List.for_all
      (fun (name, wanted_type) ->
        let wanted_type = normalize lookups ~bounds wanted_type in
        if open_type wanted_type then true
        else
          match List.assoc_opt name fixed with
          | Some defined ->
              open_type defined || Types.equal (normalize lookups ~bounds defined) wanted_type
          | None -> (
              match (base, wanted_type) with
              | Some base, Types.Projection { base = projected; name = projected_name; _ } ->
                  Types.equal base projected && projected_name = name
              | _ -> false))
      wanted.associated
  in
  let broken_trait =
    match Definition.interface lookups wanted.trait with
    | Some (Error_interface report) -> Some report
    | _ -> None
  in
  if depth > 32 then None
  else if Option.is_some broken_trait then
    Option.map (fun report -> Accepted (Types.Error report)) broken_trait
  else if Path.equal wanted.trait copyable_path || Path.equal wanted.trait plain_path then
    let property : Properties.property =
      if Path.equal wanted.trait plain_path then Plain else Copyable
    in
    if
      (not conditions)
      || Properties.has lookups ~bounds ~normalize:(normalize lookups ~bounds) property type_
    then Some Built_in
    else None
  else if Path.equal wanted.trait Properties.storable_trait then
    if
      (not conditions)
      || Properties.storable lookups ~bounds ~normalize:(normalize lookups ~bounds) type_
    then Some Built_in
    else None
  else
    match type_ with
    | Types.Error _ | Types.Hole | Types.Variable _ -> Some (Accepted type_)
    | Types.Never | Types.Integer | Types.Literal _ | Types.Function _ -> None
    | Types.Parameter _ | Types.Projection _ ->
        if
          List.exists
            (fun (bound : Types.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:(Some type_) bound.associated)
            (Properties.known_bounds lookups ~bounds type_)
        then Some From_bound
        else None
    | Types.Any trait ->
        if
          List.exists
            (fun (bound : Types.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:None
                   (if Path.equal bound.trait trait.trait then trait.associated
                    else bound.associated))
            (Properties.bound_closure lookups ~self:type_ trait)
        then Some From_any
        else None
    | Types.Named { path; _ } ->
        let packages =
          List.sort_uniq compare
            (Path.package wanted.trait :: Path.package path
            :: List.filter_map
                 (function
                   | Types.Type (Types.Named { path; _ }) -> Some (Path.package path) | _ -> None)
                 wanted.trait_arguments)
        in
        let candidates =
          List.concat_map
            (fun package -> impls_in lookups ~trait:wanted.trait ~type_:path package)
            packages
        in
        List.find_map
          (fun impl_path ->
            match impl_interface lookups impl_path with
            | None -> None
            | Some impl -> (
                let variables =
                  List.map (fun (generic : Types.generic) -> generic.generic) impl.impl_generics
                in
                match match_type ~variables [] impl.for_type type_ with
                | None -> None
                | Some substitution -> (
                    match
                      match_arguments ~variables substitution impl.implements.trait_arguments
                        wanted.trait_arguments
                    with
                    | None -> None
                    | Some substitution ->
                        let associated =
                          List.map
                            (fun (name, type_) -> (name, Types.substitute substitution type_))
                            impl.implements.associated
                        in
                        let conditions_hold =
                          (not conditions)
                          || List.for_all
                               (fun (argument, bound) ->
                                 Option.is_some
                                   (implements lookups ~bounds ~depth:(depth + 1) argument bound))
                               (required impl.impl_generics substitution)
                        in
                        if conditions_hold && associated_match ~base:None associated then
                          Some (From_impl { impl = impl_path; substitution })
                        else None)))
          candidates

and associated_type lookups ~bounds ?defining type_ (trait : Types.trait_reference) name =
  match List.assoc_opt name trait.associated with
  | Some fixed -> Some fixed
  | None -> (
      match implements lookups ~bounds ~conditions:false type_ trait with
      | Some (From_impl { impl; substitution }) -> (
          match impl_interface lookups impl with
          | Some interface ->
              Option.iter (fun defining -> defining := impl :: !defining) defining;
              Option.map (Types.substitute substitution)
                (List.assoc_opt name interface.implements.associated)
          | None -> None)
      | Some From_bound -> (
          match
            List.find_map
              (fun (bound : Types.trait_reference) -> List.assoc_opt name bound.associated)
              (Properties.known_bounds lookups ~bounds type_)
          with
          | Some fixed -> Some fixed
          | None -> Some (Types.Projection { base = type_; trait; name }))
      | Some From_any -> (
          match type_ with
          | Types.Any any ->
              List.find_map
                (fun (bound : Types.trait_reference) -> List.assoc_opt name bound.associated)
                (any :: Properties.bound_closure lookups ~self:type_ any)
          | _ -> None)
      | Some Built_in -> None
      | Some (Accepted (Types.Variable _)) -> None
      | Some (Accepted unknown) -> Some unknown
      | None -> None)

and capability_set lookups ~bounds ?(depth = 0) type_ (trait : Types.trait_reference) name =
  let projection =
    Types.capability_set [ Types.Capability_projection { base = type_; trait; name } ]
  in
  if depth > 32 then projection
  else
    match implements lookups ~bounds ~conditions:false type_ trait with
    | Some (From_impl { impl; substitution }) -> (
        match impl_interface lookups impl with
        | Some interface ->
            normalize_capabilities lookups ~bounds ~depth:(depth + 1)
              (Types.substitute_capabilities substitution
                 (Option.value ~default:Types.no_capabilities
                    (List.assoc_opt name interface.capability_sets)))
        | None -> Types.no_capabilities)
    | Some From_bound | Some (Accepted (Types.Variable _)) | None -> projection
    | Some (From_any | Built_in | Accepted _) -> Types.no_capabilities

and normalize_capabilities lookups ~bounds ?depth (capabilities : Types.capability_set) =
  let projection = function Types.Capability_projection _ -> true | _ -> false in
  if not (List.exists projection (capabilities :> Types.capability list)) then capabilities
  else
    Types.flat_map_capabilities
      (function
        | Types.Capability_projection { base; trait; name } ->
            (capability_set lookups ~bounds ?depth (normalize lookups ~bounds base)
               { trait with associated = [] } name
              :> Types.capability list)
        | capability -> [ capability ])
      capabilities

and normalize lookups ~bounds ?defining (type_ : Types.ty) : Types.ty =
  let normalize = normalize lookups ~bounds ?defining in
  let associated_type = associated_type lookups ~bounds ?defining in
  Types.map
    ~capabilities:(normalize_capabilities lookups ~bounds)
    (function
      | Types.Projection { base; trait; name } -> (
          let base = normalize base in
          match base with
          | Types.Variable _ | Types.Hole -> Some (Types.Projection { base; trait; name })
          | Types.Error _ -> Some base
          | Types.Parameter _ | Types.Projection _ -> (
              match associated_type base trait name with
              | Some (Types.Projection _ as projection) -> Some projection
              | Some fixed when not (Types.is_error fixed) -> Some (normalize fixed)
              | _ -> Some (Types.Projection { base; trait; name }))
          | _ -> (
              match associated_type base trait name with
              | Some fixed -> Some (normalize fixed)
              | None -> Some (Types.Projection { base; trait; name })))
      | _ -> None)
    type_

let signature lookups (path : Path.t) =
  match (Definition.signature lookups path, path) with
  | Some signature, _ -> Some signature
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
      match (impl_interface lookups owner, trait_substitution lookups owner) with
      | Some impl, Some substitution ->
          Option.map
            (fun declared ->
              let signature =
                Types.method_in_impl ~impl_generics:impl.impl_generics ~impl_uses:impl.impl_uses
                  (Types.substitute_signature substitution declared)
              in
              let bounds = Types.bounds_of signature.generics in
              { signature with uses = normalize_capabilities lookups ~bounds signature.uses })
            (Definition.signature lookups
               (Method { owner = impl.implements.trait; name; receiver }))
      | _ -> None)
  | None, _ -> None

let has property lookups ~bounds type_ =
  Properties.has lookups ~bounds ~normalize:(normalize lookups ~bounds) property type_

let copyable = has Copyable
let plain = has Plain
let is_view = has View
let holds_function = has Holds_function

let contents lookups ~bounds type_ =
  Properties.contents lookups
    ~normalize:(fun type_ ->
      let defining = ref [] in
      let normalized = normalize lookups ~bounds ~defining type_ in
      (normalized, !defining))
    type_
