module Names = Resolve.Names

let head = function Types.Named { path; _ } -> Some path | _ -> None

let derivable (trait : Path.t) =
  match Well_known.of_path trait with
  | Some (Equal | Hash | Ordered | Default | Serialize | Deserialize) -> true
  | _ -> false

let index =
  Query.query ~name:"impl_index" ~phase:Phases.interfaces ~show:Path.show_package
    (fun database package ->
      List.concat_map
        (fun (declaration : Names.declaration) ->
          if declaration.ordinal <> 0 then []
          else
            match declaration.kind with
            | Impl -> (
                match Query.demand database Environment.impl_interface declaration.path with
                | Some impl when not impl.impl_broken -> (
                    match head impl.for_type with
                    | Some type_ -> [ ((impl.implements.trait, type_), declaration.path) ]
                    | None -> [])
                | _ -> [])
            | Type -> (
                match Query.demand database Environment.type_interface declaration.path with
                | Some type_interface ->
                    List.filter_map
                      (fun trait ->
                        if derivable trait then
                          Some
                            ( (trait, declaration.path),
                              (Derived { type_ = declaration.path; trait } : Path.t) )
                        else None)
                      type_interface.derives
                | None -> [])
            | _ -> [])
        (Query.demand database Names.package_declarations package))

(* A package's impls by the type they are for: each with its trait. *)
let by_type =
  Query.query ~name:"impls_by_type" ~phase:Phases.interfaces ~show:Path.show_package
    (fun database package ->
      List.fold_left
        (fun table ((trait, type_), impl) ->
          Path.Map.update type_
            (fun impls -> Some ((trait, impl) :: Option.value ~default:[] impls))
            table)
        Path.Map.empty
        (Query.demand database index package)
      |> Path.Map.map List.rev)

let impls_for database (type_ : Path.t) package =
  Option.value ~default:[] (Path.Map.find_opt type_ (Query.demand database by_type package))

let impls_in =
  Query.query ~name:"impls" ~phase:Phases.interfaces ~saved:true
    ~show:(fun (trait, type_, package) ->
      Printf.sprintf "%s for %s in %s" (Path.show trait) (Path.show type_)
        (Path.show_package package))
    (fun database ((trait : Path.t), (type_ : Path.t), package) ->
      List.filter_map
        (fun (indexed_trait, impl) -> if Path.equal indexed_trait trait then Some impl else None)
        (impls_for database type_ package))

let cursor_trait = Well_known.path Cursor

(* The cursor of a yielding function or method implements [Cursor], and no
   [impl] is written for it. Its [impl] is a derived one, named by the
   function. *)
let cursor_impl (method_ : Path.t) : Path.t = Derived { type_ = method_; trait = cursor_trait }

let cursor_uses database (type_ : Types.ty) =
  match type_ with
  | Types.Cursor { method_; arguments } -> (
      match Query.demand database Environment.signature method_ with
      | Some signature -> (
          match Types.substitution_of signature.generics arguments with
          | Some substitution -> (Types.substitute_signature substitution signature).uses
          | None -> signature.uses)
      | None -> Types.no_capabilities)
  | _ -> Types.no_capabilities

let cursor_of_impl : Path.t -> Path.t option = function
  | Derived { type_ = method_; trait } when Path.equal trait cursor_trait -> Some method_
  | _ -> None

(* The interface of a cursor's [impl]. Its generic parameters are the
   yielding method's, its [Element] is the method's yielded type, and its
   methods are the trait's methods with [Self] substituted. Every method
   except [next] is a provided method of the trait. [next] runs the method's
   own code up to its next [yield], so the associated capability set of the
   [impl] is the method's [uses]. *)
let cursor_interface database ~method_ =
  match
    ( Query.demand database Environment.signature method_,
      Query.demand database Environment.trait_interface cursor_trait )
  with
  | Some ({ output = Yields (_, element); _ } as signature), Some trait_interface ->
      let impl_generics = signature.generics in
      let for_type =
        Types.Cursor { method_; arguments = Types.generic_arguments signature.generics }
      in
      let self : Types.substitution =
        [ ({ owner = cursor_trait; name = "Self" }, Types.Type for_type) ]
      in
      let of_cursor (declared : Types.signature) =
        let declared = Types.substitute_signature self declared in
        {
          declared with
          uses =
            Types.flat_map_capabilities
              (function
                | Types.Capability_projection { base; trait; _ }
                  when Types.equal base for_type && Path.equal trait.trait cursor_trait ->
                    (signature.uses :> Types.capability list)
                | capability -> [ capability ])
              declared.uses;
        }
      in
      Some
        {
          Types.impl_generics;
          implements =
            { trait = cursor_trait; trait_arguments = []; associated = [ ("Element", element) ] };
          for_type;
          impl_uses = Types.no_capabilities;
          capability_sets =
            List.map (fun name -> (name, signature.uses)) trait_interface.associated_capabilities;
          impl_methods =
            List.map
              (fun (method_ : Types.trait_method) ->
                ( method_.method_name,
                  method_.method_receiver,
                  Types.method_in_impl ~impl_generics ~impl_uses:Types.no_capabilities
                    (of_cursor method_.method_signature) ))
              trait_interface.methods;
          impl_broken = false;
        }
  | _ -> None

(* The interface of a derived [impl]: the type's generic parameters, each
   bound by the trait, as [impl Equal for Option[Value: Equal]], and the
   trait's methods with [Self] replaced. *)
let derived_interface database ~type_ ~trait =
  match
    ( Query.demand database Environment.type_interface type_,
      Query.demand database Environment.trait_interface trait )
  with
  | _ when Option.is_some (cursor_of_impl (Derived { type_; trait })) ->
      cursor_interface database ~method_:type_
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
      let self : Types.substitution = [ ({ owner = trait; name = "Self" }, Types.Type for_type) ] in
      Some
        {
          Types.impl_generics;
          implements = trait_reference;
          for_type;
          impl_uses = Types.no_capabilities;
          capability_sets = [];
          impl_methods =
            List.map
              (fun (method_ : Types.trait_method) ->
                ( method_.method_name,
                  method_.method_receiver,
                  Types.method_in_impl ~impl_generics ~impl_uses:Types.no_capabilities
                    (Types.substitute_signature self method_.method_signature) ))
              trait_interface.methods;
          impl_broken = false;
        }
  | _ -> None

let impl_interface database (path : Path.t) =
  match path with
  | Derived { type_; trait } -> derived_interface database ~type_ ~trait
  | _ -> Query.demand database Environment.impl_interface path

let trait_substitution database (impl : Path.t) =
  Option.bind (impl_interface database impl) (fun (interface : Types.impl_interface) ->
      Option.map
        (fun trait ->
          Properties.trait_substitution trait ~self:interface.for_type interface.implements)
        (Query.demand database Environment.trait_interface interface.implements.trait))

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

let through_any ~(trait : Path.t) (method_ : Types.trait_method) : through_any =
  let self : Types.parameter = { owner = trait; name = "Self" } in
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
  let signature = method_.method_signature in
  let result = Types.result_type signature.output in
  if signature.generics <> [] then Has_generics
  else if
    List.exists (fun (info : Types.parameter_info) -> names_self info.type_) signature.parameters
    || names_self result
  then Names_self
  else Callable

let cursor_element database (method_ : Path.t) arguments =
  match Query.demand database Environment.signature method_ with
  | Some ({ output = Yields (_, element); _ } as signature) ->
      Option.map
        (fun substitution -> Types.substitute substitution element)
        (Types.substitution_of signature.generics arguments)
  | _ -> None

let copyable_path = Properties.copyable_trait
let plain_path = Properties.plain_trait

type bounds = Types.parameter -> Types.trait_reference list

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

let rec implements database ~(bounds : bounds) ?(depth = 0) ?(conditions = true) (type_ : Types.ty)
    (wanted : Types.trait_reference) : evidence option =
  let arguments_match actual_arguments =
    List.length actual_arguments = List.length wanted.trait_arguments
    && List.for_all2
         (fun wanted actual ->
           match (wanted, actual) with
           | Types.Type wanted, Types.Type actual ->
               open_type wanted || open_type actual
               || Types.equal
                    (normalize database ~bounds wanted)
                    (normalize database ~bounds actual)
           | Types.Value wanted, Types.Value actual -> wanted = actual
           | _ -> false)
         wanted.trait_arguments actual_arguments
  in
  (* The associated types that the [impl] defines must equal the ones that
     the wanted trait reference fixes. An associated type that the reference
     leaves open is the projection on the type. *)
  let associated_match ~base fixed =
    List.for_all
      (fun (name, wanted_type) ->
        let wanted_type = normalize database ~bounds wanted_type in
        if open_type wanted_type then true
        else
          match List.assoc_opt name fixed with
          | Some defined ->
              open_type defined || Types.equal (normalize database ~bounds defined) wanted_type
          | None -> (
              match (base, wanted_type) with
              | Some base, Types.Projection { base = projected; name = projected_name; _ } ->
                  Types.equal base projected && projected_name = name
              | _ -> false))
      wanted.associated
  in
  let broken_trait =
    match Query.demand database Environment.interface wanted.trait with
    | Some (Environment.Error_interface report) -> Some report
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
      || Properties.has database ~bounds ~normalize:(normalize database ~bounds) property type_
    then Some Built_in
    else None
  else if Path.equal wanted.trait Properties.storable_trait then
    if
      (not conditions)
      || Properties.storable database ~bounds ~normalize:(normalize database ~bounds) type_
    then Some Built_in
    else None
  else
    match type_ with
    | Types.Error _ | Types.Hole | Types.Variable _ -> Some (Accepted type_)
    | Types.Cursor { method_; arguments } ->
        if Path.equal wanted.trait cursor_trait then
          Option.bind (Query.demand database Environment.signature method_) (fun signature ->
              Option.map
                (fun substitution -> From_impl { impl = cursor_impl method_; substitution })
                (Types.substitution_of signature.generics arguments))
        else None
    | Types.Never | Types.Integer | Types.Literal _ | Types.Function _ -> None
    | Types.Parameter _ | Types.Projection _ ->
        if
          List.exists
            (fun (bound : Types.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:(Some type_) bound.associated)
            (Properties.known_bounds database ~bounds type_)
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
            (Properties.bound_closure database ~self:type_ trait)
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
            (fun package -> Query.demand database impls_in (wanted.trait, path, package))
            packages
        in
        List.find_map
          (fun impl_path ->
            match impl_interface database impl_path with
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
                                   (implements database ~bounds ~depth:(depth + 1) argument bound))
                               (required impl.impl_generics substitution)
                        in
                        if conditions_hold && associated_match ~base:None associated then
                          Some (From_impl { impl = impl_path; substitution })
                        else None)))
          candidates

and associated_type database ~bounds ?defining type_ (trait : Types.trait_reference) name =
  match List.assoc_opt name trait.associated with
  | Some fixed -> Some fixed
  | None -> (
      match implements database ~bounds ~conditions:false type_ trait with
      | Some (From_impl { impl; substitution }) -> (
          match impl_interface database impl with
          | Some interface ->
              Option.iter (fun defining -> defining := impl :: !defining) defining;
              Option.map (Types.substitute substitution)
                (List.assoc_opt name interface.implements.associated)
          | None -> None)
      | Some From_bound -> (
          match
            List.find_map
              (fun (bound : Types.trait_reference) -> List.assoc_opt name bound.associated)
              (Properties.known_bounds database ~bounds type_)
          with
          | Some fixed -> Some fixed
          | None -> Some (Types.Projection { base = type_; trait; name }))
      | Some From_any -> (
          match type_ with
          | Types.Any any ->
              List.find_map
                (fun (bound : Types.trait_reference) -> List.assoc_opt name bound.associated)
                (any :: Properties.bound_closure database ~self:type_ any)
          | _ -> None)
      (* [Copyable] and [Plain] have no associated types. *)
      | Some Built_in -> None
      (* An associated type of an [Error] or a [Hole] is an [Error] or a
         [Hole] too. An associated type of a type that is not inferred yet
         is unknown. *)
      | Some (Accepted (Types.Variable _)) -> None
      | Some (Accepted unknown) -> Some unknown
      | None -> None)

and capability_set database ~bounds ?(depth = 0) type_ (trait : Types.trait_reference) name =
  let projection =
    Types.capability_set [ Types.Capability_projection { base = type_; trait; name } ]
  in
  if depth > 32 then projection
  else
    match implements database ~bounds ~conditions:false type_ trait with
    | Some (From_impl { impl; substitution }) -> (
        match impl_interface database impl with
        | Some interface ->
            normalize_capabilities database ~bounds ~depth:(depth + 1)
              (Types.substitute_capabilities substitution
                 (Option.value ~default:Types.no_capabilities
                    (List.assoc_opt name interface.capability_sets)))
        | None -> Types.no_capabilities)
    | Some From_bound | Some (Accepted (Types.Variable _)) | None -> projection
    | Some (From_any | Built_in | Accepted _) -> Types.no_capabilities

and normalize_capabilities database ~bounds ?depth (capabilities : Types.capability_set) =
  let projection = function Types.Capability_projection _ -> true | _ -> false in
  if not (List.exists projection (capabilities :> Types.capability list)) then capabilities
  else
    Types.flat_map_capabilities
      (function
        | Types.Capability_projection { base; trait; name } ->
            (capability_set database ~bounds ?depth (normalize database ~bounds base)
               { trait with associated = [] } name
              :> Types.capability list)
        | capability -> [ capability ])
      capabilities

and normalize database ~bounds ?defining (type_ : Types.ty) : Types.ty =
  let normalize = normalize database ~bounds ?defining in
  let associated_type = associated_type database ~bounds ?defining in
  Types.map
    ~capabilities:(normalize_capabilities database ~bounds)
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

let signature database (path : Path.t) =
  match (Query.demand database Environment.signature path, path) with
  | Some signature, _ -> Some signature
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
      match (impl_interface database owner, trait_substitution database owner) with
      | Some impl, Some substitution ->
          Option.map
            (fun declared ->
              let signature =
                Types.method_in_impl ~impl_generics:impl.impl_generics ~impl_uses:impl.impl_uses
                  (Types.substitute_signature substitution declared)
              in
              let bounds = Types.bounds_of signature.generics in
              { signature with uses = normalize_capabilities database ~bounds signature.uses })
            (Query.demand database Environment.signature
               (Method { owner = impl.implements.trait; name; receiver }))
      | _ -> None)
  | None, _ -> None

(* Whether a type is [Copyable], [Plain], or a view, with each associated
   type that its definition's facts depend on normalized. *)
let has property database ~bounds type_ =
  Properties.has database ~bounds ~normalize:(normalize database ~bounds) property type_

let copyable = has Copyable
let plain = has Plain
let is_view = has View
let holds_function = has Holds_function

let contents database ~bounds type_ =
  Properties.contents database
    ~normalize:(fun type_ ->
      let defining = ref [] in
      let normalized = normalize database ~bounds ~defining type_ in
      (normalized, !defining))
    type_
