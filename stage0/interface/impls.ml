(* Finding the [impl] of a trait for a type, and normalizing associated
   types. See TYPECHECKER.md, "Finding an impl" and "Traits and impls across
   a package".

   An [impl] lives in the package of its trait, of its type, or of the
   outermost type of one of the trait's arguments, so finding one looks in
   those packages only. Each package's [impl]s are indexed once, by trait
   and type, and each question is a query over that index, so adding an
   [impl] re-checks only the definitions whose question's answer
   changed. *)

module T = Types
module Names = Resolve.Names

(* The outermost path of a type, which an [impl] is chosen by. *)
let head = function T.Named { path; _ } -> Some path | _ -> None
let derivable_names = [ "Equal"; "Hash"; "Ordered"; "Default" ]

let derivable (trait : Path.t) =
  match trait with
  | Top { module_ = { package = "standard"; modules = [ "core" ] }; name } ->
      List.mem name derivable_names
  | _ -> false

(* Every [impl] of a package, written or derived, by trait and type
   constructor. *)
let index =
  Query.query ~name:"impl_index" ~show:Fun.id (fun database package ->
      match Workspace.package database package with
      | None -> []
      | Some package ->
          List.concat_map
            (fun module_ ->
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
                (Query.demand database Names.declarations module_))
            package.modules)

let impls_in =
  Query.query ~name:"impls"
    ~show:(fun (trait, type_, package) ->
      Printf.sprintf "%s for %s in %s" (Path.show trait) (Path.show type_) package)
    (fun database ((trait : Path.t), (type_ : Path.t), package) ->
      List.filter_map
        (fun ((indexed_trait, indexed_type), impl) ->
          if Path.equal indexed_trait trait && Path.equal indexed_type type_ then Some impl
          else None)
        (Query.demand database index package))

(* The interface of a derived [impl]: the type's generic parameters, each
   bound by the trait, as [impl Equal for Option[Value: Equal]], and the
   trait's methods with [Self] replaced. *)
let derived_interface database ~type_ ~trait =
  match
    ( Query.demand database Environment.type_interface type_,
      Query.demand database Environment.trait_interface trait )
  with
  | Some type_interface, Some trait_interface ->
      let trait_reference : T.trait_reference = { trait; trait_arguments = []; associated = [] } in
      let impl_generics =
        List.map
          (fun (generic : T.generic) ->
            match generic.kind with
            | Type_generic bounds ->
                { generic with kind = Type_generic (bounds @ [ trait_reference ]) }
            | Value_generic | Capability_generic -> generic)
          type_interface.type_generics
      in
      let for_type =
        T.Named
          { path = type_; arguments = Environment.generic_arguments type_interface.type_generics }
      in
      let self : T.substitution = [ ({ owner = trait; name = "Self" }, T.Type for_type) ] in
      let substitute = T.substitute self in
      Some
        {
          T.impl_generics;
          implements = trait_reference;
          for_type;
          impl_uses = [];
          impl_methods =
            List.map
              (fun (method_ : T.trait_method) ->
                let signature = method_.method_signature in
                ( method_.method_name,
                  method_.method_receiver,
                  {
                    signature with
                    receiver =
                      Option.map
                        (fun (receiver, type_) -> (receiver, substitute type_))
                        signature.receiver;
                    parameters =
                      List.map
                        (fun (parameter : T.parameter_info) ->
                          { parameter with type_ = substitute parameter.type_ })
                        signature.parameters;
                    output =
                      (match signature.output with
                      | Returns type_ -> Returns (substitute type_)
                      | Yields (mode, type_) -> Yields (mode, substitute type_)
                      | Lends (mode, type_) -> Lends (mode, substitute type_));
                  } ))
              trait_interface.methods;
          impl_broken = false;
        }
  | _ -> None

let impl_interface database (path : Path.t) =
  match path with
  | Derived { type_; trait } -> derived_interface database ~type_ ~trait
  | _ -> Query.demand database Environment.impl_interface path

(* Matching *)

let open_type = function T.Error | T.Variable _ | T.Hole -> true | _ -> false

(* Matches a type with an [impl]'s generic parameters in it against a type,
   extending the substitution, or fails. Inference variables and errors
   match anything, since a statement that has them is still being
   checked. *)
let rec match_type ~variables (substitution : T.substitution) pattern type_ =
  match (pattern, type_) with
  | T.Parameter parameter, _ when List.mem parameter variables -> (
      match List.assoc_opt parameter substitution with
      | Some (T.Type bound) ->
          if T.equal bound type_ || open_type type_ then Some substitution else None
      | Some (T.Value _ | T.Capabilities _) -> None
      | None -> Some ((parameter, T.Type type_) :: substitution))
  | _, t when open_type t -> Some substitution
  | T.Named left, T.Named right when Path.equal left.path right.path ->
      match_arguments ~variables substitution left.arguments right.arguments
  | _ -> if T.equal pattern type_ then Some substitution else None

and match_arguments ~variables substitution patterns arguments =
  if List.length patterns <> List.length arguments then None
  else
    List.fold_left2
      (fun substitution pattern argument ->
        match substitution with
        | None -> None
        | Some substitution -> (
            match (pattern, argument) with
            | T.Type pattern, T.Type argument -> match_type ~variables substitution pattern argument
            | T.Value (T.Value_parameter parameter), T.Value value when List.mem parameter variables
              -> (
                match List.assoc_opt parameter substitution with
                | Some (T.Value bound) -> if bound = value then Some substitution else None
                | _ -> Some ((parameter, T.Value value) :: substitution))
            | T.Value left, T.Value right -> (
                if left = right then Some substitution
                else match right with T.Value_variable _ -> Some substitution | _ -> None)
            | _ -> None))
      (Some substitution) patterns arguments

(* Evidence *)

type evidence =
  | From_impl of { impl : Path.t; substitution : T.substitution }
  | From_bound of T.parameter  (** A generic parameter's bound, or a trait it requires. *)
  | From_any  (** [any Trait] implements its trait. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)
  | Accepted
      (** An [Error] or [Hole], or a trait whose definition did not parse: accepted silently. *)

let copyable_path = Properties.copyable_trait
let plain_path = Properties.plain_trait

(* The bounds in scope where a question is asked: each generic parameter's
   bounds, as the definition asking declares them. *)
type bounds = T.parameter -> T.trait_reference list

let rec implements database ~(bounds : bounds) ?(depth = 0) (type_ : T.ty)
    (wanted : T.trait_reference) : evidence option =
  let arguments_match given_arguments =
    List.length given_arguments = List.length wanted.trait_arguments
    && List.for_all2
         (fun wanted given ->
           match (wanted, given) with
           | T.Type wanted, T.Type given ->
               open_type wanted || open_type given
               || T.equal (normalize database ~bounds wanted) (normalize database ~bounds given)
           | T.Value wanted, T.Value given -> wanted = given
           | _ -> false)
         wanted.trait_arguments given_arguments
  in
  (* The associated types the answer fixes must be the ones the question
     asks for. One a bound leaves open is the projection of the type. *)
  let associated_match ~base fixed =
    List.for_all
      (fun (name, wanted_type) ->
        let wanted_type = normalize database ~bounds wanted_type in
        if open_type wanted_type then true
        else
          match List.assoc_opt name fixed with
          | Some given -> open_type given || T.equal (normalize database ~bounds given) wanted_type
          | None -> (
              match (base, wanted_type) with
              | Some base, T.Projection { base = projected; name = projected_name; _ } ->
                  T.equal base projected && projected_name = name
              | _ -> false))
      wanted.associated
  in
  if depth > 32 then None
  else if
    Query.demand database Environment.interface wanted.trait = Some Environment.Error_interface
  then Some Accepted
  else if Path.equal wanted.trait copyable_path || Path.equal wanted.trait plain_path then
    if
      (Path.equal wanted.trait copyable_path && Properties.copyable database ~bounds type_)
      || (Path.equal wanted.trait plain_path && Properties.plain database ~bounds type_)
    then Some Built_in
    else None
  else
    match type_ with
    | T.Error | T.Hole | T.Variable _ -> Some Accepted
    | T.Never | T.Integer | T.Literal _ | T.Function _ | T.Cursor _ -> None
    | T.Parameter _ | T.Projection _ ->
        if
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:(Some type_) bound.associated)
            (Properties.known_bounds database ~bounds type_)
        then Some (match type_ with T.Parameter parameter -> From_bound parameter | _ -> Accepted)
        else None
    | T.Any trait ->
        if
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:None
                   (if Path.equal bound.trait trait.trait then trait.associated
                    else bound.associated))
            (Properties.bound_closure database ~self:type_ trait)
        then Some From_any
        else None
    | T.Named { path; _ } ->
        let packages =
          List.sort_uniq compare
            (Path.package wanted.trait :: Path.package path
            :: List.filter_map
                 (function T.Type (T.Named { path; _ }) -> Some (Path.package path) | _ -> None)
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
                  List.map (fun (generic : T.generic) -> generic.generic) impl.impl_generics
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
                            (fun (name, type_) -> (name, T.substitute substitution type_))
                            impl.implements.associated
                        in
                        let conditions_hold =
                          List.for_all
                            (fun (generic : T.generic) ->
                              match generic.kind with
                              | Type_generic generic_bounds -> (
                                  match List.assoc_opt generic.generic substitution with
                                  | Some (T.Type argument) ->
                                      List.for_all
                                        (fun bound ->
                                          Option.is_some
                                            (implements database ~bounds ~depth:(depth + 1) argument
                                               (T.substitute_trait substitution bound)))
                                        generic_bounds
                                  | _ -> true)
                              | Value_generic | Capability_generic -> true)
                            impl.impl_generics
                        in
                        if conditions_hold && associated_match ~base:None associated then
                          Some (From_impl { impl = impl_path; substitution })
                        else None)))
          candidates

(* The associated type a trait's [impl] for a type chooses, or [None]. *)
and associated_type database ~bounds type_ (trait : T.trait_reference) name =
  match List.assoc_opt name trait.associated with
  | Some fixed -> Some fixed
  | None -> (
      match implements database ~bounds type_ trait with
      | Some (From_impl { impl; substitution }) -> (
          match impl_interface database impl with
          | Some impl ->
              Option.map (T.substitute substitution)
                (List.assoc_opt name impl.implements.associated)
          | None -> None)
      | Some (From_bound _) -> (
          match
            List.find_map
              (fun (bound : T.trait_reference) -> List.assoc_opt name bound.associated)
              (Properties.known_bounds database ~bounds type_)
          with
          | Some fixed -> Some fixed
          | None -> Some (T.Projection { base = type_; trait; name }))
      | Some From_any -> (
          match type_ with
          | T.Any any ->
              List.find_map
                (fun (bound : T.trait_reference) -> List.assoc_opt name bound.associated)
                (any :: Properties.bound_closure database ~self:type_ any)
          | _ -> None)
      | Some (Accepted | Built_in) -> Some T.Error
      | None -> None)

(* Replaces every projection whose base is known by what the [impl]
   chooses. A projection on a generic parameter stays, unless a bound fixes
   it. *)
and normalize database ~bounds (type_ : T.ty) : T.ty =
  T.map
    (function
      | T.Projection { base; trait; name } -> (
          let base = normalize database ~bounds base in
          match base with
          | T.Variable _ | T.Hole -> Some (T.Projection { base; trait; name })
          | T.Error -> Some T.Error
          | T.Parameter _ | T.Projection _ -> (
              match associated_type database ~bounds base trait name with
              | Some (T.Projection _ as projection) -> Some projection
              | Some fixed when fixed <> T.Error -> Some (normalize database ~bounds fixed)
              | _ -> Some (T.Projection { base; trait; name }))
          | _ -> (
              match associated_type database ~bounds base trait name with
              | Some fixed -> Some (normalize database ~bounds fixed)
              | None -> Some T.Error))
      | _ -> None)
    type_
