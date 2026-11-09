(* Finding the [impl] of a trait for a type, and normalizing associated
   types. See TYPECHECKER.md, "Finding an impl" and "Traits and impls across
   a package".

   An [impl] lives in the package of its trait, of its type, or of the
   outermost type of one of the trait's arguments, so finding one looks in
   those packages only, each with its own query. Adding an [impl] then
   re-checks only the definitions that asked that question. *)

module T = Types
module Names = Resolve.Names

(* The outermost path of a type, which an [impl] is chosen by. *)
let head = function T.Named { path; _ } -> Some path | _ -> None
let package_of (path : Path.t) = Path.package path
let derived_path ~type_ ~trait : Path.t = Derived { type_; trait }

(* The [impl]s, written or derived, of a trait for a type constructor in one
   package. *)
let impls_in =
  Query.query ~name:"impls"
    ~show:(fun (trait, type_, package) ->
      Printf.sprintf "%s for %s in %s" (Path.show trait) (Path.show type_) package)
    (fun database ((trait : Path.t), (type_ : Path.t), package) ->
      match Workspace.package database package with
      | None -> []
      | Some package ->
          List.concat_map
            (fun module_ ->
              List.filter_map
                (fun (declaration : Names.declaration) ->
                  if declaration.ordinal <> 0 then None
                  else
                    match declaration.kind with
                    | Impl -> (
                        match Query.demand database Environment.impl_interface declaration.path with
                        | Some impl
                          when Path.equal impl.implements.trait trait
                               && head impl.for_type = Some type_ ->
                            Some declaration.path
                        | _ -> None)
                    | Type when Path.equal declaration.path type_ -> (
                        match Query.demand database Environment.type_interface declaration.path with
                        | Some type_interface
                          when List.exists (Path.equal trait) type_interface.derives ->
                            Some (derived_path ~type_ ~trait)
                        | _ -> None)
                    | _ -> None)
                (Query.demand database Names.declarations module_))
            package.modules)

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
      Some
        {
          T.impl_generics;
          implements = trait_reference;
          for_type;
          impl_uses = [];
          impl_methods =
            List.map
              (fun (method_ : T.trait_method) ->
                ( method_.method_name,
                  method_.method_receiver,
                  {
                    method_.method_signature with
                    receiver =
                      Option.map
                        (fun (receiver, type_) -> (receiver, T.substitute self type_))
                        method_.method_signature.receiver;
                    parameters =
                      List.map
                        (fun (parameter : T.parameter_info) ->
                          { parameter with type_ = T.substitute self parameter.type_ })
                        method_.method_signature.parameters;
                    output =
                      (match method_.method_signature.output with
                      | Returns type_ -> Returns (T.substitute self type_)
                      | Yields (mode, type_) -> Yields (mode, T.substitute self type_)
                      | Lends (mode, type_) -> Lends (mode, T.substitute self type_));
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

(* Matches a type with an [impl]'s generic parameters in it against a type,
   extending the substitution, or fails. Inference variables and errors
   match anything, since a statement that has them is still being
   checked. *)
let rec match_type ~variables (substitution : T.substitution) pattern type_ =
  match (pattern, type_) with
  | T.Parameter parameter, _ when List.mem parameter variables -> (
      match List.assoc_opt parameter substitution with
      | Some (T.Type bound) -> if T.equal bound type_ then Some substitution else None
      | Some (T.Value _) -> None
      | None -> Some ((parameter, T.Type type_) :: substitution))
  | _, (T.Error | T.Variable _ | T.Hole) -> Some substitution
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
  | Accepted  (** An [Error] or [Hole], or a definition that did not parse: accepted silently. *)

let copyable_path = Properties.copyable_trait
let plain_path = Properties.plain_trait

(* The bounds in scope where a question is asked: a generic parameter's
   bounds, as the definition asking declares them. *)
type bounds = T.parameter -> T.trait_reference list

let bound_closure = Properties.bound_closure

let arguments_match wanted given =
  List.length wanted = List.length given
  && List.for_all2
       (fun wanted given ->
         match (wanted, given) with
         | T.Type wanted, T.Type given -> (
             T.equal wanted given
             ||
             match (wanted, given) with
             | (T.Error | T.Variable _ | T.Hole), _ | _, (T.Error | T.Variable _ | T.Hole) -> true
             | _ -> false)
         | T.Value wanted, T.Value given -> wanted = given
         | _ -> false)
       wanted given

let associated_match (wanted : T.trait_reference) (given : (string * T.ty) list) =
  List.for_all
    (fun (name, type_) ->
      match List.assoc_opt name given with
      | Some fixed -> T.equal fixed type_ || type_ = T.Error
      | None -> true)
    wanted.associated

let rec implements database ~(bounds : bounds) ?(depth = 0) (type_ : T.ty)
    (wanted : T.trait_reference) : evidence option =
  if depth > 32 then None
  else if Path.equal wanted.trait copyable_path || Path.equal wanted.trait plain_path then
    if
      (Path.equal wanted.trait copyable_path && Properties.copyable database ~bounds type_)
      || (Path.equal wanted.trait plain_path && Properties.plain database ~bounds type_)
    then Some Built_in
    else None
  else
    match type_ with
    | T.Error | T.Hole | T.Never | T.Variable _ -> Some Accepted
    | T.Parameter parameter ->
        if
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match wanted.trait_arguments bound.trait_arguments
              && associated_match wanted bound.associated)
            (List.concat_map (bound_closure database) (bounds parameter))
        then Some (From_bound parameter)
        else None
    | T.Any trait ->
        if
          List.exists
            (fun (bound : T.trait_reference) -> Path.equal bound.trait wanted.trait)
            (bound_closure database trait)
        then Some From_any
        else None
    | T.Named { path; _ } -> (
        match Intrinsic.builtin_of_path path with
        | _ ->
            let packages =
              List.sort_uniq compare
                (package_of wanted.trait :: package_of path
                :: List.filter_map
                     (function T.Type (T.Named { path; _ }) -> Some (package_of path) | _ -> None)
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
                | Some impl when impl.impl_broken -> Some Accepted
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
                                                (implements database ~bounds ~depth:(depth + 1)
                                                   argument
                                                   (T.substitute_trait substitution bound)))
                                            generic_bounds
                                      | _ -> true)
                                  | Value_generic | Capability_generic -> true)
                                impl.impl_generics
                            in
                            if conditions_hold && associated_match wanted associated then
                              Some (From_impl { impl = impl_path; substitution })
                            else None))
                | None -> None)
              candidates)
    | T.Function _ | T.Projection _ | T.Cursor _ | T.Integer | T.Literal _ -> None

(* The associated type a trait's [impl] for a type chooses, or [None]. *)
let associated_type database ~bounds type_ (trait : T.trait_reference) name =
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
      | Some (From_bound parameter) ->
          List.find_map
            (fun (bound : T.trait_reference) -> List.assoc_opt name bound.associated)
            (List.concat_map (bound_closure database) (bounds parameter))
      | Some From_any -> (
          match type_ with T.Any any -> List.assoc_opt name any.associated | _ -> None)
      | Some (Accepted | Built_in) -> Some T.Error
      | None -> None)

(* Replaces every projection whose base is known by what the [impl]
   chooses. A projection on a generic parameter stays, unless a bound fixes
   it. *)
let rec normalize database ~bounds (type_ : T.ty) : T.ty =
  let normalize = normalize database ~bounds in
  match type_ with
  | T.Projection { base; trait; name } -> (
      let base = normalize base in
      match base with
      | T.Parameter _ -> (
          match associated_type database ~bounds base trait name with
          | Some fixed when fixed <> T.Error -> fixed
          | _ -> T.Projection { base; trait; name })
      | T.Variable _ | T.Hole -> T.Projection { base; trait; name }
      | T.Error -> T.Error
      | _ -> (
          match associated_type database ~bounds base trait name with
          | Some fixed -> normalize fixed
          | None -> T.Error))
  | T.Named { path; arguments } ->
      T.Named { path; arguments = List.map (normalize_argument database ~bounds) arguments }
  | T.Function function_type ->
      T.Function
        {
          function_type with
          inputs = List.map (fun (mode, input) -> (mode, normalize input)) function_type.inputs;
          output =
            (match function_type.output with
            | Returns output -> Returns (normalize output)
            | Yields (mode, output) -> Yields (mode, normalize output)
            | Lends (mode, output) -> Lends (mode, normalize output));
        }
  | T.Any trait ->
      T.Any
        {
          trait with
          associated = List.map (fun (name, type_) -> (name, normalize type_)) trait.associated;
        }
  | _ -> type_

and normalize_argument database ~bounds = function
  | T.Type type_ -> T.Type (normalize database ~bounds type_)
  | value -> value
