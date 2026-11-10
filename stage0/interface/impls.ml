(* Finding the [impl] of a trait for a type, and normalizing associated
   types.

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
  Query.query ~name:"impl_index" ~phase:Interfaces ~show:Fun.id (fun database package ->
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
  Query.query ~name:"impls_by_type" ~phase:Interfaces ~show:Fun.id (fun database package ->
      List.fold_left
        (fun table ((trait, type_), impl) ->
          Path.Map.update type_
            (fun found -> Some ((trait, impl) :: Option.value ~default:[] found))
            table)
        Path.Map.empty
        (Query.demand database index package)
      |> Path.Map.map List.rev)

(* The impls of a package for a type, each with its trait. *)
let impls_for database (type_ : Path.t) package =
  Option.value ~default:[] (Path.Map.find_opt type_ (Query.demand database by_type package))

let impls_in =
  Query.query ~name:"impls" ~phase:Interfaces ~saved:true
    ~show:(fun (trait, type_, package) ->
      Printf.sprintf "%s for %s in %s" (Path.show trait) (Path.show type_) package)
    (fun database ((trait : Path.t), (type_ : Path.t), package) ->
      List.filter_map
        (fun (indexed_trait, impl) -> if Path.equal indexed_trait trait then Some impl else None)
        (impls_for database type_ package))

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

(* What a trait's [Self] and parameters stand for in an [impl] of it, in
   terms of the [impl]'s own generic parameters. A method the trait gives a
   body is read with this for an [impl] that leaves the method to it, and so
   are the trait's clauses that an [impl]'s method keeps. *)
let trait_substitution database (impl : Path.t) =
  Option.bind (impl_interface database impl) (fun (interface : T.impl_interface) ->
      Option.map
        (fun trait ->
          Properties.trait_substitution trait ~self:interface.for_type interface.implements)
        (Query.demand database Environment.trait_interface interface.implements.trait))

(* Matching *)

let open_type = function T.Error _ | T.Variable _ | T.Hole -> true | _ -> false

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
  | From_bound
      (** A bound in scope, on a generic parameter or on an associated type of one, or a trait such
          a bound requires: the [impl] is found when the code is instantiated. *)
  | From_any  (** [any Trait] implements its trait. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)
  | Accepted of T.ty
      (** Everything is accepted of this type: an [Error], a [Hole], or a type the statement has not
          worked out yet. A trait whose definition did not parse is accepted of every type, as the
          [Error] of its report. *)

let cursor_trait : Path.t =
  Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Cursor" }

(* What a pulled yielding method's cursor gives: what the method yields,
   with the method's type arguments. *)
let cursor_element database (method_ : Path.t) arguments =
  match Query.demand database Environment.signature method_ with
  | Some ({ output = Yields (_, element); _ } as signature) ->
      Option.map
        (fun substitution -> T.substitute substitution element)
        (T.substitution_of signature.generics arguments)
  | _ -> None

let copyable_path = Properties.copyable_trait
let plain_path = Properties.plain_trait

(* The bounds in scope where a question is asked: each generic parameter's
   bounds, as the definition asking declares them. *)
type bounds = T.parameter -> T.trait_reference list

(* What a definition's bounds ask of what stands for its generic
   parameters: each type, with a bound it must meet. *)
let required (generics : T.generic list) (substitution : T.substitution) =
  List.concat_map
    (fun (generic : T.generic) ->
      match (generic.kind, List.assoc_opt generic.generic substitution) with
      | Type_generic generic_bounds, Some (T.Type argument) ->
          List.map (fun bound -> (argument, T.substitute_trait substitution bound)) generic_bounds
      | _ -> [])
    generics

(* The evidence that a type implements a trait. Without [conditions] it is
   the [impl] that answers for the type, whether or not the bounds on its
   parameters hold, which is what an associated type is read from: a bound
   that does not hold is reported where the trait is asked for, and reading
   the type asks nothing more of the type's arguments. *)
let rec implements database ~(bounds : bounds) ?(depth = 0) ?(conditions = true) (type_ : T.ty)
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
  let broken_trait =
    match Query.demand database Environment.interface wanted.trait with
    | Some (Environment.Error_interface report) -> Some report
    | _ -> None
  in
  if depth > 32 then None
  else if Option.is_some broken_trait then
    Option.map (fun report -> Accepted (T.Error report)) broken_trait
  else if Path.equal wanted.trait copyable_path || Path.equal wanted.trait plain_path then
    let property : Properties.property =
      if Path.equal wanted.trait plain_path then Plain else Copyable
    in
    if
      (not conditions)
      || Properties.has database ~bounds ~normalize:(normalize database ~bounds) property type_
    then Some Built_in
    else None
  else
    match type_ with
    | T.Error _ | T.Hole | T.Variable _ -> Some (Accepted type_)
    | T.Cursor _ -> if Path.equal wanted.trait cursor_trait then Some Built_in else None
    | T.Never | T.Integer | T.Literal _ | T.Function _ -> None
    | T.Parameter _ | T.Projection _ ->
        if
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait wanted.trait
              && arguments_match bound.trait_arguments
              && associated_match ~base:(Some type_) bound.associated)
            (Properties.known_bounds database ~bounds type_)
        then Some From_bound
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

(* The associated type a trait's [impl] for a type chooses, or [None]. *)
and associated_type database ~bounds type_ (trait : T.trait_reference) name =
  match List.assoc_opt name trait.associated with
  | Some fixed -> Some fixed
  | None -> (
      match implements database ~bounds ~conditions:false type_ trait with
      | Some (From_impl { impl; substitution }) -> (
          match impl_interface database impl with
          | Some impl ->
              Option.map (T.substitute substitution)
                (List.assoc_opt name impl.implements.associated)
          | None -> None)
      | Some From_bound -> (
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
      | Some Built_in -> (
          match type_ with
          | T.Cursor { method_; arguments } when name = "Element" ->
              cursor_element database method_ arguments
          | _ -> None)
      (* An associated type of an [Error] or a [Hole] is one too; of a type
         not worked out yet, it is not known. *)
      | Some (Accepted (T.Variable _)) -> None
      | Some (Accepted unknown) -> Some unknown
      | None -> None)

(* Replaces every projection whose base is known by what the [impl]
   chooses. A projection on a generic parameter stays, unless a bound fixes
   it, and so does one no [impl] answers, which then equals nothing but
   itself. *)
and normalize database ~bounds (type_ : T.ty) : T.ty =
  T.map
    (function
      | T.Projection { base; trait; name } -> (
          let base = normalize database ~bounds base in
          match base with
          | T.Variable _ | T.Hole -> Some (T.Projection { base; trait; name })
          | T.Error _ -> Some base
          | T.Parameter _ | T.Projection _ -> (
              match associated_type database ~bounds base trait name with
              | Some (T.Projection _ as projection) -> Some projection
              | Some fixed when not (T.is_error fixed) -> Some (normalize database ~bounds fixed)
              | _ -> Some (T.Projection { base; trait; name }))
          | _ -> (
              match associated_type database ~bounds base trait name with
              | Some fixed -> Some (normalize database ~bounds fixed)
              | None -> Some (T.Projection { base; trait; name })))
      | _ -> None)
    type_

(* Whether a type is [Copyable], [Plain], or a view, with each associated
   type that its definition's facts turn on replaced by what its [impl]
   chooses. *)
let has property database ~bounds type_ =
  Properties.has database ~bounds ~normalize:(normalize database ~bounds) property type_

let copyable = has Copyable
let plain = has Plain
let is_view = has View

(* The named types a value of a type holds in place. *)
let held_in_place database ~bounds type_ =
  Properties.held database ~normalize:(normalize database ~bounds) type_
