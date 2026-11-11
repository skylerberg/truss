(* The type checker's queries. *)

module Members = Members

type result = Body.result = {
  checked : Checked.t;
  core : Core.t option;
  diagnostics : Diagnostic.t list;
  evidence : string list;
}

let checked = Body.checked

(* The core form of a method of a derived [impl], by the method's path. *)
let derived = Derived.core
let diagnostics = Body.diagnostics

(* The core form of a definition. [None] if the definition has an error. *)
let core =
  Query.query ~name:"core" ~phase:Bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database checked key) (fun (result : result) -> result.core))

(* The core form of the function or method at a path, with a substitution
   to apply to it.

   - A function or method with a written body: its own core form, and the
     empty substitution.
   - A method of a derived [impl]: the generated core form, and the empty
     substitution.
   - A method that an [impl] inherits from its trait: the core form of the
     trait's default method, and the substitution that maps [Self] and the
     trait's generic parameters to the [impl]'s types. *)
let of_path ~written database (path : Path.t) =
  let written path =
    Option.bind (Query.demand database Interface.Summary.key path) (Query.demand database written)
  in
  match (written path, path) with
  | Some form, _ -> Some (form, [])
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
      match Query.demand database derived path with
      | Some form -> Some (form, [])
      | None ->
          Option.bind (Interface.Impls.impl_interface database owner)
            (fun (impl : Types.impl_interface) ->
              Option.bind (Interface.Impls.trait_substitution database owner) (fun substitution ->
                  Option.map
                    (fun form -> (form, substitution))
                    (written (Method { owner = impl.implements.trait; name; receiver })))))
  | None, _ -> None

let core_of_path =
  Query.query ~name:"core_of_path" ~phase:Bodies ~show:Path.show (of_path ~written:core)

(* Whether a caller's proof can read the body of a function. In the
   function's own package, it reads the body of a function in the logic,
   which the body defines. In another package, it reads that body only if
   the function is [transparent]: a body that other packages' proofs read
   is part of the package's interface, and only a marked one is. In every
   package, it reads the body that a trait provides for a method, which an
   [impl] inherits or must agree with. It never reads the body of a
   theorem: a call of a theorem asserts the [requires] and assumes the
   [ensures]. *)
let callers_read_body database ~same_package (path : Path.t) =
  let provided =
    match path with
    | Method { owner; _ } ->
        Option.is_some (Query.demand database Interface.Environment.trait_interface owner)
    | _ -> false
  in
  provided
  || Interface.Summary.kind_of database path <> Some Theorem
     &&
     match Interface.Impls.signature database path with
     | Some signature ->
         Types.body_is_definition signature && (same_package || signature.transparent)
     | None -> true

(* A form without the body of its function, with the counts of the nodes
   that are left. *)
let without_body (form : Core.t) : Core.t =
  match form.definition with
  | Function { parameters; contract; body = Some _ } ->
      let definition : Core.definition = Function { parameters; contract; body = None } in
      let nodes = ref 0 and synthetic_locals = ref 0 in
      let node id = nodes := max !nodes (id + 1) in
      Core_walk.definition
        {
          Core_walk.ignore_all with
          expression = (fun node_ -> node node_.id);
          statement = (fun node_ -> node node_.id);
          pattern =
            (fun node_ ->
              node node_.id;
              match node_.kind with
              | Bind { local = Synthetic number; _ } ->
                  synthetic_locals := max !synthetic_locals (number + 1)
              | _ -> ());
        }
        definition;
      { definition; node_count = !nodes; synthetic_local_count = !synthetic_locals }
  | _ -> form

(* What a caller's proof reads of a definition: its core form, without the
   body of a function whose body no caller's proof reads. The parameters
   and the contract are built before the body, so their nodes are numbered
   the same whatever the body is. Editing such a body leaves this result
   equal, and no caller is proven again. *)
let specification =
  Query.query ~name:"specification" ~phase:Bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:true key.path then form else without_body form)
        (Query.demand database core key))

(* What a caller's proof in another package reads of a definition. Editing
   the body of a function that is not [transparent] leaves this result
   equal, so no proof in a package that depends on this one runs again. *)
let exported_specification =
  Query.query ~name:"exported_specification" ~phase:Bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:false key.path then form
          else without_body form)
        (Query.demand database core key))

(* As [core_of_path], for what a caller's proof reads of the function or
   method at a path. *)
let specification_of_path =
  Query.query ~name:"specification_of_path" ~phase:Bodies ~show:Path.show
    (of_path ~written:specification)

let exported_specification_of_path =
  Query.query ~name:"exported_specification_of_path" ~phase:Bodies ~show:Path.show
    (of_path ~written:exported_specification)

(* The packages whose [impl]s met a bound in a definition. *)
let evidence =
  Query.query ~name:"evidence" ~phase:Bodies ~show:Resolve.Names.show_key (fun database key ->
      match Query.demand database checked key with
      | Some (result : result) -> result.evidence
      | None -> [])

(* The checked tables of a definition, or [None] if the definition has a
   parse error, a resolution error, or a type error. The pattern, use, and
   ownership checks run only on a definition that has none, so that one
   mistake is not reported again by a later check. *)
let clean database key =
  match
    ( Query.demand database Resolve.Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database checked key )
  with
  | Some definition, Some resolved, Some { checked; diagnostics = []; _ }
    when resolved.diagnostics = []
         && (not (Resolve.Parts.broken definition Header || Resolve.Parts.broken definition Body))
         &&
         (* A method inside a type, trait, or impl that did not parse. *)
         match Query.demand database Interface.Environment.lowered key with
         | Some { interface = Error_interface _; _ } -> false
         | _ -> true ->
      Some checked
  | _ -> None

(* Whether a definition has no parse error, resolution error, or type
   error. *)
let is_clean database key = Option.is_some (clean database key)
