module Members = Members

type result = Body.result = {
  checked : Checked.t;
  core : Core.t option;
  diagnostics : Diagnostic.t list;
  evidence : Path.package list;
}

let checked = Body.checked
let derived = Derived.core
let diagnostics = Body.diagnostics

let core =
  Query.query ~name:"core" ~phase:Phases.bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database checked key) (fun (result : result) -> result.core))

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
  Query.query ~name:"core_of_path" ~phase:Phases.bodies ~show:Path.show (of_path ~written:core)

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

let specification =
  Query.query ~name:"specification" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:true key.path then form else without_body form)
        (Query.demand database core key))

let exported_specification =
  Query.query ~name:"exported_specification" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:false key.path then form
          else without_body form)
        (Query.demand database core key))

let specification_of_path =
  Query.query ~name:"specification_of_path" ~phase:Phases.bodies ~show:Path.show
    (of_path ~written:specification)

let exported_specification_of_path =
  Query.query ~name:"exported_specification_of_path" ~phase:Phases.bodies ~show:Path.show
    (of_path ~written:exported_specification)

let evidence =
  Query.query ~name:"evidence" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      match Query.demand database checked key with
      | Some (result : result) -> result.evidence
      | None -> [])

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

let is_clean database key = Option.is_some (clean database key)
