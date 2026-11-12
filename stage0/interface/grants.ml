module T = Types
module Names = Resolve.Names

(* The capability a grant's entry names: a prelude capability by its name,
   and any other by its full path, which must be one the package granting
   it can see. *)
let capability database ~package written : Path.t option =
  let found (module_ : Path.module_) name =
    match Query.demand database Names.find (module_, name) with
    | Some { kind = Capability; visibility; _ }
      when module_.package = package || Names.is_public visibility ->
        Some (Path.Top { module_; name })
    | _ -> None
  in
  match Option.map List.rev (Path.parse_names written) with
  | Some [ name ] ->
      Option.bind (Resolve.Prelude.find_type name) (fun module_ -> found module_ name)
  | Some (name :: modules) -> (
      match Workspace.split_module database (List.rev modules) with
      | Some module_ -> found module_ name
      | None -> None)
  | Some [] | None -> None

(* A capability as a grant writes it. *)
let written (path : Path.t) =
  match path with
  | Top { module_; name } when Resolve.Prelude.find_type name = Some module_ -> name
  | _ -> Path.show path

type grant = {
  capabilities : Path.t list;
  unknown : string list;  (** The entries that name no capability *)
}

let granted =
  Query.query ~name:"granted" ~phase:Phases.interfaces ~saved:true
    ~show:(fun (package, dependency) ->
      Printf.sprintf "%s to %s" (Path.show_package package) (Path.show_package dependency))
    (fun database (package, dependency) ->
      Option.map
        (fun (entry : Workspace.dependency) ->
          let found =
            List.map (fun name -> (name, capability database ~package name)) entry.capabilities
          in
          {
            capabilities = List.filter_map snd found;
            unknown =
              List.filter_map (fun (name, path) -> if path = None then Some name else None) found;
          })
        (List.find_opt
           (fun (entry : Workspace.dependency) -> entry.package = dependency)
           (Query.demand database Workspace.dependencies package)))

let missing database ~package ~of_ (uses : T.capability list) =
  if of_ = package || of_ = Path.standard_package then []
  else
    let granted =
      match Query.demand database granted (package, of_) with
      | Some grant -> grant.capabilities
      | None -> []
    in
    List.filter_map
      (function
        | T.Capability path when not (List.exists (Path.equal path) granted) -> Some path
        | _ -> None)
      (List.sort_uniq compare uses)

let message ~what ~of_ capability =
  let of_ = Path.show_package of_ in
  Printf.sprintf
    "%s uses `%s`, which the manifest does not grant `%s`. To grant it, add \"%s\" to the entry \
     for `%s` in `truss.toml`."
    what (written capability) of_ (written capability) of_

let rec evidence_uses database ~bounds ?(depth = 0) (evidence : Impls.evidence) =
  match evidence with
  | From_impl { impl; substitution } when depth < 16 -> (
      match Impls.impl_interface database impl with
      | None -> []
      | Some interface ->
          ( impl,
            interface,
            List.sort_uniq compare
              (interface.impl_uses
              @ List.concat_map
                  (fun (_, _, (signature : T.signature)) -> signature.uses)
                  interface.impl_methods) )
          :: List.concat_map
               (fun (argument, bound) ->
                 match Impls.implements database ~bounds argument bound with
                 | Some nested -> evidence_uses database ~bounds ~depth:(depth + 1) nested
                 | None -> [])
               (Impls.required interface.impl_generics substitution))
  | _ -> []

let messages database ~package impls =
  List.concat_map
    (fun (impl, (interface : T.impl_interface), uses) ->
      let of_ = Path.package impl in
      List.map
        (message
           ~what:
             (Printf.sprintf "The `impl` of `%s` for `%s`"
                (T.show_trait interface.implements)
                (T.show interface.for_type))
           ~of_)
        (missing database ~package ~of_ uses))
    impls

let evidence_messages database ~package ~bounds evidence =
  messages database ~package (evidence_uses database ~bounds evidence)
