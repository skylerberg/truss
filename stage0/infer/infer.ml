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
let core_of_path =
  Query.query ~name:"core_of_path" ~phase:Bodies ~show:Path.show (fun database (path : Path.t) ->
      let written path =
        Option.bind (Query.demand database Interface.Summary.key path) (Query.demand database core)
      in
      match (written path, path) with
      | Some form, _ -> Some (form, [])
      | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
          match Query.demand database derived path with
          | Some form -> Some (form, [])
          | None ->
              Option.bind (Interface.Impls.impl_interface database owner)
                (fun (impl : Types.impl_interface) ->
                  Option.bind (Interface.Impls.trait_substitution database owner)
                    (fun substitution ->
                      Option.map
                        (fun form -> (form, substitution))
                        (written (Method { owner = impl.implements.trait; name; receiver })))))
      | None, _ -> None)

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
