(* Checking bodies. *)

module Members = Members

type result = Body.result = {
  checked : Checked.t;
  core : Core.t option;
  diagnostics : Diagnostic.t list;
  evidence : string list;
}

let checked = Body.checked

(* The core form of a method a derived [impl] gives, by the method's path. *)
let derived = Derived.core
let diagnostics = Body.diagnostics

(* A definition's core form, when it has one: what the stages after
   checking read. *)
let core =
  Query.query ~name:"core" ~phase:Bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database checked key) (fun (result : result) -> result.core))

(* The core form of a function or a method at a path, for every path that
   code is compiled or proven at, with what stands in it for the parameters
   of another definition. A written one has its own form. A method that a
   derived [impl] gives has the form made from the type's shape. A method
   that an [impl] leaves to its trait has the trait's, in which [Self] and
   the trait's parameters stand for what the [impl] gives them. *)
let core_at =
  Query.query ~name:"core_at" ~phase:Bodies ~show:Path.show (fun database (path : Path.t) ->
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

(* A definition's checked form, when its header and body parsed whole and
   resolution and body checking found no error in it. The later stages,
   patterns, use, and ownership, check only such a definition, so an error
   is reported once, by the stage that finds it, and never again as a
   consequence. *)
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
         (* A method written inside what did not parse has nothing known
            of it. *)
         match Query.demand database Interface.Environment.lowered key with
         | Some { interface = Error_interface _; _ } -> false
         | _ -> true ->
      Some checked
  | _ -> None
