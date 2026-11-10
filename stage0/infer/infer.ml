(* Checking bodies. *)

module Members = Members

type result = Body.result = {
  checked : Checked.t;
  core : Core.t option;
  diagnostics : Diagnostic.t list;
  evidence : string list;
}

let checked = Body.checked
let diagnostics = Body.diagnostics

(* A definition's core form, when it has one: what the stages after
   checking read. *)
let core =
  Query.query ~name:"core" ~phase:Bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database checked key) (fun (result : result) -> result.core))

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
