(* Checking bodies. See TYPECHECKER.md, "Checking bodies" and "Patterns". *)

module Members = Members

type result = Body.result = { checked : Checked.t; diagnostics : Diagnostic.t list }

let checked = Body.checked
let diagnostics = Body.diagnostics

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
  | Some definition, Some resolved, Some { checked; diagnostics = [] }
    when resolved.diagnostics = []
         && not (Resolve.Parts.broken definition Header || Resolve.Parts.broken definition Body) ->
      Some checked
  | _ -> None
