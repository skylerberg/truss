(* Checking interfaces. See TYPECHECKER.md, "Checking signatures and
   definitions", "Properties of types", and "Finding an impl". *)

module Summary = Summary
module Lower = Lower
module Constants = Constants
module Environment = Environment
module Properties = Properties
module Impls = Impls
module Check = Check

(* Every interface error of a file, in its offsets and in order. *)
let diagnostics database module_ =
  List.concat_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match Query.demand database Resolve.Names.base key with
      | Some (_, base) ->
          List.map (Diagnostic.move base) (Query.demand database Check.diagnostics key)
      | None -> [])
    (Query.demand database Resolve.Names.declarations module_)
  |> List.sort (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code) (right.span, right.code))
