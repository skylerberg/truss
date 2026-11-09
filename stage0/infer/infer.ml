(* Checking bodies. See TYPECHECKER.md, "Checking bodies" and "Patterns". *)

module Unify = Unify
module Members = Members
module Expressions = Expressions
module Capabilities = Capabilities
module Body = Body

type result = Body.result = { checked : Checked.t; diagnostics : Diagnostic.t list }

let checked = Body.checked
let diagnostics = Body.diagnostics
