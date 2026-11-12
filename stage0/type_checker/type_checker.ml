(* The type checker's entry point: every stage, in order, over the
   definitions of a build. The stages are linked together; each reads the
   earlier ones' results through their queries. *)

(* Every diagnostic of a file, from the lexer to the package checks, in the
   file's offsets and in order. *)
let diagnostics database module_ =
  let file = Query.demand database Workspace.file module_ in
  List.sort_uniq
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    (file.diagnostics
    @ Resolve.diagnostics database module_
    @ Interface.diagnostics database module_
    @ Infer.diagnostics database module_
    @ Patterns.diagnostics database module_
    @ Usage.diagnostics database module_
    @ Ownership.diagnostics database module_
    @ Package_checks.diagnostics database module_)

(* The same, as a query, which the database keeps current for each file of
   a worktree and saves, so that a check after a restart finds it done. *)
type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : string; name : string }
  | Unused of string

let manifest_problems = Package_checks.manifest_problems
let manifest_sentence = Package_checks.manifest_sentence
let code_packages = Package_checks.code_packages

let file_diagnostics =
  Query.query ~name:"all_diagnostics" ~phase:Phases.diagnostics ~show:Path.show_module ~saved:true
    diagnostics

module For_testing = struct
  module Patterns = Patterns
  module Usage = Usage
  module Package_checks = Package_checks
end
