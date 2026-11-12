(* The type checker's entry point: every stage, in order, over the
   definitions of a build. The stages are linked together; each reads the
   earlier ones' results through their queries. *)

type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

let stages =
  [
    (Resolve, Resolve.diagnostics);
    (Interface, Interface.diagnostics);
    (Infer, Infer.diagnostics);
    (Patterns, Patterns.diagnostics);
    (Usage, Usage.diagnostics);
    (Ownership, Ownership.diagnostics);
    (Package_checks, Package_checks.diagnostics);
  ]

let through last database module_ =
  let rec stage_diagnostics = function
    | [] -> []
    | (stage, diagnostics) :: rest ->
        diagnostics database module_ @ if stage = last then [] else stage_diagnostics rest
  in
  stage_diagnostics stages

(* Every diagnostic of a file, from the lexer to the package checks, in the
   file's offsets and in order. *)
let diagnostics database module_ =
  let file = Query.demand database Workspace.file module_ in
  List.sort_uniq
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    (file.diagnostics @ through Package_checks database module_)

(* The same, as a query, which the database keeps current for each file of
   a worktree and saves, so that a check after a restart finds it done. *)
type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

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
