(* The diagnostics of the program built from a command's packages,
   printed on standard error or as JSON. A manifest problem is
   reported with them: both the problems the session finds while it reads
   the manifests and the ones that only a package's code reveals. *)

type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }

(* The prover's diagnostics are computed only when first read, so a command
   prints every other diagnostic before it waits for the solver. *)
type t = { checked : file list; proven : file list Lazy.t; problems : string list }

let shown (project : Project.t) file diagnostics =
  match Diagnostic.shown diagnostics with
  | [] -> None
  | diagnostics -> Some { file; source = Project.source project file; diagnostics }

(* The diagnostics of every file of [Project.program_files], in package
   order, and with [proofs], the prover's too. Such a dependency is checked
   because the program is built from it: code generation cannot lower a
   body that does not type-check, and a release build omits the run-time
   checks that the dependency's proofs replace. Files without a diagnostic
   are left out, and each file lists at most [Diagnostic.limit]. *)
let gather ?(proofs = false) (project : Project.t) =
  let files = Project.program_files project in
  {
    checked =
      List.filter_map
        (fun file -> shown project file (Database.diagnostics project.session file))
        files;
    proven =
      (if proofs then
         lazy
           (let proven = Proofs.diagnostics project files in
            List.filter_map (fun file -> shown project file (proven file)) files)
       else Lazy.from_val []);
    problems =
      Database.problems project.session
      @ List.map
          (fun (file, package, problem) ->
            Printf.sprintf "%s: %s" file (Checks.manifest_sentence ~package problem))
          (Project.manifest_problems project);
  }

let of_files files = { checked = files; proven = Lazy.from_val []; problems = [] }
let files report = report.checked @ Lazy.force report.proven
let clean report = report.problems = [] && files report = []

let count report =
  List.length report.problems
  + List.fold_left (fun total file -> total + List.length file.diagnostics) 0 (files report)

let to_json report =
  List.concat_map
    (fun file ->
      List.map
        (fun diagnostic -> Json.Raw (Diagnostic.to_json_object file.source diagnostic))
        file.diagnostics)
    (files report)

(* A command's JSON document, with the report's diagnostics and problems. *)
let document report fields =
  Json.document ~diagnostics:(to_json report)
    (("problems", Json.List (List.map (fun problem -> Json.String problem) report.problems))
    :: fields)

let plural count one many = Printf.sprintf "%d %s" count (if count = 1 then one else many)

(* Prints each problem, each diagnostic as [Diagnostic.render] renders it,
   and a count, on standard error. The prover's diagnostics come last, so
   the others appear while the solver runs. *)
let print report =
  let print_files =
    List.iter (fun file ->
        List.iter
          (fun diagnostic -> Output.eprint (Diagnostic.render file.source diagnostic))
          file.diagnostics)
  in
  List.iter Output.eprint_line report.problems;
  print_files report.checked;
  print_files (Lazy.force report.proven);
  match count report with
  | 0 -> ()
  | error_count -> Output.eprintf "%s\n" (plural error_count "error" "errors")

(* The code has errors, so the command stops, and the command line writes
   the report and exits with 1. *)
exception Errors of t
