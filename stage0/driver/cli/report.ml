(* The diagnostics of the program built from a command's packages,
   printed on standard error or as JSON. A manifest problem is
   reported with them: both the problems the session finds while it reads
   the manifests and the ones that only a package's code reveals. *)

type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }

(* The prover's diagnostics are computed only when first read, so a command
   prints every other diagnostic before it waits for the solver. *)
type t = { checked : file list; proven : file list Lazy.t; problems : string list }

let shown session packages file diagnostics =
  match Diagnostic.shown diagnostics with
  | [] -> None
  | diagnostics ->
      Some { file; source = Command_packages.source session packages file; diagnostics }

let gather ?(proofs = false) session packages =
  let files = Command_packages.program_files session packages in
  {
    checked =
      List.filter_map
        (fun file -> shown session packages file (Database.diagnostics session file))
        files;
    proven =
      (if proofs then
         lazy
           (let proven = Proofs.diagnostics session packages files in
            List.filter_map (fun file -> shown session packages file (proven file)) files)
       else Lazy.from_val []);
    problems =
      Database.problems session
      @ List.map
          (fun (file, package, problem) ->
            Printf.sprintf "%s: %s" file (Checks.manifest_sentence ~package problem))
          (Database.manifest_problems session packages);
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
