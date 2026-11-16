type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }

type t = {
  checked : file list;
  proofs : Proofs.t Lazy.t option;
  proven : file list Lazy.t;
  problems : Project.problem list;
}

let shown snapshot packages file diagnostics =
  match Diagnostic.shown diagnostics with
  | [] -> None
  | diagnostics ->
      Some { file; source = Command_packages.source snapshot packages file; diagnostics }

let gather ?(proofs = false) pipeline snapshot packages =
  let program_packages = Command_packages.program_packages snapshot packages in
  let files = Command_packages.files snapshot program_packages in
  Pipeline.check pipeline program_packages;
  let proofs =
    if proofs then Some (lazy (Proofs.check pipeline snapshot packages files)) else None
  in
  {
    checked =
      List.filter_map
        (fun file -> shown snapshot packages file (Pipeline.file_diagnostics pipeline file))
        files;
    proofs;
    proven =
      lazy
        (match proofs with
        | Some proofs ->
            let proofs = Lazy.force proofs in
            List.filter_map
              (fun file -> shown snapshot packages file (Proofs.diagnostics proofs file))
              files
        | None -> []);
    problems =
      Workspace.problems snapshot
      @ List.map
          (fun (file, package, problem) ->
            {
              Project.file;
              line = None;
              message = Package_checks.manifest_sentence ~package problem;
            })
          (Command_packages.manifest_problems snapshot pipeline packages);
  }

let of_files files = { checked = files; proofs = None; proven = Lazy.from_val []; problems = [] }
let proofs report = Option.map Lazy.force report.proofs
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

let document report fields =
  Json.document ~diagnostics:(to_json report)
    (( "problems",
       Json.List
         (List.map (fun problem -> Json.String (Project.show_problem problem)) report.problems) )
    :: fields)

let plural count one many = Printf.sprintf "%d %s" count (if count = 1 then one else many)

let print report =
  let print_files =
    List.iter (fun file ->
        List.iter
          (fun diagnostic -> Output.eprint (Diagnostic.render file.source diagnostic))
          file.diagnostics)
  in
  List.iter (fun problem -> Output.eprint_line (Project.show_problem problem)) report.problems;
  print_files report.checked;
  print_files (Lazy.force report.proven);
  match count report with
  | 0 -> ()
  | error_count -> Output.eprintf "%s\n" (plural error_count "error" "errors")

exception Errors of t
