type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }

type t = {
  checked : file list;
  proofs : Proofs.t Lazy.t option;
  proven : file list Lazy.t;
  problems : Project.problem list;
}

let make_shown_file snapshot database packages file diagnostics =
  match Diagnostic.select_shown diagnostics with
  | [] -> None
  | diagnostics ->
      Some
        { file; source = Command_packages.read_source snapshot database packages file; diagnostics }

let gather ?(proofs = false) database snapshot packages =
  let program_packages = Command_packages.list_program_packages snapshot packages in
  let files = Command_packages.list_files snapshot program_packages in
  let proofs =
    if proofs then Some (lazy (Proofs.check database snapshot packages files)) else None
  in
  {
    checked =
      List.filter_map
        (fun file ->
          make_shown_file snapshot database packages file
            (Database.list_file_diagnostics database file))
        files;
    proofs;
    proven =
      lazy
        (match proofs with
        | Some proofs ->
            let proofs = Lazy.force proofs in
            List.filter_map
              (fun file ->
                make_shown_file snapshot database packages file
                  (Proofs.list_diagnostics proofs file))
              files
        | None -> []);
    problems =
      Workspace.problems snapshot
      @ Workspace.list_dependency_problems snapshot database
      @ List.map
          (fun (file, package, (problem : Database.manifest_problem)) ->
            {
              Project.file;
              line = None;
              message =
                (match problem with
                | Not_a_capability { dependency; name } ->
                    Interface.Grants.describe_not_a_capability ~dependency name
                | Unused_dependency dependency ->
                    Package_checks.describe_unused_dependency ~package dependency);
            })
          (Command_packages.list_manifest_problems snapshot database packages);
  }

let of_files files = { checked = files; proofs = None; proven = Lazy.from_val []; problems = [] }
let force_proofs report = Option.map Lazy.force report.proofs
let list_files report = report.checked @ Lazy.force report.proven
let clean report = report.problems = [] && list_files report = []

let count report =
  List.length report.problems
  + List.fold_left (fun total file -> total + List.length file.diagnostics) 0 (list_files report)

let to_json report =
  List.concat_map
    (fun file ->
      List.map
        (fun diagnostic -> Json.Raw (Diagnostic.to_json_object file.source diagnostic))
        file.diagnostics)
    (list_files report)

let make_document report fields =
  Json.make_document ~diagnostics:(to_json report)
    (( "problems",
       Json.List
         (List.map (fun problem -> Json.String (Project.show_problem problem)) report.problems) )
    :: fields)

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
  | error_count -> Output.eprintf "%s\n" (Diagnostic.show_count error_count "error" "errors")

exception Errors of t
