type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }

type t = {
  checked : file list;
  proofs : Proofs.t Lazy.t option;
  proven : file list Lazy.t;
  problems : Project.problem list;
}

let make_shown_file snapshot database file diagnostics =
  match Diagnostic.select_shown diagnostics with
  | [] -> None
  | diagnostics ->
      Some { file; source = Command_packages.read_source snapshot database file; diagnostics }

let gather ~proofs database snapshot packages =
  let program_packages = Command_packages.list_program_packages snapshot packages in
  let files = Command_packages.list_files snapshot program_packages in
  let proofs =
    if proofs then
      Some (lazy (Proofs.check database snapshot packages (In_packages program_packages)))
    else None
  in
  {
    checked =
      List.filter_map
        (fun file ->
          make_shown_file snapshot database file (Database.list_file_diagnostics database file))
        files;
    proofs;
    proven =
      lazy
        (match proofs with
        | Some proofs ->
            let proofs = Lazy.force proofs in
            List.filter_map
              (fun file ->
                make_shown_file snapshot database file (Proofs.list_diagnostics proofs file))
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
                | Not_a_capability { dependency; capability } ->
                    Interface.Grants.describe_not_a_capability ~dependency capability
                | Unused_dependency dependency ->
                    Package_checks.describe_unused_dependency ~package dependency);
            })
          (Command_packages.list_manifest_problems snapshot database packages);
  }

let of_files files = { checked = files; proofs = None; proven = Lazy.from_val []; problems = [] }
let force_proofs report = Option.map Lazy.force report.proofs
let list_files report = report.checked @ Lazy.force report.proven
let list_diagnostics report = List.concat_map (fun file -> file.diagnostics) (list_files report)

let count_errors report =
  List.length report.problems
  + List.length (List.filter Diagnostic.is_error (list_diagnostics report))

let count_warnings report =
  List.length
    (List.filter (fun diagnostic -> not (Diagnostic.is_error diagnostic)) (list_diagnostics report))

let has_errors report = count_errors report > 0

let count_fixable report =
  let count diagnostics = List.length (Diagnostic.list_machine_applicable diagnostics) in
  let count_warnings_of file =
    count (List.filter (fun diagnostic -> not (Diagnostic.is_error diagnostic)) file.diagnostics)
  in
  List.fold_left (fun total file -> total + count file.diagnostics) 0 report.checked
  + List.fold_left (fun total file -> total + count_warnings_of file) 0 (Lazy.force report.proven)

let describe_fixable report =
  match count_fixable report with
  | 0 -> ""
  | fixable when fixable = count_errors report + count_warnings report ->
      if fixable = 1 then ". `truss check --fix` fixes it."
      else ". `truss check --fix` fixes all of them."
  | fixable -> Printf.sprintf ". `truss check --fix` fixes %d of them." fixable

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

let print ?(offers_fix = true) report =
  let is_colored = Output.is_colored () in
  let print_files =
    List.iter (fun file ->
        List.iter
          (fun diagnostic -> Output.eprint (Diagnostic.render ~is_colored file.source diagnostic))
          file.diagnostics)
  in
  List.iter (fun problem -> Output.eprint (Project.show_problem problem ^ "\n\n")) report.problems;
  print_files report.checked;
  print_files (Lazy.force report.proven);
  let errors =
    Diagnostic.paint_severity ~is_colored Error
      (Diagnostic.show_count (count_errors report) "error" "errors")
  and warnings =
    Diagnostic.paint_severity ~is_colored Warning
      (Diagnostic.show_count (count_warnings report) "warning" "warnings")
  and fixable = if offers_fix then describe_fixable report else "" in
  match (count_errors report, count_warnings report) with
  | 0, 0 -> ()
  | _, 0 -> Output.eprintf "%s%s\n" errors fixable
  | 0, _ -> Output.eprintf "%s%s\n" warnings fixable
  | _ -> Output.eprintf "%s and %s%s\n" errors warnings fixable

exception Errors of t

let require_no_errors report =
  if has_errors report then raise (Errors report) else if not (Output.json ()) then print report
