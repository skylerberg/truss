(* The diagnostics of the packages a command is about, shown for people on
   standard error or as JSON. A manifest that cannot be read, or a package
   name used twice, is a problem in the code too, which the session finds
   before any file is checked. *)

type file = { module_ : Path.module_; source : Source.t; diagnostics : Diagnostic.t list }
type t = { files : file list; problems : string list }

(* Every file's diagnostics, in the packages' order, leaving out files with
   none. Each file lists at most [Diagnostic.limit]. *)
let gather (project : Project.t) =
  {
    files =
      List.filter_map
        (fun module_ ->
          match Diagnostic.shown (Database.diagnostics project.session module_) with
          | [] -> None
          | diagnostics -> Some { module_; source = Project.source project module_; diagnostics })
        (Project.modules project);
    problems = Database.problems project.session;
  }

let clean report = report.files = [] && report.problems = []

let count report =
  List.length report.problems
  + List.fold_left (fun total file -> total + List.length file.diagnostics) 0 report.files

let to_json report =
  List.concat_map
    (fun file ->
      List.map
        (fun diagnostic -> Json.Raw (Diagnostic.to_json_object file.source diagnostic))
        file.diagnostics)
    report.files

(* A command's JSON document, with the report's diagnostics and problems. *)
let document report fields =
  Json.document ~diagnostics:(to_json report)
    (("problems", Json.List (List.map (fun p -> Json.String p) report.problems)) :: fields)

let plural count one many = Printf.sprintf "%d %s" count (if count = 1 then one else many)

(* Each problem, each diagnostic as [Diagnostic.render] shows it, and a
   count, on standard error. *)
let print report =
  List.iter Output.eprint_line report.problems;
  List.iter
    (fun file ->
      List.iter
        (fun diagnostic -> Output.eprint (Diagnostic.render file.source diagnostic))
        file.diagnostics)
    report.files;
  match count report with 0 -> () | n -> Output.eprintf "%s\n" (plural n "error" "errors")
