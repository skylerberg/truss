(* A package's diagnostics, shown for people on standard error or as JSON.
   See CLI.md, "Output streams and exit status". *)

type file = { module_ : Path.module_; source : Source.t; diagnostics : Diagnostic.t list }

(* Every file's diagnostics, in the package's order, leaving out files with
   none. Each file lists at most [Diagnostic.limit]. *)
let gather (project : Project.t) =
  List.filter_map
    (fun module_ ->
      match Diagnostic.shown (Type_checker.diagnostics project.database module_) with
      | [] -> None
      | diagnostics -> Some { module_; source = Project.source project module_; diagnostics })
    (Project.modules project)

let count files = List.fold_left (fun total file -> total + List.length file.diagnostics) 0 files

let to_json files =
  List.concat_map
    (fun file ->
      List.map
        (fun diagnostic -> Json.Raw (Diagnostic.to_json_object file.source diagnostic))
        file.diagnostics)
    files

let plural count one many = Printf.sprintf "%d %s" count (if count = 1 then one else many)

(* Each diagnostic as [Diagnostic.render] shows it, and a count, on standard
   error. *)
let print files =
  List.iter
    (fun file ->
      List.iter
        (fun diagnostic -> prerr_string (Diagnostic.render file.source diagnostic))
        file.diagnostics)
    files;
  match count files with 0 -> () | n -> Printf.eprintf "%s\n%!" (plural n "error" "errors")
