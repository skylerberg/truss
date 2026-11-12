(* The diagnostics of the packages a command is about, shown for people on
   standard error or as JSON. An error in a manifest is a problem in the code
   too: the errors reading the manifests shows, which the session finds
   before any file is checked, and the errors only a package's code shows
   in its own. *)

type file = { module_ : Path.module_; source : Source.t; diagnostics : Diagnostic.t list }

(* The prover's diagnostics are solved only when first read, so a command
   prints every other diagnostic before it waits for the solver. *)
type t = { checked : file list; proven : file list Lazy.t; problems : string list }

let shown (project : Project.t) module_ diagnostics =
  match Diagnostic.shown diagnostics with
  | [] -> None
  | diagnostics -> Some { module_; source = Project.source project module_; diagnostics }

(* Every file's diagnostics, in the packages' order, leaving out files with
   none, and with [proofs], the prover's too. Each file lists at most
   [Diagnostic.limit]. *)
let gather ?(proofs = false) (project : Project.t) =
  (* A dependency's proofs are the program's too: a build leaves out the
     run-time checks its proofs stand for. *)
  let checked =
    List.map
      (fun module_ -> (module_, Database.diagnostics project.session module_))
      (if proofs then Project.program_modules project else Project.modules project)
  in
  (* A file is proven only once it has no other diagnostic, since the
     prover reads the type checker's output. *)
  let provable =
    List.filter_map
      (fun (module_, diagnostics) -> if diagnostics = [] then Some module_ else None)
      checked
  in
  {
    checked =
      List.filter_map (fun (module_, diagnostics) -> shown project module_ diagnostics) checked;
    proven =
      (if proofs && provable <> [] then
         lazy
           (let proven = Proofs.diagnostics project provable in
            List.filter_map (fun module_ -> shown project module_ (proven module_)) provable)
       else Lazy.from_val []);
    problems =
      Database.problems project.session
      @ List.map
          (fun (file, package, problem) ->
            Printf.sprintf "%s: %s" file (Type_checker.manifest_sentence ~package problem))
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

(* Each problem, each diagnostic as [Diagnostic.render] shows it, and a
   count, on standard error. The prover's diagnostics come last, so the
   others show while the solver runs. *)
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
