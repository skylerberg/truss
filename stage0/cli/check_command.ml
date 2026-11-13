(* [truss check]: every diagnostic of the packages, and with [--fix], each
   diagnostic's only fix applied. *)

(* The diagnostics to fix in one round in one file: each diagnostic with
   exactly one fix, except a fix whose edits overlap an earlier fix's, since
   applying both could produce neither intended result. A skipped fix is
   reconsidered in the next round, after the file is checked again. *)
let chosen (diagnostics : Diagnostic.t list) =
  let overlaps (left : Diagnostic.span Diagnostic.edit) (right : Diagnostic.span Diagnostic.edit) =
    (left.span.start < right.span.stop && right.span.start < left.span.stop)
    || left.span.start = right.span.start
       && (left.span.start = left.span.stop || right.span.start = right.span.stop)
  in
  let accepted_edits = ref [] in
  List.filter
    (fun (diagnostic : Diagnostic.t) ->
      match diagnostic.fixes with
      | [ fix ] ->
          let clear =
            List.for_all
              (fun (edit : Diagnostic.span Diagnostic.edit) ->
                not (List.exists (overlaps edit) !accepted_edits))
              fix.edits
          in
          if clear then accepted_edits := fix.edits @ !accepted_edits;
          clear
      | _ -> false)
    diagnostics

(* Applies non-overlapping edits to a text from last to first, so each
   edit's offsets stay valid. *)
let apply text (edits : Diagnostic.span Diagnostic.edit list) =
  List.sort
    (fun (left : Diagnostic.span Diagnostic.edit) right -> compare right.span.start left.span.start)
    edits
  |> List.fold_left
       (fun text (edit : Diagnostic.span Diagnostic.edit) ->
         String.sub text 0 edit.span.start ^ edit.replacement
         ^ String.sub text edit.span.stop (String.length text - edit.span.stop))
       text

(* Bounds the rounds, so two fixes that undo each other cannot loop
   forever. *)
let rounds = 32

(* Deletes the manifest entry of each unused dependency, which is that
   problem's only fix, and returns each deletion as JSON. A grant is never
   added: granting a capability is a decision that a reviewer must see a
   person make. *)
let unused_dependencies (project : Project.t) =
  let root = Database.root project.session in
  List.filter_map
    (fun (file, package, (problem : Checks.manifest_problem)) ->
      match problem with
      | Unused dependency ->
          let path = Filename.concat root file in
          let text = In_channel.with_open_bin path In_channel.input_all in
          Project.write_file path (Manifest.without_dependency text dependency);
          Some
            (Json.to_string
               (Json.Object
                  [
                    ("file", Json.String (Project.shown path));
                    ("message", Json.String (Checks.manifest_sentence ~package problem));
                  ]))
      | Not_a_capability _ -> None)
    (Project.manifest_problems project)

(* Writes the canonical lock file when the lock file on disk differs, which
   is that problem's only fix. It never chooses a version: a dependency
   without a version in the lock file or any record needs `truss add`. *)
let lock_file (project : Project.t) =
  match Database.lock_fix project.session with
  | None -> []
  | Some text ->
      let path = Filename.concat (Database.root project.session) "truss.lock" in
      Project.write_file path text;
      [
        Json.to_string
          (Json.Object
             [
               ("file", Json.String (Project.shown path));
               ("message", Json.String "This is not the lock file the manifests give.");
             ]);
      ]

(* Applies fixes until none remains, and returns the fixed diagnostics as
   JSON, each against the file text at the time of its fix. *)
let fix (project : Project.t) =
  let rec round number fixed =
    let applied =
      List.concat_map
        (fun file ->
          let diagnostics = Database.diagnostics project.session file in
          match chosen diagnostics with
          | [] -> []
          | chosen ->
              let source = Project.source project file in
              let edits =
                List.concat_map
                  (fun (diagnostic : Diagnostic.t) ->
                    match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
                  chosen
              in
              Project.write_file (Project.path project file) (apply (Source.text source) edits);
              List.map (fun diagnostic -> Diagnostic.to_json_object source diagnostic) chosen)
        (Project.files project)
      @ unused_dependencies project @ lock_file project
    in
    if applied = [] || number = rounds then List.rev fixed
    else begin
      Project.reload project;
      round (number + 1) (List.rev_append applied fixed)
    end
  in
  round 1 []

(* A check also lists the overlaps between this worktree's changes and those
   of the repository's other open worktrees. An overlap is not a
   diagnostic, since neither worktree's code has an error, so it does not
   change the exit status. *)
let run ~fix:fixing ~proofs =
  let project = Project.current () in
  let fixed = if fixing then fix project else [] in
  let report = Report.gather ~proofs project in
  let overlaps = Overlap_command.with_other_worktrees project.session in
  if Output.json () then
    Json.print
      (Report.document report
         ((if fixing then
             [ ("fixed", Json.List (List.map (fun fixed_text -> Json.Raw fixed_text) fixed)) ]
           else [])
         @ [ ("overlaps", Overlap_command.to_json overlaps) ]))
  else begin
    if fixed <> [] then
      Output.eprintf "Fixed %s.\n" (Report.plural (List.length fixed) "error" "errors");
    Report.print report;
    if overlaps <> [] then begin
      Output.print_line "Overlaps with other worktrees:";
      Overlap_command.print overlaps
    end
  end;
  if Report.clean report then 0 else 1

module For_testing = struct
  let chosen = chosen
end
