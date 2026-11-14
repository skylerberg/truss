(* [truss check]: every diagnostic of the packages, and with [--fix], each
   diagnostic's only fix applied. *)

(* Bounds the rounds, so two fixes that undo each other cannot loop
   forever. *)
let rounds = 32

(* Deletes the manifest entry of each unused dependency, which is that
   problem's only fix, and returns each deletion as JSON. A grant is never
   added: granting a capability is a decision that a reviewer must see a
   person make. *)
let unused_dependencies session packages =
  let root = Database.root session in
  List.filter_map
    (fun (file, package, (problem : Checks.manifest_problem)) ->
      match problem with
      | Unused dependency ->
          let path = Filename.concat root file in
          let text = In_channel.with_open_bin path In_channel.input_all in
          Command_packages.write_file path (Manifest.without_dependency text dependency);
          Some
            (Json.to_string
               (Json.Object
                  [
                    ("file", Json.String (Shown_path.shown path));
                    ("message", Json.String (Checks.manifest_sentence ~package problem));
                  ]))
      | Not_a_capability _ -> None)
    (Database.manifest_problems session packages)

(* Writes the canonical lock file when the lock file on disk differs, which
   is that problem's only fix. It never chooses a version: a dependency
   without a version in the lock file or any record needs `truss add`. *)
let lock_file session =
  match Database.lock_fix session with
  | None -> []
  | Some text ->
      let path = Filename.concat (Database.root session) "truss.lock" in
      Command_packages.write_file path text;
      [
        Json.to_string
          (Json.Object
             [
               ("file", Json.String (Shown_path.shown path));
               ("message", Json.String "This is not the lock file the manifests give.");
             ]);
      ]

(* Applies fixes until none remains, and returns the fixed diagnostics as
   JSON, each against the file text at the time of its fix. *)
let fix session packages =
  let rec round number fixed =
    let applied =
      List.concat_map
        (fun file ->
          let diagnostics = Database.diagnostics session file in
          match Diagnostic.machine_applicable diagnostics with
          | [] -> []
          | chosen ->
              let source = Command_packages.source session packages file in
              let edits =
                List.concat_map
                  (fun (diagnostic : Diagnostic.t) ->
                    match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
                  chosen
              in
              Command_packages.write_file
                (Command_packages.path session file)
                (Diagnostic.apply_edits (Source.text source) edits);
              List.map (fun diagnostic -> Diagnostic.to_json_object source diagnostic) chosen)
        (Command_packages.files session packages)
      @ unused_dependencies session packages
      @ lock_file session
    in
    if applied = [] || number = rounds then List.rev fixed
    else begin
      Database.refresh session;
      round (number + 1) (List.rev_append applied fixed)
    end
  in
  round 1 []

(* A check also lists the overlaps between this worktree's changes and those
   of the repository's other open worktrees. An overlap is not a
   diagnostic, since neither worktree's code has an error, so it does not
   change the exit status. *)
let run ~fix:fixing ~proofs =
  let session, packages = Command_packages.current () in
  let fixed = if fixing then fix session packages else [] in
  let report = Report.gather ~proofs session packages in
  let overlaps = Overlap_command.with_other_worktrees session in
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
