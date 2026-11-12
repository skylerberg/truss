(* [truss check]: every diagnostic in the package, and with [--fix], the
   fixes that have no alternative applied. *)

(* The fixes of one round in one file: each diagnostic's only fix, leaving
   out any whose edits overlap an earlier one's, since applying both could
   give a result neither intended. They are applied in the next round once the
   file is checked again. *)
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

(* Applies non-overlapping edits to a text, from the last to the first, so
   each edit's offsets still hold when it is applied. *)
let apply text (edits : Diagnostic.span Diagnostic.edit list) =
  List.sort
    (fun (left : Diagnostic.span Diagnostic.edit) right -> compare right.span.start left.span.start)
    edits
  |> List.fold_left
       (fun text (edit : Diagnostic.span Diagnostic.edit) ->
         String.sub text 0 edit.span.start ^ edit.replacement
         ^ String.sub text edit.span.stop (String.length text - edit.span.stop))
       text

(* Rounds are bounded, so fixes that undo each other cannot run forever. *)
let rounds = 32

(* Deletes each entry of a dependency that nothing in its package uses, which
   is that problem's only fix, and returns each as JSON. A grant is never
   added: that is a choice, which a reviewer is to see someone made. *)
let unused_dependencies (project : Project.t) =
  let root = Database.root project.session in
  List.filter_map
    (fun (file, package, (problem : Type_checker.manifest_problem)) ->
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
                    ("message", Json.String (Type_checker.manifest_sentence ~package problem));
                  ]))
      | Not_a_capability _ -> None)
    (Project.manifest_problems project)

(* Writes the lock file the manifests give, when the one written is another,
   which is that problem's only fix. No version is chosen by it: a line the
   manifests need and no lock file or record gives is `truss add`'s. *)
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

(* Applies fixes until none is left to apply, and returns the diagnostics
   they fixed, each as JSON in the file it was in when it was fixed. *)
let fix (project : Project.t) =
  let rec round number fixed =
    let applied =
      List.concat_map
        (fun module_ ->
          let diagnostics = Database.diagnostics project.session module_ in
          match chosen diagnostics with
          | [] -> []
          | chosen ->
              let source = Project.source project module_ in
              let edits =
                List.concat_map
                  (fun (diagnostic : Diagnostic.t) ->
                    match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
                  chosen
              in
              Project.write_file (Project.file project module_) (apply (Source.text source) edits);
              List.map (fun diagnostic -> Diagnostic.to_json_object source diagnostic) chosen)
        (Project.modules project)
      @ unused_dependencies project @ lock_file project
    in
    if applied = [] || number = rounds then List.rev fixed
    else begin
      Project.reload project;
      round (number + 1) (List.rev_append applied fixed)
    end
  in
  round 1 []

(* A check also lists where this worktree's changes meet those of other
   open worktrees of the repository. Overlaps are not diagnostics: nothing is wrong with either worktree's
   code, so they do not change the exit status. *)
let run ~directory ~fix:fixing ~proofs ~json =
  let project = Project.load directory in
  let fixed = if fixing then fix project else [] in
  let report = Report.gather ~proofs project in
  let overlaps = Overlap_command.with_other_worktrees project.session in
  if json then
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
