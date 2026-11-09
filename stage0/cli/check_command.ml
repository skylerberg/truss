(* [truss check]: every diagnostic in the package, and with [--fix], the
   fixes that have no alternative applied. See CLI.md, "Checking". *)

(* The fixes of one round in one file: each diagnostic's only fix, leaving
   out any whose edits overlap an earlier one's, since applying both could
   not give what either meant. They are applied in the next round once the
   file is checked again. *)
let chosen (diagnostics : Diagnostic.t list) =
  let overlaps (a : Diagnostic.edit) (b : Diagnostic.edit) =
    (a.span.start < b.span.stop && b.span.start < a.span.stop)
    || (a.span.start = b.span.start && (a.span.start = a.span.stop || b.span.start = b.span.stop))
  in
  let taken = ref [] in
  List.filter
    (fun (diagnostic : Diagnostic.t) ->
      match diagnostic.fixes with
      | [ fix ] ->
          let clear =
            List.for_all
              (fun (edit : Diagnostic.edit) -> not (List.exists (overlaps edit) !taken))
              fix.edits
          in
          if clear then taken := fix.edits @ !taken;
          clear
      | _ -> false)
    diagnostics

(* Applies non-overlapping edits to a text, from the last to the first, so
   each edit's offsets still hold when it is applied. *)
let apply text (edits : Diagnostic.edit list) =
  List.sort (fun (a : Diagnostic.edit) b -> compare b.span.start a.span.start) edits
  |> List.fold_left
       (fun text (edit : Diagnostic.edit) ->
         String.sub text 0 edit.span.start ^ edit.replacement
         ^ String.sub text edit.span.stop (String.length text - edit.span.stop))
       text

(* Rounds are bounded, so fixes that undo each other cannot run forever. *)
let rounds = 32

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
    in
    if applied = [] || number = rounds then List.rev fixed
    else begin
      Project.reload project;
      round (number + 1) (List.rev_append applied fixed)
    end
  in
  round 1 []

(* A check also lists where this worktree's changes meet those of other
   open worktrees of the repository, as DATABASE.md's "Parallel work" asks.
   Overlaps are not diagnostics: nothing is wrong with either worktree's
   code, so they do not change the exit status. *)
let run ~directory ~fix:fixing ~json =
  let project = Project.load directory in
  let fixed = if fixing then fix project else [] in
  let report = Report.gather project in
  let overlaps = Overlap_command.with_other_worktrees project.session in
  if json then
    Json.print
      (Report.document report
         ((if fixing then [ ("fixed", Json.List (List.map (fun d -> Json.Raw d) fixed)) ] else [])
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
