module Part = Pipeline.Part

module Part_set = Set.Make (struct
  type t = Part.t

  let compare = compare
end)

type place = { path : Path.t; kinds : string list }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

type merge_diagnostic = { file : string; diagnostic : Diagnostic.t }

type comparison = {
  other : string;
  overlaps : overlap list;
  merged : merge_diagnostic list;
  error : string option;
}

let describe place =
  Printf.sprintf "the %s of %s" (Output.listed place.kinds) (Path.show place.path)

let sentence = function
  | Both_change place -> "both change " ^ describe place
  | Reads { this_worktree; change; reads } ->
      Printf.sprintf "%s worktree's change to %s, in its %s, reads %s, which the other changes"
        (if this_worktree then "this" else "the other")
        (Path.show change.path) (Output.listed change.kinds) (describe reads)

let own_changes snapshot pipeline base =
  let own = List.map snd (Workspace.packages snapshot) in
  Part_set.of_list
    (List.filter
       (fun part ->
         match Part.definition part with
         | Some path -> List.mem (Path.package path) own
         | None -> false)
       (Pipeline.changes pipeline base))

let places_of parts =
  let kinds = Hashtbl.create 16 in
  Part_set.iter
    (fun part ->
      Option.iter
        (fun path ->
          Hashtbl.replace kinds path
            (Part.kind_name part :: Option.value (Hashtbl.find_opt kinds path) ~default:[]))
        (Part.definition part))
    parts;
  Hashtbl.fold
    (fun path kinds places -> { path; kinds = List.sort_uniq compare kinds } :: places)
    kinds []

let reading_overlaps ~this_worktree pipeline ~changed ~changed_by_other =
  let groups = Hashtbl.create 16 in
  List.iter
    (fun ({ dependent; dependency } : Pipeline.read) ->
      if
        Part_set.mem dependent changed
        && Part_set.mem dependency changed_by_other
        && not (Part_set.mem dependency changed)
      then
        match (Part.definition dependent, Part.definition dependency) with
        | Some change, Some read ->
            let changes, reads =
              Option.value (Hashtbl.find_opt groups (change, read)) ~default:([], [])
            in
            Hashtbl.replace groups (change, read)
              (Part.kind_name dependent :: changes, Part.kind_name dependency :: reads)
        | _ -> ())
    (Pipeline.dependencies pipeline
       (List.sort_uniq Path.compare (List.filter_map Part.definition (Part_set.elements changed))));
  Hashtbl.fold
    (fun (change, read) (changes, reads) overlaps ->
      Reads
        {
          this_worktree;
          change = { path = change; kinds = List.sort_uniq compare changes };
          reads = { path = read; kinds = List.sort_uniq compare reads };
        }
      :: overlaps)
    groups []

let overlaps snapshot pipeline (side : Workspace.side) =
  let base = Workspace.pipeline side.base and theirs = Workspace.pipeline side.other in
  let mine_changed = own_changes snapshot pipeline base in
  let theirs_changed = own_changes side.other theirs base in
  List.sort compare
    (List.map
       (fun place -> Both_change place)
       (places_of (Part_set.inter mine_changed theirs_changed))
    @ reading_overlaps ~this_worktree:true pipeline ~changed:mine_changed
        ~changed_by_other:theirs_changed
    @ reading_overlaps ~this_worktree:false theirs ~changed:theirs_changed
        ~changed_by_other:mine_changed)

let keyed_diagnostics snapshot =
  let pipeline = Workspace.pipeline snapshot in
  let packages = List.map snd (Workspace.packages snapshot) in
  Pipeline.check pipeline packages;
  List.concat_map
    (fun file ->
      List.map
        (fun (diagnostic : Diagnostic.t) ->
          ( ( Workspace.file_path snapshot file,
              Diagnostic.Code.name diagnostic.code,
              diagnostic.message ),
            diagnostic ))
        (Pipeline.file_diagnostics pipeline file))
    (Command_packages.files snapshot packages)

let merge_diagnostics snapshot (side : Workspace.side) =
  Result.map
    (fun merged ->
      let sides = List.map fst (keyed_diagnostics snapshot @ keyed_diagnostics side.other) in
      List.filter_map
        (fun (((file, _, _) as key), diagnostic) ->
          if List.mem key sides then None else Some { file; diagnostic })
        (List.sort_uniq (fun (left, _) (right, _) -> compare left right) (keyed_diagnostics merged)))
    (side.merged ())

let compare_with ~merge snapshot pipeline (other, side) =
  match side with
  | Error message -> { other; overlaps = []; merged = []; error = Some message }
  | Ok side -> (
      let overlaps = overlaps snapshot pipeline side in
      match if merge then merge_diagnostics snapshot side else Ok [] with
      | Ok merged -> { other; overlaps; merged; error = None }
      | Error message -> { other; overlaps; merged = []; error = Some message })

let place_json place =
  Json.Object
    [
      ("path", Json.String (Path.show place.path));
      ("parts", Json.List (List.map (fun kind -> Json.String kind) place.kinds));
    ]

let overlap_json = function
  | Both_change place ->
      Json.Object [ ("kind", Json.String "both_change"); ("place", place_json place) ]
  | Reads { this_worktree; change; reads } ->
      Json.Object
        [
          ("kind", Json.String "reads");
          ("this_worktree", Json.Bool this_worktree);
          ("change", place_json change);
          ("reads", place_json reads);
        ]

let to_json comparisons =
  Json.List
    (List.map
       (fun comparison ->
         Json.Object
           [
             ("other", Json.String comparison.other);
             ("overlaps", Json.List (List.map overlap_json comparison.overlaps));
             ( "merged",
               Json.List
                 (List.map
                    (fun { file; diagnostic } ->
                      Json.Object
                        [
                          ("file", Json.String file);
                          ("code", Json.String (Diagnostic.Code.name diagnostic.code));
                          ("message", Json.String diagnostic.message);
                        ])
                    comparison.merged) );
             ("error", Json.option (fun error -> Json.String error) comparison.error);
           ])
       comparisons)

let print comparisons =
  List.iter
    (fun comparison ->
      List.iter
        (fun overlap -> Output.printf "  %s: %s\n" comparison.other (sentence overlap))
        comparison.overlaps;
      List.iter
        (fun { file; diagnostic } ->
          Output.printf "  %s: merged: %s: %s: %s\n" comparison.other file
            (Diagnostic.Code.name diagnostic.code)
            diagnostic.message)
        comparison.merged;
      Option.iter (fun error -> Output.printf "  %s: %s\n" comparison.other error) comparison.error)
    comparisons

let worktree_sides snapshot =
  List.map
    (fun other -> (Shown_path.shown other, Workspace.other_worktree snapshot other))
    (Workspace.other_worktrees snapshot)

let with_other_worktrees snapshot pipeline =
  List.filter
    (fun comparison -> comparison.overlaps <> [])
    (List.map (compare_with ~merge:false snapshot pipeline) (worktree_sides snapshot))

let run ~with_ ~merge =
  let snapshot, _ = Command_packages.current () in
  let pipeline = Workspace.pipeline snapshot in
  let sides =
    match with_ with
    | Some name -> (
        match Workspace.branch snapshot name with
        | Ok side -> [ (name, Ok side) ]
        | Error message -> Outcome.cannot_run "%s" message)
    | None -> worktree_sides snapshot
  in
  let comparisons = List.map (compare_with ~merge snapshot pipeline) sides in
  if Output.json () then
    Json.print (Json.document ~diagnostics:[] [ ("overlaps", to_json comparisons) ])
  else if sides = [] then
    Output.print_line "No other worktree of this repository is open, and no branch was named."
  else if
    List.for_all
      (fun comparison ->
        comparison.overlaps = [] && comparison.merged = [] && comparison.error = None)
      comparisons
  then
    Output.print_line
      (if merge then "No overlap, and merging gives no new error." else "No overlap.")
  else print comparisons;
  0
