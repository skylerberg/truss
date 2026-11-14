(* [truss overlap]: the overlaps between this worktree's changes and those
   of the repository's other open worktrees, or of a branch, and with
   [--merge], the diagnostics that only the merge result has. *)

let describe (place : Graph_types.place) =
  match place.path with
  | Some path ->
      Printf.sprintf "the %s of %s" (Option.value place.part ~default:"definition") (Path.show path)
  | None -> place.label

let sentence : Graph_types.overlap -> string = function
  | Both_change place -> "both change " ^ describe place
  | Reads { this_worktree; change; reads } ->
      Printf.sprintf "%s worktree's change to %s reads %s, which the other changes"
        (if this_worktree then "this" else "the other")
        (describe change) (describe reads)

type comparison = {
  other : string;  (** The other worktree, relative to the current directory, or the branch *)
  overlaps : Graph_types.overlap list;
  merged : (string * string * string) list;  (** A merge's new diagnostics: file, code, message *)
  error : string option;
}

let place_json (place : Graph_types.place) =
  Json.Object
    [
      ("path", Json.option (fun path -> Json.String (Path.show path)) place.path);
      ("part", Json.option (fun path -> Json.String path) place.part);
    ]

let overlap_json : Graph_types.overlap -> Json.t = function
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
                    (fun (file, code, message) ->
                      Json.Object
                        [
                          ("file", Json.String file);
                          ("code", Json.String code);
                          ("message", Json.String message);
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
        (fun (file, code, message) ->
          Output.printf "  %s: merged: %s: %s: %s\n" comparison.other file code message)
        comparison.merged;
      Option.iter (fun error -> Output.printf "  %s: %s\n" comparison.other error) comparison.error)
    comparisons

let compare_with ~merge session (name, other) =
  let overlaps, error =
    match Database.overlap_with session other with
    | Ok overlaps -> (overlaps, None)
    | Error message -> ([], Some message)
  in
  let merged, error =
    if not merge then ([], error)
    else
      match Database.merge_preview session other with
      | Ok merged -> (merged, error)
      | Error message -> ([], Some message)
  in
  { other = name; overlaps; merged; error }

(* The overlaps with each other open worktree that has any, for [truss
   check]. *)
let with_other_worktrees session =
  List.filter_map
    (fun other ->
      match Database.overlap_with session other with
      | Ok (_ :: _ as overlaps) ->
          Some
            { other = Shown_path.shown (Database.root other); overlaps; merged = []; error = None }
      | _ -> None)
    (Database.other_worktrees session)

let run ~with_ ~merge =
  let session, _ = Command_packages.current () in
  let others =
    match with_ with
    | Some branch -> (
        match Database.base_commit session (Some branch) with
        | None -> Outcome.cannot_run "No commit is named %s." branch
        | Some commit -> (
            match Database.open_commit_of session commit with
            | Ok other -> [ (branch, other) ]
            | Error message -> Outcome.cannot_run "%s" message))
    | None ->
        List.map
          (fun other -> (Shown_path.shown (Database.root other), other))
          (Database.other_worktrees session)
  in
  let comparisons = List.map (compare_with ~merge session) others in
  if Output.json () then
    Json.print (Json.document ~diagnostics:[] [ ("overlaps", to_json comparisons) ])
  else if others = [] then
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

module For_testing = struct
  let sentence = sentence
end
