(* [truss overlap]: where this worktree's changes meet those of other open
   worktrees of the repository, or of a branch, and with [--merge], the
   errors a merge of the two would have that neither has. See DATABASE.md,
   "Parallel work". *)

let describe (place : Database.place) =
  match place.path with
  | Some path ->
      Printf.sprintf "the %s of %s" (Option.value place.part ~default:"definition") (Path.show path)
  | None -> place.label

let sentence : Database.overlap -> string = function
  | Both_change place -> "both change " ^ describe place
  | Reads { this_worktree; change; reads } ->
      Printf.sprintf "%s worktree's change to %s reads %s, which the other changes"
        (if this_worktree then "this" else "the other")
        (describe change) (describe reads)

type found = {
  other : string;  (** The other worktree, as the current directory reaches it, or the branch *)
  overlaps : Database.overlap list;
  merged : (string * string * string) list;  (** A merge's new diagnostics: file, code, message *)
  error : string option;
}

let place_json (place : Database.place) =
  Json.Object
    [
      ("path", Json.option (fun p -> Json.String (Path.show p)) place.path);
      ("part", Json.option (fun p -> Json.String p) place.part);
    ]

let overlap_json : Database.overlap -> Json.t = function
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

let to_json found =
  Json.List
    (List.map
       (fun f ->
         Json.Object
           [
             ("other", Json.String f.other);
             ("overlaps", Json.List (List.map overlap_json f.overlaps));
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
                    f.merged) );
             ("error", Json.option (fun e -> Json.String e) f.error);
           ])
       found)

let print found =
  List.iter
    (fun f ->
      List.iter (fun o -> Output.printf "  %s: %s\n" f.other (sentence o)) f.overlaps;
      List.iter
        (fun (file, code, message) ->
          Output.printf "  %s: merged: %s: %s: %s\n" f.other file code message)
        f.merged;
      Option.iter (fun e -> Output.printf "  %s: %s\n" f.other e) f.error)
    found

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

(* The overlaps with every other open worktree, leaving out those with
   none, for [truss check]. *)
let with_other_worktrees session =
  List.filter_map
    (fun other ->
      match Database.overlap_with session other with
      | Ok (_ :: _ as overlaps) ->
          Some { other = Project.shown (Database.root other); overlaps; merged = []; error = None }
      | _ -> None)
    (Database.other_worktrees session)

let run ~directory ~with_ ~merge ~json =
  let project = Project.load directory in
  let session = project.session in
  let others =
    match with_ with
    | Some branch -> (
        match Database.base_commit session (Some branch) with
        | None -> Project.cannot_run "No commit is named %s." branch
        | Some commit -> (
            match Database.open_commit_of session commit with
            | Ok other -> [ (branch, other) ]
            | Error message -> Project.cannot_run "%s" message))
    | None ->
        List.map
          (fun other -> (Project.shown (Database.root other), other))
          (Database.other_worktrees session)
  in
  let found = List.map (compare_with ~merge session) others in
  if json then Json.print (Json.document ~diagnostics:[] [ ("overlaps", to_json found) ])
  else if others = [] then
    Output.print_line "No other worktree of this repository is open, and no branch was named."
  else if List.for_all (fun f -> f.overlaps = [] && f.merged = [] && f.error = None) found then
    Output.print_line
      (if merge then "No overlap, and merging gives no new error." else "No overlap.")
  else print found;
  0
