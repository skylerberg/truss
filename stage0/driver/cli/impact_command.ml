module Names = Resolve.Names
module Part = Pipeline.Part

type status = Added | Removed | Changed of string list

type change = {
  path : Path.t;
  status : status;
  before : string option;
  after : string option;
  read_by : Pipeline.read list;
}

type revision = {
  snapshot : Database.snapshot;
  pipeline : Pipeline.t;
  names : Names.lookups;
  declared : Path.Set.t;
}

let revision snapshot pipeline =
  let packages = List.map snd (Database.packages snapshot) in
  let names = Pipeline.names pipeline packages in
  {
    snapshot;
    pipeline;
    names;
    declared =
      Path.Set.of_list
        (List.concat_map
           (fun package ->
             List.filter_map
               (fun (declaration : Names.declaration) ->
                 if declaration.ordinal = 0 then Some declaration.path else None)
               (names.package_declarations package))
           packages);
  }

let changes ~now ~before changed_parts =
  let own = List.map snd (Database.packages now.snapshot) in
  let by_definition = Hashtbl.create 32 in
  List.iter
    (fun part ->
      match Part.definition part with
      | Some path when List.mem (Path.package path) own ->
          Hashtbl.replace by_definition path
            (part :: Option.value (Hashtbl.find_opt by_definition path) ~default:[])
      | Some _ | None -> ())
    changed_parts;
  let signature_parts = List.filter Signatures.is_signature changed_parts in
  let signature_readers =
    List.filter
      (fun ({ dependency; _ } : Pipeline.read) -> List.mem dependency signature_parts)
      (Pipeline.dependents now.pipeline
         (List.sort_uniq Path.compare (List.filter_map Part.definition signature_parts)))
  in
  List.sort
    (fun left right -> Path.compare left.path right.path)
    (Hashtbl.fold
       (fun path parts changes ->
         let change =
           if Path.Set.mem path now.declared && not (Path.Set.mem path before.declared) then
             {
               path;
               status = Added;
               before = None;
               after = Signatures.of_path now.names path;
               read_by = [];
             }
           else if Path.Set.mem path before.declared && not (Path.Set.mem path now.declared) then
             {
               path;
               status = Removed;
               before = Signatures.of_path before.names path;
               after = None;
               read_by = [];
             }
           else
             let is_signature_changed = List.exists Signatures.is_signature parts in
             {
               path;
               status = Changed (List.sort_uniq compare (List.map Part.kind_name parts));
               before =
                 (if is_signature_changed then Signatures.of_path before.names path else None);
               after = (if is_signature_changed then Signatures.of_path now.names path else None);
               read_by =
                 List.filter
                   (fun ({ dependency; _ } : Pipeline.read) ->
                     Part.definition dependency = Some path)
                   signature_readers;
             }
         in
         change :: changes)
       by_definition [])

let tests_changed ~now ~before =
  let own revision = List.map snd (Database.packages revision.snapshot) in
  let compile = Compiler.lowering_only now.pipeline (own now)
  and base_compile = lazy (Compiler.lowering_only before.pipeline (own before)) in
  List.filter_map
    (fun (path : Path.t) ->
      match path with
      | Test _ -> (
          let base_key =
            if Path.Set.mem path before.declared then
              Compile.result_key (Lazy.force base_compile) path
            else None
          in
          match Compile.result_key compile path with
          | key when key = base_key -> None
          | Some key -> Some (path, Compile.is_cached compile path ~key)
          | None -> Some (path, false))
      | _ -> None)
    (Path.Set.elements now.declared)

let status_word = function Added -> "added" | Removed -> "removed" | Changed _ -> "changed"

let reading_definitions (change : change) =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun ({ dependent; _ } : Pipeline.read) -> Part.definition dependent)
       change.read_by)

let read_by_json read_by =
  Json.List
    (List.filter_map
       (fun ({ dependent; dependency } : Pipeline.read) ->
         Option.map
           (fun reader ->
             Json.Object
               [
                 ("reader", Json.String (Path.show reader));
                 ("part", Json.String (Part.kind_name dependent));
                 ("reads", Json.String (Part.kind_name dependency));
               ])
           (Part.definition dependent))
       read_by)

let change_json change =
  Json.Object
    [
      ("path", Json.String (Path.show change.path));
      ("change", Json.String (status_word change.status));
      ( "parts",
        Json.List
          (match change.status with
          | Changed kinds -> List.map (fun kind -> Json.String kind) kinds
          | Added | Removed -> []) );
      ("before", Json.option (fun text -> Json.String text) change.before);
      ("after", Json.option (fun text -> Json.String text) change.after);
      ("read_by", read_by_json change.read_by);
    ]

let print_change change =
  Output.printf "  %s: %s\n" (Path.show change.path)
    (match change.status with
    | Changed kinds -> String.concat ", " kinds
    | status -> status_word status);
  Option.iter (fun text -> Output.print_line (Signatures.labeled "was:" text)) change.before;
  Option.iter (fun text -> Output.print_line (Signatures.labeled "now:" text)) change.after;
  match reading_definitions change with
  | [] -> ()
  | readers -> Output.printf "    read by: %s\n" (String.concat ", " (List.map Path.show readers))

let print ~commit changes tests =
  let short = String.sub commit 0 (min 12 (String.length commit)) in
  if changes = [] then Output.printf "Nothing changed since %s.\n" short
  else begin
    Output.printf "Changed since %s:\n" short;
    List.iter print_change changes
  end;
  if tests <> [] then begin
    let cached_count = List.length (List.filter snd tests) in
    Output.printf "\nTests whose code changed: %d%s\n" (List.length tests)
      (if cached_count > 0 then Printf.sprintf " (%d cached)" cached_count else "");
    List.iter
      (fun (path, is_cached) ->
        Output.printf "  %s%s\n" (Path.show path) (if is_cached then "  cached" else ""))
      tests
  end

let run ~base =
  let snapshot, packages = Command_packages.current () in
  let pipeline = Database.pipeline snapshot in
  let report = Report.gather pipeline snapshot packages in
  match Database.base_commit snapshot base with
  | None ->
      Outcome.cannot_run
        "No base commit: name one with --base, or work in a git worktree with a default branch."
  | Some commit -> (
      match Database.of_commit snapshot commit with
      | Error message -> Outcome.cannot_run "%s" message
      | Ok base_snapshot ->
          let base = Database.pipeline base_snapshot in
          let changed_parts = Pipeline.changes pipeline base in
          let now = revision snapshot pipeline and before = revision base_snapshot base in
          let changes = changes ~now ~before changed_parts in
          let tests = if Report.clean report then tests_changed ~now ~before else [] in
          if Output.json () then
            Json.print
              (Report.document report
                 [
                   ("base", Json.String commit);
                   ("changes", Json.List (List.map change_json changes));
                   ( "tests",
                     Json.List
                       (List.map
                          (fun (path, is_cached) ->
                            Json.Object
                              [
                                ("test", Json.String (Path.show path));
                                ("cached", Json.Bool is_cached);
                              ])
                          tests) );
                 ])
          else begin
            Report.print report;
            print ~commit changes tests
          end;
          if Report.clean report then 0 else 1)
