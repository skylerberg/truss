(* [truss impact]: the definitions that the worktree changes since a base
   commit, and their dependents.

   The worktree's session is compared with a session of the base commit.
   Every result that depends on a changed input is updated in both and
   compared, so a result recomputed with the same value counts as
   unchanged. Reformatting a file, or moving a definition within its file,
   changes nothing. *)

module Names = Resolve.Names

type change = {
  path : Path.t;
  status : [ `Added | `Removed | `Changed of string list ];  (** The parts that changed *)
  before : string option;  (** The signature at the base, when it changed *)
  after : string option;  (** The signature now *)
  dependents : Graph_types.edge list;  (** The edges to its changed signature *)
}

let declarations context packages =
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          List.filter
            (fun (declaration : Names.declaration) -> declaration.ordinal = 0)
            (try Query.demand context Names.declarations module_ with Not_found -> []))
        (Query.demand context Workspace.modules name))
    packages

(* Each definition that changed, was added, or was removed, in order. *)
let changes (project : Project.t) base =
  let mine = project.session in
  let changed = Hashtbl.create 32 in
  let order = ref [] in
  List.iter
    (fun (path, part, (difference : Graph_types.difference)) ->
      if difference <> Same then begin
        if not (Hashtbl.mem changed path) then order := path :: !order;
        let parts = Option.value (Hashtbl.find_opt changed path) ~default:[] in
        let part = Option.value part ~default:"definition" in
        Hashtbl.replace changed path (if List.mem part parts then parts else parts @ [ part ])
      end)
    (Database.changes mine base);
  let old_context = Database.context base and context = project.context in
  let paths context session =
    List.map
      (fun (declaration : Names.declaration) -> declaration.path)
      (declarations context (Database.packages session))
  in
  let old_paths = paths old_context base and now = paths context mine in
  let is_existing path = List.exists (Path.equal path) old_paths in
  let is_signature_changed path =
    List.exists (fun part -> List.mem part Signatures.parts) (Hashtbl.find changed path)
  in
  let dependents =
    Database.dependents mine
      (List.filter (fun path -> is_existing path && is_signature_changed path) !order)
  in
  let changes =
    List.rev_map
      (fun path ->
        let parts = Hashtbl.find changed path in
        if not (is_existing path) then
          {
            path;
            status = `Added;
            before = None;
            after = Signatures.of_path context path;
            dependents = [];
          }
        else
          {
            path;
            status = `Changed parts;
            before =
              (if is_signature_changed path then Signatures.of_path old_context path else None);
            after = (if is_signature_changed path then Signatures.of_path context path else None);
            dependents =
              List.filter
                (fun (edge : Graph_types.edge) -> Path.equal edge.dependency path)
                dependents;
          })
      !order
  in
  let removed =
    List.filter_map
      (fun path ->
        if List.exists (Path.equal path) now then None
        else
          Some
            {
              path;
              status = `Removed;
              before = Signatures.of_path old_context path;
              after = None;
              dependents = [];
            })
      old_paths
  in
  changes @ removed

(* The tests whose code changed since the base, which are the tests whose
   key differs, each with whether a result is cached for its current key.
   A test's key is the hash of the code it can reach. Computing keys lowers
   code but compiles nothing, so it needs no C compiler. *)
let tests_changed (project : Project.t) base =
  let keys context session =
    Compile.test_keys
      (Compiler.lowering_only session context)
      (List.filter_map
         (fun (declaration : Names.declaration) ->
           match declaration.path with Test _ -> Some declaration.path | _ -> None)
         (declarations context (Database.packages session)))
  in
  let mine = keys project.context project.session in
  let theirs = keys (Database.context base) base in
  let results = Compiler.test_results () in
  List.filter_map
    (fun (path, key) ->
      match List.find_opt (fun (their_path, _) -> Path.equal their_path path) theirs with
      | Some (_, base_key) when base_key = key -> None
      | _ -> Some (path, results.find key <> None))
    mine

let status_word = function `Added -> "added" | `Removed -> "removed" | `Changed _ -> "changed"

let dependents_json dependents =
  Json.List
    (List.map
       (fun (edge : Graph_types.edge) ->
         Json.Object
           [
             ("reader", Json.String (Path.show edge.dependent));
             ("part", Json.String edge.dependent_part);
             ("reads", Json.String edge.dependency_part);
           ])
       dependents)

let change_json change =
  Json.Object
    [
      ("path", Json.String (Path.show change.path));
      ("change", Json.String (status_word change.status));
      ( "parts",
        Json.List
          (match change.status with
          | `Changed parts -> List.map (fun part -> Json.String part) parts
          | _ -> []) );
      ("before", Json.option (fun text -> Json.String text) change.before);
      ("after", Json.option (fun text -> Json.String text) change.after);
      ("read_by", dependents_json change.dependents);
    ]

let print_change change =
  Output.printf "  %s: %s\n" (Path.show change.path)
    (match change.status with
    | `Changed parts -> String.concat ", " parts
    | status -> status_word status);
  Option.iter (fun text -> Output.print_line (Signatures.labeled "was:" text)) change.before;
  Option.iter (fun text -> Output.print_line (Signatures.labeled "now:" text)) change.after;
  if change.dependents <> [] then
    Output.printf "    read by: %s\n"
      (String.concat ", "
         (List.sort_uniq compare
            (List.map (fun (edge : Graph_types.edge) -> Path.show edge.dependent) change.dependents)))

let run ~directory ~base ~json =
  let project = Project.load directory in
  let report = Report.gather project in
  let session = project.session in
  match Database.base_commit session base with
  | None ->
      Project.cannot_run
        "No base commit: name one with --base, or work in a git worktree with a default branch."
  | Some commit -> (
      match Database.open_commit_of session commit with
      | Error message -> Project.cannot_run "%s" message
      | Ok base_session ->
          let changes = changes project base_session in
          (* Lowering requires code without diagnostics. *)
          let tests = if Report.clean report then tests_changed project base_session else [] in
          if json then
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
                                ("test", Json.String (Path.show path)); ("kept", Json.Bool is_cached);
                              ])
                          tests) );
                 ])
          else begin
            Report.print report;
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
          end;
          if Report.clean report then 0 else 1)
