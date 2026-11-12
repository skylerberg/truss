(* [truss impact]: what the worktree's changes from a base commit reach.

   The worktree's session is compared with a session of the base commit:
   every result a changed input can reach is brought up to date and
   compared, so a part that was checked again but came out the same is
   told apart from one that changed, and reformatting, or moving a
   definition within its file, changes nothing. *)

module Names = Resolve.Names

type change = {
  path : Path.t;
  status : [ `Added | `Removed | `Changed of string list ];  (** The parts that changed *)
  before : string option;  (** The signature at the base, when it changed *)
  after : string option;  (** The signature now *)
  read_by : (Path.t * string * string) list;
      (** What reads its changed signature: each reader, its part, and the part it reads *)
}

(* The parts a definition's callers read. *)
let signature_parts = [ "interface"; "signature"; "shape" ]

let declarations context packages =
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          List.filter
            (fun (d : Names.declaration) -> d.ordinal = 0)
            (try Query.demand context Names.declarations module_ with Not_found -> []))
        (Query.demand context Workspace.modules name))
    packages

let signature context path =
  match Query.demand context Interface.Summary.key path with
  | Some key -> Signatures.text context ~body:false ~opaque:false key
  | None -> None

(* Each definition that changed, was added, or was removed, in order. *)
let changes (project : Project.t) base =
  let mine = project.session in
  let changed = Hashtbl.create 32 in
  let order = ref [] in
  List.iter
    (fun (path, part, (difference : Database.difference)) ->
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
      (fun (d : Names.declaration) -> d.path)
      (declarations context (Database.packages session))
  in
  let old_paths = paths old_context base and now = paths context mine in
  let dependencies = lazy (Database.dependencies mine) in
  let changes =
    List.rev_map
      (fun path ->
        let parts = Hashtbl.find changed path in
        if not (List.exists (Path.equal path) old_paths) then
          { path; status = `Added; before = None; after = signature context path; read_by = [] }
        else
          let signature_changed = List.exists (fun p -> List.mem p signature_parts) parts in
          {
            path;
            status = `Changed parts;
            before = (if signature_changed then signature old_context path else None);
            after = (if signature_changed then signature context path else None);
            read_by =
              (if signature_changed then
                 List.filter
                   (fun (reader, _, _) -> not (Path.equal reader path))
                   (Database.readers (Lazy.force dependencies) path)
               else []);
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
              before = signature old_context path;
              after = None;
              read_by = [];
            })
      old_paths
  in
  changes @ removed

(* The tests whose code changed since the base: those whose key, the hash of
   the code each can run, differs, each with whether its result is kept for
   its code now. Finding keys lowers code and compiles nothing, so it needs
   no C compiler. *)
let tests_changed (project : Project.t) base =
  let keys context session =
    let compile =
      Compile.create context (Compiler.target ())
        { compiler = "cc"; identity = "lowering only" }
        (Build.cache (Database.objects_directory ()))
        { build = Development; optimization = O1; extra = [] }
    in
    Compile.test_keys compile
      (List.filter_map
         (fun (d : Names.declaration) -> match d.path with Test _ -> Some d.path | _ -> None)
         (declarations context (Database.packages session)))
  in
  let mine = keys project.context project.session in
  let theirs = keys (Database.context base) base in
  let results = Compiler.test_results () in
  List.filter_map
    (fun (path, key) ->
      match List.find_opt (fun (p, _) -> Path.equal p path) theirs with
      | Some (_, base_key) when base_key = key -> None
      | _ -> Some (path, results.find key <> None))
    mine

let status_word = function `Added -> "added" | `Removed -> "removed" | `Changed _ -> "changed"

let readers_json read_by =
  Json.List
    (List.map
       (fun (reader, part, read) ->
         Json.Object
           [
             ("reader", Json.String (Path.show reader));
             ("part", Json.String part);
             ("reads", Json.String read);
           ])
       read_by)

let change_json c =
  Json.Object
    [
      ("path", Json.String (Path.show c.path));
      ("change", Json.String (status_word c.status));
      ( "parts",
        Json.List
          (match c.status with
          | `Changed parts -> List.map (fun p -> Json.String p) parts
          | _ -> []) );
      ("before", Json.option (fun s -> Json.String s) c.before);
      ("after", Json.option (fun s -> Json.String s) c.after);
      ("read_by", readers_json c.read_by);
    ]

let print_signature label text =
  match String.split_on_char '\n' text with
  | first :: rest ->
      Output.printf "    %s %s\n" label first;
      List.iter
        (fun line -> Output.printf "    %s %s\n" (String.make (String.length label) ' ') line)
        rest
  | [] -> ()

let print_change c =
  Output.printf "  %s: %s\n" (Path.show c.path)
    (match c.status with
    | `Changed parts -> String.concat ", " parts
    | status -> status_word status);
  Option.iter (print_signature "was:") c.before;
  Option.iter (print_signature "now:") c.after;
  if c.read_by <> [] then
    Output.printf "    read by: %s\n"
      (String.concat ", "
         (List.sort_uniq compare (List.map (fun (reader, _, _) -> Path.show reader) c.read_by)))

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
          (* Lowering needs code without errors. *)
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
                          (fun (path, kept) ->
                            Json.Object
                              [ ("test", Json.String (Path.show path)); ("kept", Json.Bool kept) ])
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
              let kept = List.length (List.filter snd tests) in
              Output.printf "\nTests whose code changed: %d%s\n" (List.length tests)
                (if kept > 0 then Printf.sprintf " (%d kept)" kept else "");
              List.iter
                (fun (path, kept) ->
                  Output.printf "  %s%s\n" (Path.show path) (if kept then "  kept" else ""))
                tests
            end
          end;
          if Report.clean report then 0 else 1)
