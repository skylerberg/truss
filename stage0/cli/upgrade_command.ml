(* [truss upgrade]: changes the versions of the project's registry
   packages, and reports the effect before writing the lock file. [truss
   add] prints the same report. *)

module Lock = Registry.Lock
module Version = Registry.Version

(* Parses a package argument, such as [acme::geometry], or with a version,
   such as [acme::geometry@1.4.2]. *)
let wanted text =
  let written, version =
    match String.index_opt text '@' with
    | Some at ->
        (String.sub text 0 at, Some (String.sub text (at + 1) (String.length text - at - 1)))
    | None -> (text, None)
  in
  let name =
    match Manifest.parse_name written with
    | Some ({ owner = Some _; _ } as name) -> name
    | _ ->
        Project.cannot_run
          "`%s` is not a registry package's name, which is an owner and a name, such as \
           `acme::geometry`."
          written
  in
  ( name,
    Option.map
      (fun version ->
        match Version.parse version with
        | Some version -> version
        | None ->
            Project.cannot_run "`%s` is not a version, which is three numbers, such as 1.4.2."
              version)
      version )

(* The differences between the old lock file and the new one. *)
type change =
  | Entered of Lock.entry
  | Left of Lock.entry
  | Moved of { name : Path.package; from : Version.t; to_ : Version.t }
  | Holds of { name : Path.package; gained : string list }
      (** A package that would be granted capabilities it lacks now *)

let lock_changes ~(before : Lock.t) ~(after : Lock.t) =
  List.concat_map
    (fun (entry : Lock.entry) ->
      match Lock.find before entry.name with
      | None -> [ Entered entry ]
      | Some was ->
          (if Version.compare was.version entry.version <> 0 then
             [ Moved { name = entry.name; from = was.version; to_ = entry.version } ]
           else [])
          @
          let gained = List.filter (fun held -> not (List.mem held was.holds)) entry.holds in
          if gained <> [] then [ Holds { name = entry.name; gained } ] else [])
    after
  @ List.filter_map
      (fun (entry : Lock.entry) ->
        if Lock.find after entry.name = None then Some (Left entry) else None)
      before

let holds = function [] -> "" | held -> ", which holds " ^ String.concat ", " held

let change_sentence = function
  | Entered entry ->
      Printf.sprintf "`%s` %s enters the build%s." (Path.show_package entry.name)
        (Version.show entry.version) (holds entry.holds)
  | Left entry ->
      Printf.sprintf "`%s` %s leaves the build." (Path.show_package entry.name)
        (Version.show entry.version)
  | Moved { name; from; to_ } ->
      Printf.sprintf "`%s` goes from %s to %s." (Path.show_package name) (Version.show from)
        (Version.show to_)
  | Holds { name; gained } ->
      Printf.sprintf "`%s` would hold %s, which it did not." (Path.show_package name)
        (String.concat ", " gained)

let change_json = function
  | Entered entry ->
      Json.Object
        [
          ("kind", Json.String "entered");
          ("package", Json.String (Path.show_package entry.name));
          ("version", Json.String (Version.show entry.version));
          ("holds", Json.List (List.map (fun held -> Json.String held) entry.holds));
        ]
  | Left entry ->
      Json.Object
        [
          ("kind", Json.String "left");
          ("package", Json.String (Path.show_package entry.name));
          ("version", Json.String (Version.show entry.version));
        ]
  | Moved { name; from; to_ } ->
      Json.Object
        [
          ("kind", Json.String "moved");
          ("package", Json.String (Path.show_package name));
          ("from", Json.String (Version.show from));
          ("to", Json.String (Version.show to_));
        ]
  | Holds { name; gained } ->
      Json.Object
        [
          ("kind", Json.String "holds");
          ("package", Json.String (Path.show_package name));
          ("gained", Json.List (List.map (fun held -> Json.String held) gained));
        ]

(* A signature of a registry package that the project depends on and the
   new versions change. *)
type signature = {
  path : Path.t;
  before : string option;
  after : string option;
  read_by : Path.t list;
}

(* The effect of the new versions on the project's code, computed in a
   trial session with those versions before any file is written: each
   changed signature with its dependents in the project, and the
   diagnostics that the project would have and does not have now. *)
let consequences (project : Project.t) text =
  let trial = Database.trial project.session [ ("truss.lock", Some text) ] in
  let own = List.map snd (Database.packages project.session) in
  let ours path = List.mem (Path.package path) own in
  let changed =
    List.sort_uniq Path.compare
      (List.filter_map
         (fun (path, part, (difference : Database.difference)) ->
           match part with
           | Some part
             when difference = Changed && List.mem part Signatures.parts && not (ours path) ->
               Some path
           | _ -> None)
         (Database.changes trial project.session))
  in
  let readers = lazy (Database.dependencies trial) in
  let signatures =
    List.filter_map
      (fun path ->
        match
          List.sort_uniq Path.compare
            (List.filter_map
               (fun (reader, _, _) -> if ours reader then Some reader else None)
               (Database.readers (Lazy.force readers) path))
        with
        | [] -> None
        | read_by ->
            Some
              {
                path;
                before = Signatures.of_path project.context path;
                after = Signatures.of_path (Database.context trial) path;
                read_by;
              })
      changed
  in
  let diagnostics (session : Database.session) =
    Database.problems session
    @ List.concat_map
        (fun module_ ->
          List.map
            (fun (diagnostic : Diagnostic.t) ->
              Printf.sprintf "%s: %s" (Database.module_file session module_) diagnostic.message)
            (Database.diagnostics session module_))
        (List.concat_map (Database.package_modules session) own)
  in
  let now = diagnostics project.session in
  (signatures, List.filter (fun diagnostic -> not (List.mem diagnostic now)) (diagnostics trial))

let report ~json ~lock ~signatures ~broken =
  if json then
    Json.print
      (Json.document ~diagnostics:[]
         [
           ("changes", Json.List (List.map change_json lock));
           ( "signatures",
             Json.List
               (List.map
                  (fun (changed : signature) ->
                    Json.Object
                      [
                        ("path", Json.String (Path.show changed.path));
                        ("before", Json.option (fun text -> Json.String text) changed.before);
                        ("after", Json.option (fun text -> Json.String text) changed.after);
                        ( "read_by",
                          Json.List
                            (List.map (fun path -> Json.String (Path.show path)) changed.read_by) );
                      ])
                  signatures) );
           ("breaks", Json.List (List.map (fun sentence -> Json.String sentence) broken));
         ])
  else begin
    List.iter (fun change -> Output.print_line (change_sentence change)) lock;
    if signatures <> [] then begin
      Output.print_line "";
      Output.print_line "Signatures the project reads that change:";
      List.iter
        (fun (changed : signature) ->
          Output.printf "  %s\n" (Path.show changed.path);
          Option.iter
            (fun text -> Output.print_line (Signatures.labeled "was:" text))
            changed.before;
          Option.iter (fun text -> Output.print_line (Signatures.labeled "now:" text)) changed.after;
          Output.printf "    read by: %s\n"
            (String.concat ", " (List.map Path.show changed.read_by)))
        signatures
    end;
    if broken <> [] then begin
      Output.print_line "";
      Output.print_line "With these versions the project has errors it does not have now:";
      List.iter (Output.printf "  %s\n") broken
    end
  end

let lock_file (project : Project.t) = Filename.concat (Database.root project.session) "truss.lock"

let run ~directory ~names ~json =
  let project = Project.load directory in
  let set = List.map wanted names in
  match Database.plan_lock project.session ~set ~all:(names = []) with
  | Error message -> Project.cannot_run "%s" message
  | Ok plan ->
      let lock = lock_changes ~before:plan.before ~after:plan.after in
      if lock = [] then begin
        if json then Json.print (Json.document ~diagnostics:[] [ ("changes", Json.List []) ])
        else Output.print_line "Every package is at the version asked for.";
        0
      end
      else begin
        let signatures, broken = consequences project plan.text in
        Project.write_file (lock_file project) plan.text;
        Project.reload project;
        report ~json ~lock ~signatures ~broken;
        if broken = [] then 0 else 1
      end
