module Path_table = Hashtbl.Make (Path)

let read_version text =
  match Registry.Version.parse text with
  | Some version -> version
  | None ->
      Outcome.raise_cannot_run "`%s` is not a version, which is three numbers, such as 1.4.2." text

let parse_wanted text =
  let written, version =
    match String.split_first ~sep:"@" text with
    | Some (written, version) -> (written, Some version)
    | None -> (text, None)
  in
  let name =
    match Manifest.parse_name written with
    | Some ({ owner = Some _; _ } as name) -> name
    | _ ->
        Outcome.raise_cannot_run
          "`%s` is not a registry package's name, which is an owner and a name, such as \
           `acme.geometry`."
          written
  in
  (name, Option.map read_version version)

type change =
  | Entered of Registry.Lock.entry
  | Left of Registry.Lock.entry
  | Moved of { name : Path.package; from : Registry.Version.t; to_ : Registry.Version.t }
  | Holds of { name : Path.package; gained : Grant.capability list }

let lock_changes ~(before : Registry.Lock.t) ~(after : Registry.Lock.t) =
  List.concat_map
    (fun (entry : Registry.Lock.entry) ->
      match Registry.Lock.find before entry.name with
      | None -> [ Entered entry ]
      | Some was ->
          (if Registry.Version.compare was.version entry.version <> 0 then
             [ Moved { name = entry.name; from = was.version; to_ = entry.version } ]
           else [])
          @
          let gained = List.filter (fun held -> not (List.mem held was.holds)) entry.holds in
          if gained <> [] then [ Holds { name = entry.name; gained } ] else [])
    after
  @ List.filter_map
      (fun (entry : Registry.Lock.entry) ->
        if Registry.Lock.find after entry.name = None then Some (Left entry) else None)
      before

let show_capabilities held = String.concat ", " (List.map Grant.show_capability held)
let describe_held = function [] -> "" | held -> ", which holds " ^ show_capabilities held

let describe_change = function
  | Entered entry ->
      Printf.sprintf "`%s` %s enters the build%s." (Path.show_package entry.name)
        (Registry.Version.show entry.version)
        (describe_held entry.holds)
  | Left entry ->
      Printf.sprintf "`%s` %s leaves the build." (Path.show_package entry.name)
        (Registry.Version.show entry.version)
  | Moved { name; from; to_ } ->
      Printf.sprintf "`%s` goes from %s to %s." (Path.show_package name)
        (Registry.Version.show from) (Registry.Version.show to_)
  | Holds { name; gained } ->
      Printf.sprintf "`%s` would hold %s, which it did not." (Path.show_package name)
        (show_capabilities gained)

let encode_capabilities held =
  Json.List (List.map (fun capability -> Json.String (Grant.show_capability capability)) held)

let encode_change = function
  | Entered entry ->
      Json.Object
        [
          ("kind", Json.String "entered");
          ("package", Json.String (Path.show_package entry.name));
          ("version", Json.String (Registry.Version.show entry.version));
          ("holds", encode_capabilities entry.holds);
        ]
  | Left entry ->
      Json.Object
        [
          ("kind", Json.String "left");
          ("package", Json.String (Path.show_package entry.name));
          ("version", Json.String (Registry.Version.show entry.version));
        ]
  | Moved { name; from; to_ } ->
      Json.Object
        [
          ("kind", Json.String "moved");
          ("package", Json.String (Path.show_package name));
          ("from", Json.String (Registry.Version.show from));
          ("to", Json.String (Registry.Version.show to_));
        ]
  | Holds { name; gained } ->
      Json.Object
        [
          ("kind", Json.String "holds");
          ("package", Json.String (Path.show_package name));
          ("gained", encode_capabilities gained);
        ]

type signature = {
  path : Path.t;
  before : string option;
  after : string option;
  dependents : Path.t list;
}

let list_signatures snapshot ~database ~upgraded =
  let project_packages = List.map snd (Workspace.list_packages snapshot) in
  let is_in_project path = List.mem (Path.locate_package path) project_packages in
  let changed =
    List.filter
      (fun (change : Database.change) -> change.is_signature && not (is_in_project change.changed))
      (Database.list_changes database upgraded)
  in
  ignore (Database.prove database (In_packages project_packages));
  let dependents = Path_table.create 16 in
  List.iter
    (fun ({ reader; read; read_kind; _ } : Database.read) ->
      if
        is_in_project reader
        && List.exists
             (fun (change : Database.change) ->
               Path.equal change.changed read && change.kind = read_kind)
             changed
      then
        Path_table.replace dependents read
          (reader :: Option.value (Path_table.find_opt dependents read) ~default:[]))
    (Database.list_dependents database
       (List.sort_uniq Path.compare
          (List.map (fun (change : Database.change) -> change.changed) changed)));
  let find_text database path =
    Signatures.find_signature
      (Database.make_name_lookups database)
      (Database.make_source_lookups database)
      path
  in
  List.sort
    (fun left right -> Path.compare left.path right.path)
    (Path_table.fold
       (fun path readers signatures ->
         {
           path;
           before = find_text database path;
           after = find_text upgraded path;
           dependents = List.sort_uniq Path.compare readers;
         }
         :: signatures)
       dependents [])

let list_new_errors snapshot upgraded_snapshot ~database ~upgraded =
  let project_packages = List.map snd (Workspace.list_packages snapshot) in
  let list_diagnostics (snapshot : Workspace.snapshot) database =
    List.map Project.show_problem (Workspace.problems snapshot)
    @ List.concat_map
        (fun file ->
          List.map
            (fun (diagnostic : Diagnostic.t) ->
              Printf.sprintf "%s: %s" (Workspace.locate_file snapshot file) diagnostic.message)
            (Database.list_file_diagnostics database file))
        (List.concat_map (Workspace.list_package_files snapshot) project_packages)
  in
  let now = list_diagnostics snapshot database in
  List.filter
    (fun diagnostic -> not (List.mem diagnostic now))
    (list_diagnostics upgraded_snapshot upgraded)

let encode_signature (changed : signature) =
  Json.Object
    [
      ("path", Json.String (Path.show changed.path));
      ("before", Json.encode_option (fun text -> Json.String text) changed.before);
      ("after", Json.encode_option (fun text -> Json.String text) changed.after);
      ("read_by", Json.List (List.map (fun path -> Json.String (Path.show path)) changed.dependents));
    ]

let print_signature (changed : signature) =
  Output.printf "  %s\n" (Path.show changed.path);
  Option.iter
    (fun text -> Output.print_line (Signatures.label_signature "was:" text))
    changed.before;
  Option.iter (fun text -> Output.print_line (Signatures.label_signature "now:" text)) changed.after;
  Output.printf "    read by: %s\n" (String.concat ", " (List.map Path.show changed.dependents))

let report ~lock ~signatures ~broken =
  if Output.json () then
    Json.print
      (Json.make_document ~diagnostics:[]
         [
           ("changes", Json.List (List.map encode_change lock));
           ("signatures", Json.List (List.map encode_signature signatures));
           ("breaks", Json.List (List.map (fun sentence -> Json.String sentence) broken));
         ])
  else begin
    List.iter (fun change -> Output.print_line (describe_change change)) lock;
    if signatures <> [] then begin
      Output.print_line "";
      Output.print_line "Signatures the project reads that change:";
      List.iter print_signature signatures
    end;
    if broken <> [] then begin
      Output.print_line "";
      Output.print_line "With these versions the project has errors it does not have now:";
      List.iter (Output.printf "  %s\n") broken
    end
  end

let lock_file snapshot = Filename.concat (Workspace.locate_root snapshot) "truss.lock"

let run ~names =
  let snapshot, _ = Command_packages.load_current () in
  let set = List.map parse_wanted names in
  match Workspace.plan_lock snapshot ~set ~all:(names = []) with
  | Error message -> Outcome.raise_cannot_run "%s" message
  | Ok plan ->
      let lock = lock_changes ~before:plan.before ~after:plan.after in
      if lock = [] then begin
        if Output.json () then
          Json.print (Json.make_document ~diagnostics:[] [ ("changes", Json.List []) ])
        else Output.print_line "Every package is at the version asked for.";
        0
      end
      else begin
        let upgraded_snapshot =
          Workspace.make_overlay snapshot [ (Project.lock_file, Some plan.text) ]
        in
        let database = Database.copy (Workspace.open_database snapshot) in
        let signatures, broken =
          Fun.protect
            ~finally:(fun () -> Database.close_uncommitted database)
            (fun () ->
              let upgraded = Workspace.open_database upgraded_snapshot in
              ( list_signatures snapshot ~database ~upgraded,
                list_new_errors snapshot upgraded_snapshot ~database ~upgraded ))
        in
        Command_packages.write_file (lock_file snapshot) plan.text;
        report ~lock ~signatures ~broken;
        if broken = [] then 0 else 1
      end
