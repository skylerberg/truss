module Path_table = Hashtbl.Make (Path)

let parse_wanted text =
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
        Outcome.raise_cannot_run
          "`%s` is not a registry package's name, which is an owner and a name, such as \
           `acme::geometry`."
          written
  in
  ( name,
    Option.map
      (fun version ->
        match Registry.Version.parse version with
        | Some version -> version
        | None ->
            Outcome.raise_cannot_run "`%s` is not a version, which is three numbers, such as 1.4.2."
              version)
      version )

type change =
  | Entered of Registry.Lock.entry
  | Left of Registry.Lock.entry
  | Moved of { name : Path.package; from : Registry.Version.t; to_ : Registry.Version.t }
  | Holds of { name : Path.package; gained : string list }

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

let holds = function [] -> "" | held -> ", which holds " ^ String.concat ", " held

let describe_change = function
  | Entered entry ->
      Printf.sprintf "`%s` %s enters the build%s." (Path.show_package entry.name)
        (Registry.Version.show entry.version)
        (holds entry.holds)
  | Left entry ->
      Printf.sprintf "`%s` %s leaves the build." (Path.show_package entry.name)
        (Registry.Version.show entry.version)
  | Moved { name; from; to_ } ->
      Printf.sprintf "`%s` goes from %s to %s." (Path.show_package name)
        (Registry.Version.show from) (Registry.Version.show to_)
  | Holds { name; gained } ->
      Printf.sprintf "`%s` would hold %s, which it did not." (Path.show_package name)
        (String.concat ", " gained)

let encode_change = function
  | Entered entry ->
      Json.Object
        [
          ("kind", Json.String "entered");
          ("package", Json.String (Path.show_package entry.name));
          ("version", Json.String (Registry.Version.show entry.version));
          ("holds", Json.List (List.map (fun held -> Json.String held) entry.holds));
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
          ("gained", Json.List (List.map (fun held -> Json.String held) gained));
        ]

type signature = {
  path : Path.t;
  before : string option;
  after : string option;
  dependents : Path.t list;
}

let list_signatures snapshot trial =
  let database = Workspace.open_database snapshot and upgraded = Workspace.open_database trial in
  let own = List.map snd (Workspace.list_packages snapshot) in
  let is_own path = List.mem (Path.locate_package path) own in
  let changed =
    List.filter
      (fun part ->
        Signatures.is_signature part
        &&
        match Database.Part.find_definition part with
        | Some path -> not (is_own path)
        | None -> false)
      (Database.list_changes database upgraded)
  in
  let dependents = Path_table.create 16 in
  List.iter
    (fun ({ dependent; dependency } : Database.read) ->
      match (Database.Part.find_definition dependent, Database.Part.find_definition dependency) with
      | Some reader, Some path when is_own reader && List.mem dependency changed ->
          Path_table.replace dependents path
            (reader :: Option.value (Path_table.find_opt dependents path) ~default:[])
      | _ -> ())
    (Database.list_dependents database
       (List.sort_uniq Path.compare (List.filter_map Database.Part.find_definition changed)));
  let text database path =
    Signatures.find_signature
      (Database.make_name_lookups database [ Path.locate_package path ])
      path
  in
  List.sort
    (fun left right -> Path.compare left.path right.path)
    (Path_table.fold
       (fun path readers signatures ->
         {
           path;
           before = text database path;
           after = text upgraded path;
           dependents = List.sort_uniq Path.compare readers;
         }
         :: signatures)
       dependents [])

let new_errors snapshot trial =
  let own = List.map snd (Workspace.list_packages snapshot) in
  let diagnostics (snapshot : Workspace.snapshot) =
    let database = Workspace.open_database snapshot in
    Database.check database own;
    List.map Project.show_problem (Workspace.problems snapshot)
    @ List.concat_map
        (fun file ->
          List.map
            (fun (diagnostic : Diagnostic.t) ->
              Printf.sprintf "%s: %s" (Workspace.locate_file snapshot file) diagnostic.message)
            (Database.list_file_diagnostics database file))
        (List.concat_map (Workspace.list_package_files snapshot) own)
  in
  let now = diagnostics snapshot in
  List.filter (fun diagnostic -> not (List.mem diagnostic now)) (diagnostics trial)

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
        let trial = Workspace.make_trial snapshot [ (Project.lock_file, Some plan.text) ] in
        let signatures = list_signatures snapshot trial in
        let broken = new_errors snapshot trial in
        Command_packages.write_file (lock_file snapshot) plan.text;
        report ~lock ~signatures ~broken;
        if broken = [] then 0 else 1
      end
