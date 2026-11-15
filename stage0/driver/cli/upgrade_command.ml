module Lock = Registry.Lock
module Version = Registry.Version

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
        Outcome.cannot_run
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
            Outcome.cannot_run "`%s` is not a version, which is three numbers, such as 1.4.2."
              version)
      version )

type change =
  | Entered of Lock.entry
  | Left of Lock.entry
  | Moved of { name : Path.package; from : Version.t; to_ : Version.t }
  | Holds of { name : Path.package; gained : string list }

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

let new_errors snapshot text =
  let trial = Database.trial snapshot [ ("truss.lock", Some text) ] in
  let own = List.map snd (Database.packages snapshot) in
  let diagnostics (snapshot : Database.snapshot) =
    let pipeline = Database.pipeline snapshot in
    Pipeline.check pipeline own;
    List.map Project.show_problem (Database.problems snapshot)
    @ List.concat_map
        (fun file ->
          List.map
            (fun (diagnostic : Diagnostic.t) ->
              Printf.sprintf "%s: %s" (Database.file_path snapshot file) diagnostic.message)
            (Pipeline.file_diagnostics pipeline file))
        (List.concat_map (Database.package_files snapshot) own)
  in
  let now = diagnostics snapshot in
  List.filter (fun diagnostic -> not (List.mem diagnostic now)) (diagnostics trial)

let report ~lock ~broken =
  if Output.json () then
    Json.print
      (Json.document ~diagnostics:[]
         [
           ("changes", Json.List (List.map change_json lock));
           ("breaks", Json.List (List.map (fun sentence -> Json.String sentence) broken));
         ])
  else begin
    List.iter (fun change -> Output.print_line (change_sentence change)) lock;
    if broken <> [] then begin
      Output.print_line "";
      Output.print_line "With these versions the project has errors it does not have now:";
      List.iter (Output.printf "  %s\n") broken
    end
  end

let lock_file snapshot = Filename.concat (Database.root snapshot) "truss.lock"

let run ~names =
  let snapshot, _ = Command_packages.current () in
  let set = List.map wanted names in
  match Database.plan_lock snapshot ~set ~all:(names = []) with
  | Error message -> Outcome.cannot_run "%s" message
  | Ok plan ->
      let lock = lock_changes ~before:plan.before ~after:plan.after in
      if lock = [] then begin
        if Output.json () then
          Json.print (Json.document ~diagnostics:[] [ ("changes", Json.List []) ])
        else Output.print_line "Every package is at the version asked for.";
        0
      end
      else begin
        let broken = new_errors snapshot plan.text in
        Command_packages.write_file (lock_file snapshot) plan.text;
        report ~lock ~broken;
        if broken = [] then 0 else 1
      end
