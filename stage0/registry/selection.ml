type package = {
  name : Path.package;
  version : Version.t;
  hash : string;
  manifest : Manifest.package;
  record : Lock.t;
}

type problem =
  | No_version of { name : Path.package; wanted_by : Path.package }
  | Cannot_load of { name : Path.package; version : Version.t; reason : string }
  | Two_contents of { name : Path.package; version : Version.t; recorded_by : Path.package }

let sentence problem =
  let show = Path.show_package in
  match problem with
  | No_version { name; wanted_by } ->
      Printf.sprintf
        "`%s` depends on `%s`, which is not a package of this project and has no line in \
         `truss.lock`. Run `truss add %s`."
        (show wanted_by) (show name) (show name)
  | Cannot_load { name; version; reason } ->
      Printf.sprintf "`truss.lock` names `%s` %s, whose files are not in the store, and %s."
        (show name) (Version.show version) reason
  | Two_contents { name; version; recorded_by } ->
      Printf.sprintf
        "`%s` was published with `%s` %s under another hash than the build has for it. One version \
         has one content, so one of the two is wrong."
        (show recorded_by) (show name) (Version.show version)

let choose ~lock ~roots ~local ~load =
  let chosen = Hashtbl.create 16 in
  List.iter
    (fun (entry : Lock.entry) -> Hashtbl.replace chosen entry.name (entry.version, entry.hash))
    lock;
  let rec pass () =
    let seen = Hashtbl.create 16 in
    let changed = ref false and found = ref [] and problems = ref [] in
    let problem found = if not (List.mem found !problems) then problems := found :: !problems in
    let record_of ~recorded_by (entry : Lock.entry) =
      match Hashtbl.find_opt chosen entry.name with
      | Some (version, _) when Version.compare version entry.version > 0 -> ()
      | Some (version, hash) when Version.compare version entry.version = 0 ->
          if hash <> entry.hash then
            problem (Two_contents { name = entry.name; version; recorded_by })
      | _ ->
          Hashtbl.replace chosen entry.name (entry.version, entry.hash);
          changed := true
    in
    let rec visit wanted_by name =
      if not (local name || Hashtbl.mem seen name) then begin
        Hashtbl.replace seen name ();
        match Hashtbl.find_opt chosen name with
        | None -> problem (No_version { name; wanted_by })
        | Some (version, hash) -> (
            match load name version ~hash with
            | Error reason -> problem (Cannot_load { name; version; reason })
            | Ok ((manifest : Manifest.package), record) ->
                found := { name; version; hash; manifest; record } :: !found;
                List.iter (record_of ~recorded_by:name) record;
                (* A dependency that a package's record does not name is one
                   only its tests use, which a build that uses the package
                   does not take on. *)
                List.iter
                  (fun (dependency : Manifest.dependency) ->
                    if Lock.find record dependency.package <> None then
                      visit name dependency.package)
                  manifest.dependencies)
      end
    in
    List.iter (fun (wanted_by, name) -> visit wanted_by name) roots;
    (* A version that a record raised may have another record, so the walk
       is made again until none is raised. Versions only rise, so it ends. *)
    if !changed then pass ()
    else
      ( List.sort (fun left right -> Path.compare_package left.name right.name) !found,
        List.rev !problems )
  in
  pass ()

let holds ~project packages =
  let held = Hashtbl.create 16 in
  let of_ name = Option.value ~default:[] (Hashtbl.find_opt held name) in
  let in_build name = List.exists (fun package -> package.name = name) packages in
  let grant ~holder (dependency : Manifest.dependency) =
    in_build dependency.package
    &&
    let given =
      match holder with
      | None -> dependency.capabilities
      | Some holder ->
          List.filter (fun capability -> List.mem capability (of_ holder)) dependency.capabilities
    in
    let now = List.sort_uniq String.compare (given @ of_ dependency.package) in
    now <> of_ dependency.package
    && begin
      Hashtbl.replace held dependency.package now;
      true
    end
  in
  let rec settle () =
    let changed =
      List.fold_left
        (fun changed dependency -> grant ~holder:None dependency || changed)
        false project
    in
    let changed =
      List.fold_left
        (fun changed package ->
          List.fold_left
            (fun changed dependency -> grant ~holder:(Some package.name) dependency || changed)
            changed package.manifest.dependencies)
        changed packages
    in
    if changed then settle ()
  in
  settle ();
  List.map (fun package -> (package.name, of_ package.name)) packages

let lock ~project packages : Lock.t =
  let held = holds ~project packages in
  List.map
    (fun package ->
      {
        Lock.name = package.name;
        version = package.version;
        hash = package.hash;
        holds = Option.value ~default:[] (List.assoc_opt package.name held);
      })
    packages

let differences ~(written : Lock.t) ~(current : Lock.t) =
  let capabilities = function [] -> "nothing" | held -> String.concat ", " held in
  List.filter_map
    (fun (entry : Lock.entry) ->
      match Lock.find written entry.name with
      | None ->
          Some
            (Printf.sprintf "`%s` %s is in the build and has no line."
               (Path.show_package entry.name) (Version.show entry.version))
      | Some line when Version.compare line.version entry.version <> 0 ->
          Some
            (Printf.sprintf "`%s` is %s, and a package of the build was published with %s."
               (Path.show_package entry.name) (Version.show line.version)
               (Version.show entry.version))
      | Some line when line.hash <> entry.hash ->
          Some
            (Printf.sprintf "`%s` %s has another hash." (Path.show_package entry.name)
               (Version.show entry.version))
      | Some line when List.sort String.compare line.holds <> entry.holds ->
          Some
            (Printf.sprintf "`%s` is said to hold %s, and the manifests grant it %s."
               (Path.show_package entry.name) (capabilities line.holds) (capabilities entry.holds))
      | Some _ -> None)
    current
  @ List.filter_map
      (fun (line : Lock.entry) ->
        if Lock.find current line.name = None then
          Some (Printf.sprintf "Nothing in the build uses `%s`." (Path.show_package line.name))
        else None)
      written
