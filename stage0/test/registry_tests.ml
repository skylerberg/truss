let () =
  Harness.test "a version is three numbers" (fun () ->
      if Registry.Version.parse "1.4.2" <> Some (1, 4, 2) then Harness.fail "1.4.2 is not read";
      List.iter
        (fun text -> if Registry.Version.parse text <> None then Harness.fail "%s is read" text)
        [ "1.4"; "1.4.2.0"; "1.x.2"; ""; "1..2"; "-1.0.0" ]);
  Harness.test "versions compare by their numbers, not as text" (fun () ->
      if Registry.Version.compare (1, 10, 0) (1, 9, 0) <= 0 then
        Harness.fail "1.10.0 is not after 1.9.0");
  Harness.test "a package's versions start with the number at the end of its name, or 1" (fun () ->
      List.iter
        (fun (name, major) ->
          let actual = Registry.Version.parse_major name in
          if actual <> major then Harness.fail "%s gives %d" (Path.show_package name) actual)
        [
          ({ owner = Some "acme"; name = "geometry" }, 1);
          ({ owner = Some "acme"; name = "geometry_v2" }, 2);
          ({ owner = Some "acme"; name = "geometry_v17" }, 17);
          ({ owner = Some "acme"; name = "v2" }, 1);
          ({ owner = Some "acme"; name = "move" }, 1);
          ({ owner = Some "acme"; name = "geometry_v" }, 1);
        ])

let () =
  Harness.test "a package's hash does not depend on the order its files are given in" (fun () ->
      let files = [ ("truss.toml", "a"); ("vector.truss", "b"); ("guide/start.md", "c") ] in
      if Registry.Content.hash files <> Registry.Content.hash (List.rev files) then
        Harness.fail "the hashes differ";
      if not (Registry.Content.is_hash (Registry.Content.hash files)) then
        Harness.fail "not 64 hexadecimal digits");
  Harness.test "a package's hash is the BLAKE3 hash of a line for each file, as PACKAGES.md defines"
    (fun () ->
      let make_line path bytes = path ^ " " ^ Blake3.hash_to_hex bytes ^ "\n" in
      let expected = Blake3.hash_to_hex (make_line "a.truss" "one" ^ make_line "b/c.truss" "two") in
      if Registry.Content.hash [ ("b/c.truss", "two"); ("a.truss", "one") ] <> expected then
        Harness.fail "another hash");
  Harness.test "a package's hash changes with a file's bytes, and with its path" (fun () ->
      let hash = Registry.Content.hash [ ("a.truss", "one"); ("b.truss", "two") ] in
      if hash = Registry.Content.hash [ ("a.truss", "one"); ("b.truss", "too") ] then
        Harness.fail "bytes";
      if hash = Registry.Content.hash [ ("a.truss", "one"); ("c.truss", "two") ] then
        Harness.fail "path";
      if hash = Registry.Content.hash [ ("a.truss", "onetwo") ] then Harness.fail "one file for two")

let lock_block () =
  String.concat "\n"
    (Documents.list_block_after
       (File_system.read (Harness.make_workspace_path "PACKAGES.md"))
       "## The lock file")
  ^ "\n"

let () =
  Harness.test "PACKAGES.md's lock file is read, and is written back as it is" (fun () ->
      let text = lock_block () in
      match Registry.Lock.parse text with
      | [
          {
            name = { Path.owner = Some "acme"; name = "geometry_v2" };
            version = 2, 1, 3;
            holds = [];
            _;
          };
          {
            name = { Path.owner = Some "truss"; name = "postgres" };
            version = 1, 12, 0;
            holds = [ Prelude "Clock"; Prelude "Handles"; Prelude "NetworkClient" ];
            _;
          };
        ] as entries ->
          if Registry.Lock.print entries <> text then
            Harness.fail "written as %S" (Registry.Lock.print entries)
      | _ -> Harness.fail "read differently");
  Harness.test "a lock file with nothing in it has no package" (fun () ->
      if Registry.Lock.parse "" <> [] || Registry.Lock.parse "format 1\n" <> [] then
        Harness.fail "has one");
  let hash = String.make 64 'a' in
  let expect_malformed_at line text =
    match Registry.Lock.parse text with
    | exception Registry.Lock.Malformed { line = actual; _ } when actual = line -> ()
    | exception Registry.Lock.Malformed { line = actual; problem } ->
        let message = Project_catalog.describe_lock_problem problem in
        Harness.fail "at line %d: %s" actual message
    | _ -> Harness.fail "accepted"
  in
  Harness.test "a lock file without its first line is malformed" (fun () ->
      expect_malformed_at 1 (Printf.sprintf "acme.geometry 1.0.0 %s\n" hash));
  Harness.test "a line that is not a name, a version, and a hash is malformed, at its line"
    (fun () ->
      expect_malformed_at 2 "format 1\nacme.geometry 1.0.0\n";
      expect_malformed_at 2 (Printf.sprintf "format 1\ngeometry 1.0.0 %s\n" hash);
      expect_malformed_at 2 (Printf.sprintf "format 1\nacme.geometry 1.0 %s\n" hash);
      expect_malformed_at 2 "format 1\nacme.geometry 1.0.0 abc\n";
      expect_malformed_at 3
        (Printf.sprintf "format 1\nacme.geometry 1.0.0 %s\nacme.geometry 1.1.0 %s\n" hash hash));
  Harness.test "a prelude capability that a lock file holds by its full path is written by its name"
    (fun () ->
      let line = Printf.sprintf "acme.geometry 1.0.0 %s holds" hash in
      let written =
        Registry.Lock.print
          (Registry.Lock.parse
             (Printf.sprintf "format 1\n%s standard.capabilities.Clock, Handles\n" line))
      in
      if written <> Printf.sprintf "format 1\n%s Clock, Handles\n" line then
        Harness.fail "written as %S" written);
  Harness.test "a capability that a lock file holds is a name or a full path" (fun () ->
      expect_malformed_at 2 (Printf.sprintf "format 1\nacme.geometry 1.0.0 %s holds a:b\n" hash);
      expect_malformed_at 2 (Printf.sprintf "format 1\nacme.geometry 1.0.0 %s holds Clock,\n" hash));
  Harness.test "a lock file's lines are in order of owner, and then of name" (fun () ->
      let first = Printf.sprintf "a.y 1.0.0 %s\n" hash
      and second = Printf.sprintf "a1.x 1.0.0 %s\n" hash in
      let written = Registry.Lock.print (Registry.Lock.parse ("format 1\n" ^ second ^ first)) in
      if written <> "format 1\n" ^ first ^ second then Harness.fail "written as %S" written);
  Harness.test "a version must start with the number its package's name ends in" (fun () ->
      expect_malformed_at 2 (Printf.sprintf "format 1\nacme.geometry_v2 1.0.0 %s\n" hash);
      expect_malformed_at 2 (Printf.sprintf "format 1\nacme.geometry 2.0.0 %s\n" hash))

let make_scratch_directory = Harness.make_scratch_directory

let use_registry_at root =
  Unix.putenv Registry.Index.variable root;
  Option.get (Registry.Index.find_current_registry ())

let make_version_directory root (package : Path.package) version =
  List.fold_left Filename.concat root
    (Path.list_package_parts package @ [ Registry.Version.show version ])

let () =
  let files = [ ("truss.toml", "[package]\nname = \"acme.geometry\"\n"); ("vector.truss", "") ] in
  Harness.test "a registry lists a package's versions in the order they were added" (fun () ->
      let registry = use_registry_at (make_scratch_directory "registry") in
      Registry.Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      Registry.Index.add registry
        { Path.owner = Some "acme"; name = "geometry" }
        (1, 1, 0) (("angle.truss", "") :: files);
      (match
         Registry.Index.list_versions registry { Path.owner = Some "acme"; name = "geometry" }
       with
      | [ ((1, 0, 0), first); ((1, 1, 0), second) ] ->
          if first <> Registry.Content.hash files || first = second then
            Harness.fail "the hashes are wrong"
      | _ -> Harness.fail "listed differently");
      if
        Option.map fst
          (Registry.Index.find_newest registry { Path.owner = Some "acme"; name = "geometry" })
        <> Some (1, 1, 0)
      then Harness.fail "the newest is not 1.1.0";
      if Registry.Index.list_versions registry { Path.owner = Some "acme"; name = "nothing" } <> []
      then Harness.fail "a package it does not hold");
  Harness.test "a version is fetched into a directory named by its hash, with every file" (fun () ->
      let registry = use_registry_at (make_scratch_directory "registry")
      and into = make_scratch_directory "packages" in
      Registry.Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      let hash = Registry.Content.hash files in
      match
        Registry.Index.fetch registry ~into
          { Path.owner = Some "acme"; name = "geometry" }
          (1, 0, 0) ~hash
      with
      | Ok directory ->
          if Filename.basename directory <> hash then Harness.fail "in %s" directory;
          if Registry.Content.hash (Registry.Content.list_all_files directory) <> hash then
            Harness.fail "other files"
      | Error reason -> Harness.fail "%s" reason);
  Harness.test "files that do not have the hash asked for are not kept" (fun () ->
      let root = make_scratch_directory "registry" and into = make_scratch_directory "packages" in
      let registry = use_registry_at root in
      Registry.Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      let hash = Registry.Content.hash files in
      let changed =
        Filename.concat
          (make_version_directory root { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0))
          "vector.truss"
      in
      Out_channel.with_open_bin changed (fun channel -> output_string channel "fn extra() {}\n");
      (match
         Registry.Index.fetch registry ~into
           { Path.owner = Some "acme"; name = "geometry" }
           (1, 0, 0) ~hash
       with
      | Error reason ->
          if not (String.includes ~affix:"do not have the hash" reason) then
            Harness.fail "said %s" reason
      | Ok _ -> Harness.fail "kept");
      if Sys.readdir into <> [||] then Harness.fail "left files behind");
  Harness.test "a version the registry does not hold is not fetched" (fun () ->
      let registry = use_registry_at (make_scratch_directory "registry")
      and into = make_scratch_directory "packages" in
      match
        Registry.Index.fetch registry ~into
          { Path.owner = Some "acme"; name = "geometry" }
          (1, 0, 0) ~hash:(String.make 64 'b')
      with
      | Error _ -> ()
      | Ok _ -> Harness.fail "fetched")

let parse_package text = Option.get (Path.parse_package text)

let hash_of name (version : Registry.Version.t) =
  Registry.Content.hash [ (name, Registry.Version.show version) ]

let load published name version ~hash =
  let written = Path.show_package name in
  match List.assoc_opt (written, version) published with
  | Some (dependencies, record) when hash = hash_of written version ->
      Ok
        ( ({
             name;
             truss = Some "0.1";
             dependencies =
               List.map
                 (fun (name, capabilities) ->
                   { Manifest.package = parse_package name; capabilities })
                 dependencies;
           }
            : Manifest.package),
          List.map
            (fun (name, version) ->
              {
                Registry.Lock.name = parse_package name;
                version;
                hash = hash_of name version;
                holds = [];
              })
            record )
  | _ -> Error (Project_catalog.Unavailable "it is not there")

let make_entry name version =
  { Registry.Lock.name = parse_package name; version; hash = hash_of name version; holds = [] }

let list_chosen (packages, problems) =
  if problems <> [] then
    Harness.fail "problems: %s"
      (String.concat " " (List.map Project_catalog.describe_selection_problem problems));
  List.map
    (fun (actual : Registry.Selection.package) -> (Path.show_package actual.name, actual.version))
    packages

let () =
  let published =
    [
      (("acme.geometry", (1, 0, 0)), ([ ("acme.units", []) ], [ ("acme.units", (1, 0, 0)) ]));
      (("acme.geometry", (1, 1, 0)), ([ ("acme.units", []) ], [ ("acme.units", (1, 2, 0)) ]));
      (("acme.shapes", (1, 0, 0)), ([ ("acme.units", []) ], [ ("acme.units", (1, 1, 0)) ]));
      (("acme.units", (1, 0, 0)), ([], []));
      (("acme.units", (1, 1, 0)), ([], []));
      (("acme.units", (1, 2, 0)), ([], []));
      (("acme.units", (1, 3, 0)), ([], []));
    ]
  in
  let choose lock roots =
    Registry.Selection.choose ~lock
      ~roots:(List.map (fun name -> (parse_package "app", parse_package name)) roots)
      ~is_local:(fun name -> name = parse_package "app" || name = parse_package "acme.local")
      ~load:(load published)
  in
  Harness.test "a build uses the version its lock file names, and nothing newer" (fun () ->
      if
        list_chosen (choose [ make_entry "acme.units" (1, 1, 0) ] [ "acme.units" ])
        <> [ ("acme.units", (1, 1, 0)) ]
      then Harness.fail "chose another");
  Harness.test "a build uses the highest version any of its packages was published with" (fun () ->
      let lock = [ make_entry "acme.geometry" (1, 0, 0); make_entry "acme.shapes" (1, 0, 0) ] in
      if
        list_chosen (choose lock [ "acme.geometry"; "acme.shapes" ])
        <> [ ("acme.geometry", (1, 0, 0)); ("acme.shapes", (1, 0, 0)); ("acme.units", (1, 1, 0)) ]
      then Harness.fail "chose another");
  Harness.test "a version the lock file names above every record's is kept" (fun () ->
      let lock = [ make_entry "acme.geometry" (1, 0, 0); make_entry "acme.units" (1, 3, 0) ] in
      if
        list_chosen (choose lock [ "acme.geometry" ])
        <> [ ("acme.geometry", (1, 0, 0)); ("acme.units", (1, 3, 0)) ]
      then Harness.fail "chose another");
  Harness.test "a package no dependency reaches is not in the build, whatever the lock file names"
    (fun () ->
      let lock = [ make_entry "acme.units" (1, 0, 0); make_entry "acme.shapes" (1, 0, 0) ] in
      if list_chosen (choose lock [ "acme.units" ]) <> [ ("acme.units", (1, 0, 0)) ] then
        Harness.fail "chose another");
  Harness.test "a dependency that nothing gives a version is a problem that names who wants it"
    (fun () ->
      match choose [] [ "acme.units" ] with
      | ( _,
          [
            No_version
              {
                name = { Path.owner = Some "acme"; name = "units" };
                wanted_by = { Path.owner = None; name = "app" };
              };
          ] ) ->
          ()
      | _ -> Harness.fail "not reported");
  Harness.test "a version whose files cannot be had is a problem" (fun () ->
      match choose [ make_entry "acme.units" (1, 9, 0) ] [ "acme.units" ] with
      | ( _,
          [
            Cannot_load
              { name = { Path.owner = Some "acme"; name = "units" }; version = 1, 9, 0; _ };
          ] ) ->
          ()
      | _ -> Harness.fail "not reported");
  Harness.test "a record that names a version under another hash than the build's is a problem"
    (fun () ->
      let lock =
        [
          make_entry "acme.geometry" (1, 0, 0);
          { (make_entry "acme.units" (1, 0, 0)) with hash = "other" };
        ]
      in
      match choose lock [ "acme.geometry" ] with
      | _, problems ->
          if
            not
              (List.exists
                 (function
                   | Registry.Selection.Two_contents
                       { name = { Path.owner = Some "acme"; name = "units" }; _ } ->
                       true
                   | _ -> false)
                 problems)
          then Harness.fail "not reported");
  Harness.test "a project's package is used whatever the registry has by its name" (fun () ->
      let published =
        (("acme.walls", (1, 0, 0)), ([ ("acme.local", []) ], [ ("acme.local", (1, 0, 0)) ]))
        :: published
      in
      let packages =
        Registry.Selection.choose
          ~lock:[ make_entry "acme.walls" (1, 0, 0) ]
          ~roots:
            [
              ({ Path.owner = None; name = "app" }, { Path.owner = Some "acme"; name = "walls" });
              ({ Path.owner = None; name = "app" }, { Path.owner = Some "acme"; name = "local" });
            ]
          ~is_local:(fun name -> name = { Path.owner = Some "acme"; name = "local" })
          ~load:(load published)
      in
      if list_chosen packages <> [ ("acme.walls", (1, 0, 0)) ] then Harness.fail "chose another")

let () =
  let make_package name dependencies : Registry.Selection.package =
    {
      name;
      version = (1, 0, 0);
      hash = hash_of (Path.show_package name) (1, 0, 0);
      manifest =
        {
          name;
          truss = Some "0.1";
          dependencies =
            List.map
              (fun (package, capabilities) -> { Manifest.package; capabilities })
              dependencies;
        };
      record = [];
    }
  in
  let make_grant package capabilities = { Manifest.package; capabilities } in
  Harness.test "a package holds the capabilities the project grants it" (fun () ->
      let held =
        Registry.Selection.For_testing.list_holds
          ~project:
            [
              make_grant
                { Path.owner = Some "truss"; name = "http" }
                [ Prelude "NetworkClient"; Prelude "Clock" ];
            ]
          [ make_package { Path.owner = Some "truss"; name = "http" } [] ]
      in
      if
        held
        <> [
             ( { Path.owner = Some "truss"; name = "http" },
               [ Prelude "Clock"; Prelude "NetworkClient" ] );
           ]
      then Harness.fail "holds another");
  Harness.test "a package holds only the granted capabilities that its user holds itself" (fun () ->
      let held =
        Registry.Selection.For_testing.list_holds
          ~project:
            [ make_grant { Path.owner = Some "truss"; name = "http" } [ Prelude "NetworkClient" ] ]
          [
            make_package
              { Path.owner = Some "truss"; name = "http" }
              [
                ( { Path.owner = Some "truss"; name = "tls" },
                  [ Prelude "NetworkClient"; Prelude "Clock" ] );
              ];
            make_package { Path.owner = Some "truss"; name = "tls" } [];
          ]
      in
      if List.assoc { Path.owner = Some "truss"; name = "tls" } held <> [ Prelude "NetworkClient" ]
      then
        Harness.fail "holds [%s]"
          (String.concat "; "
             (List.map Grant.show_capability
                (List.assoc { Path.owner = Some "truss"; name = "tls" } held))));
  Harness.test "a package holds every capability any of its users grants it" (fun () ->
      let held =
        Registry.Selection.For_testing.list_holds
          ~project:
            [
              make_grant { Path.owner = Some "truss"; name = "http" } [ Prelude "NetworkClient" ];
              make_grant { Path.owner = Some "truss"; name = "tls" } [ Prelude "Random" ];
            ]
          [
            make_package
              { Path.owner = Some "truss"; name = "http" }
              [ ({ Path.owner = Some "truss"; name = "tls" }, [ Prelude "NetworkClient" ]) ];
            make_package { Path.owner = Some "truss"; name = "tls" } [];
          ]
      in
      if
        List.assoc { Path.owner = Some "truss"; name = "tls" } held
        <> [ Prelude "NetworkClient"; Prelude "Random" ]
      then Harness.fail "holds another");
  Harness.test
    "a package holds a capability that its user holds, whether each manifest writes it by its name \
     or by its full path" (fun () ->
      let read_dependencies text =
        match Manifest.parse text with
        | { package = Some package; _ } -> package.dependencies
        | { package = None; _ } -> failwith "the manifest has no package"
      in
      let http = { Path.owner = Some "truss"; name = "http" }
      and tls = { Path.owner = Some "truss"; name = "tls" } in
      let http_package = make_package http [] in
      let lock =
        Registry.Lock.print
          (Registry.Selection.lock
             ~project:
               (read_dependencies
                  "[package]\nname = \"app\"\n[dependencies]\n\"truss.http\" = [\"Clock\"]\n")
             [
               {
                 http_package with
                 manifest =
                   {
                     http_package.manifest with
                     dependencies =
                       read_dependencies
                         "[package]\n\
                          name = \"truss.http\"\n\
                          [dependencies]\n\
                          \"truss.tls\" = [\"standard.capabilities.Clock\"]\n";
                   };
               };
               make_package tls [];
             ])
      in
      match String.split_on_char '\n' lock with
      | [ "format 1"; http_line; tls_line; "" ]
        when String.ends_with ~suffix:" holds Clock" http_line
             && String.ends_with ~suffix:" holds Clock" tls_line ->
          ()
      | _ -> Harness.fail "locked as %S" lock);
  Harness.test "where a lock file differs from the one a build gives is told for each package"
    (fun () ->
      let written =
        [
          make_entry "acme.units" (1, 0, 0);
          { (make_entry "truss.http" (1, 0, 0)) with holds = [ Prelude "Clock" ] };
        ]
      and current = [ make_entry "acme.geometry" (1, 0, 0); make_entry "truss.http" (1, 0, 0) ] in
      let actual =
        String.concat " "
          (List.map Project_catalog.describe_difference
             (Registry.Selection.list_differences ~written ~current))
      in
      List.iter
        (fun part ->
          if not (String.includes ~affix:part actual) then
            Harness.fail "%s is not in: %s" part actual)
        [
          "`acme.geometry` 1.0.0 is in the build and has no line";
          "Nothing in the build uses `acme.units`";
          "`truss.http` is said to hold Clock, and the manifests grant it nothing";
        ])
