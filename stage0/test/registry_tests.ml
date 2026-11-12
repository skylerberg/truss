(* The tests of versions, a package's hash, the lock file, a registry's
   files, and choosing a build's versions. *)

open Harness
module Version = Registry.Version
module Content = Registry.Content
module Lock = Registry.Lock
module Index = Registry.Index
module Selection = Registry.Selection

let contains text part = Substring.contains text part

(* Versions *)

let () =
  test "a version is three numbers" (fun () ->
      if Version.parse "1.4.2" <> Some (1, 4, 2) then fail "1.4.2 is not read";
      List.iter
        (fun text -> if Version.parse text <> None then fail "%s is read" text)
        [ "1.4"; "1.4.2.0"; "1.x.2"; ""; "1..2"; "-1.0.0" ]);
  test "versions compare by their numbers, not as text" (fun () ->
      if Version.compare (1, 10, 0) (1, 9, 0) <= 0 then fail "1.10.0 is not after 1.9.0");
  test "a package's versions start with the number at the end of its name, or 1" (fun () ->
      List.iter
        (fun (name, major) ->
          let actual = Version.major_of_name name in
          if actual <> major then fail "%s gives %d" (Path.show_package name) actual)
        [
          ({ owner = Some "acme"; name = "geometry" }, 1);
          ({ owner = Some "acme"; name = "geometry_v2" }, 2);
          ({ owner = Some "acme"; name = "geometry_v17" }, 17);
          ({ owner = Some "acme"; name = "v2" }, 1);
          ({ owner = Some "acme"; name = "move" }, 1);
          ({ owner = Some "acme"; name = "geometry_v" }, 1);
        ])

(* A package's hash *)

let () =
  test "a package's hash does not depend on the order its files are given in" (fun () ->
      let files = [ ("truss.toml", "a"); ("vector.truss", "b"); ("guide/start.md", "c") ] in
      if Content.hash files <> Content.hash (List.rev files) then fail "the hashes differ";
      if not (Content.is_hash (Content.hash files)) then fail "not 64 hexadecimal digits");
  test "a package's hash changes with a file's bytes, and with its path" (fun () ->
      let hash = Content.hash [ ("a.truss", "one"); ("b.truss", "two") ] in
      if hash = Content.hash [ ("a.truss", "one"); ("b.truss", "too") ] then fail "bytes";
      if hash = Content.hash [ ("a.truss", "one"); ("c.truss", "two") ] then fail "path";
      if hash = Content.hash [ ("a.truss", "onetwo") ] then fail "one file for two")

(* The lock file *)

let lock_block () =
  String.concat "\n"
    (Documents.block_after
       (Documents.read (Harness.workspace_path "SYNTAX.md"))
       "### The lock file")
  ^ "\n"

let () =
  test "SYNTAX.md's lock file is read, and is written back as it is" (fun () ->
      let text = lock_block () in
      match Lock.parse text with
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
            holds = [ "Clock"; "Handles"; "NetworkClient" ];
            _;
          };
        ] as entries ->
          if Lock.print entries <> text then fail "written as %S" (Lock.print entries)
      | _ -> fail "read differently");
  test "a lock file with nothing in it has no package" (fun () ->
      if Lock.parse "" <> [] || Lock.parse "format 1\n" <> [] then fail "has one");
  let hash = String.make 64 'a' in
  let malformed_at line text =
    match Lock.parse text with
    | exception Lock.Malformed (actual, _) when actual = line -> ()
    | exception Lock.Malformed (actual, message) -> fail "at line %d: %s" actual message
    | _ -> fail "accepted"
  in
  test "a lock file without its first line is malformed" (fun () ->
      malformed_at 1 (Printf.sprintf "acme::geometry 1.0.0 %s\n" hash));
  test "a line that is not a name, a version, and a hash is malformed, at its line" (fun () ->
      malformed_at 2 "format 1\nacme::geometry 1.0.0\n";
      malformed_at 2 (Printf.sprintf "format 1\ngeometry 1.0.0 %s\n" hash);
      malformed_at 2 (Printf.sprintf "format 1\nacme::geometry 1.0 %s\n" hash);
      malformed_at 2 "format 1\nacme::geometry 1.0.0 abc\n";
      malformed_at 3
        (Printf.sprintf "format 1\nacme::geometry 1.0.0 %s\nacme::geometry 1.1.0 %s\n" hash hash));
  test "a version must start with the number its package's name ends in" (fun () ->
      malformed_at 2 (Printf.sprintf "format 1\nacme::geometry_v2 1.0.0 %s\n" hash);
      malformed_at 2 (Printf.sprintf "format 1\nacme::geometry 2.0.0 %s\n" hash))

(* A registry's files *)

let fresh = scratch

(* The registry at a directory, as [TRUSS_REGISTRY] names one. *)
let at root =
  Index.configure (Some root);
  Option.get (Index.current ())

(* A version's files in a registry, at [owner/name/VERSION/]. *)
let version_directory root (package : Path.package) version =
  List.fold_left Filename.concat root (Path.package_parts package @ [ Version.show version ])

let () =
  let files = [ ("truss.toml", "[package]\nname = \"acme::geometry\"\n"); ("vector.truss", "") ] in
  test "a registry lists a package's versions in the order they were added" (fun () ->
      let registry = at (fresh "registry") in
      Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      Index.add registry
        { Path.owner = Some "acme"; name = "geometry" }
        (1, 1, 0) (("angle.truss", "") :: files);
      (match Index.versions registry { Path.owner = Some "acme"; name = "geometry" } with
      | [ ((1, 0, 0), first); ((1, 1, 0), second) ] ->
          if first <> Content.hash files || first = second then fail "the hashes are wrong"
      | _ -> fail "listed differently");
      if
        Option.map fst (Index.newest registry { Path.owner = Some "acme"; name = "geometry" })
        <> Some (1, 1, 0)
      then fail "the newest is not 1.1.0";
      if Index.versions registry { Path.owner = Some "acme"; name = "nothing" } <> [] then
        fail "a package it does not hold");
  test "a version is fetched into a directory named by its hash, with every file" (fun () ->
      let registry = at (fresh "registry") and into = fresh "packages" in
      Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      let hash = Content.hash files in
      match
        Index.fetch registry ~into { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) ~hash
      with
      | Ok directory ->
          if Filename.basename directory <> hash then fail "in %s" directory;
          if Content.hash (Content.files ~all:true directory) <> hash then fail "other files"
      | Error reason -> fail "%s" reason);
  test "files that do not have the hash asked for are not kept" (fun () ->
      let root = fresh "registry" and into = fresh "packages" in
      let registry = at root in
      Index.add registry { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) files;
      let hash = Content.hash files in
      let changed =
        Filename.concat
          (version_directory root { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0))
          "vector.truss"
      in
      Out_channel.with_open_bin changed (fun channel -> output_string channel "fn extra() {}\n");
      (match
         Index.fetch registry ~into { Path.owner = Some "acme"; name = "geometry" } (1, 0, 0) ~hash
       with
      | Error reason -> if not (contains reason "do not have the hash") then fail "said %s" reason
      | Ok _ -> fail "kept");
      if Sys.readdir into <> [||] then fail "left files behind");
  test "a version the registry does not hold is not fetched" (fun () ->
      let registry = at (fresh "registry") and into = fresh "packages" in
      match
        Index.fetch registry ~into
          { Path.owner = Some "acme"; name = "geometry" }
          (1, 0, 0) ~hash:(String.make 64 'b')
      with
      | Error _ -> ()
      | Ok _ -> fail "fetched")

(* Choosing versions *)

let package text = Option.get (Path.parse_package text)
let hash_of name (version : Version.t) = Content.hash [ (name, Version.show version) ]

(* A registry in memory: each package and version, with what it depends on,
   each with the capabilities it grants, and what it was published with. *)
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
                 (fun (name, capabilities) -> { Manifest.package = package name; capabilities })
                 dependencies;
             usize_bits = 32;
           }
            : Manifest.package),
          List.map
            (fun (name, version) ->
              { Lock.name = package name; version; hash = hash_of name version; holds = [] })
            record )
  | _ -> Error "it is not there"

let entry name version =
  { Lock.name = package name; version; hash = hash_of name version; holds = [] }

let chosen (packages, problems) =
  if problems <> [] then
    fail "problems: %s" (String.concat " " (List.map Selection.sentence problems));
  List.map
    (fun (actual : Selection.package) -> (Path.show_package actual.name, actual.version))
    packages

let () =
  let published =
    [
      (("acme::geometry", (1, 0, 0)), ([ ("acme::units", []) ], [ ("acme::units", (1, 0, 0)) ]));
      (("acme::geometry", (1, 1, 0)), ([ ("acme::units", []) ], [ ("acme::units", (1, 2, 0)) ]));
      (("acme::shapes", (1, 0, 0)), ([ ("acme::units", []) ], [ ("acme::units", (1, 1, 0)) ]));
      (("acme::units", (1, 0, 0)), ([], []));
      (("acme::units", (1, 1, 0)), ([], []));
      (("acme::units", (1, 2, 0)), ([], []));
      (("acme::units", (1, 3, 0)), ([], []));
    ]
  in
  let choose lock roots =
    Selection.choose ~lock
      ~roots:(List.map (fun name -> (package "app", package name)) roots)
      ~local:(fun name -> name = package "app" || name = package "acme::local")
      ~load:(load published)
  in
  test "a build uses the version its lock file names, and nothing newer" (fun () ->
      if
        chosen (choose [ entry "acme::units" (1, 1, 0) ] [ "acme::units" ])
        <> [ ("acme::units", (1, 1, 0)) ]
      then fail "chose another");
  test "a build uses the highest version any of its packages was published with" (fun () ->
      let lock = [ entry "acme::geometry" (1, 0, 0); entry "acme::shapes" (1, 0, 0) ] in
      if
        chosen (choose lock [ "acme::geometry"; "acme::shapes" ])
        <> [
             ("acme::geometry", (1, 0, 0)); ("acme::shapes", (1, 0, 0)); ("acme::units", (1, 1, 0));
           ]
      then fail "chose another");
  test "a version the lock file names above every record's is kept" (fun () ->
      let lock = [ entry "acme::geometry" (1, 0, 0); entry "acme::units" (1, 3, 0) ] in
      if
        chosen (choose lock [ "acme::geometry" ])
        <> [ ("acme::geometry", (1, 0, 0)); ("acme::units", (1, 3, 0)) ]
      then fail "chose another");
  test "a package no dependency reaches is not in the build, whatever the lock file names"
    (fun () ->
      let lock = [ entry "acme::units" (1, 0, 0); entry "acme::shapes" (1, 0, 0) ] in
      if chosen (choose lock [ "acme::units" ]) <> [ ("acme::units", (1, 0, 0)) ] then
        fail "chose another");
  test "a dependency that nothing gives a version is a problem that names who wants it" (fun () ->
      match choose [] [ "acme::units" ] with
      | ( _,
          [
            No_version
              {
                name = { Path.owner = Some "acme"; name = "units" };
                wanted_by = { Path.owner = None; name = "app" };
              };
          ] ) ->
          ()
      | _ -> fail "not reported");
  test "a version whose files cannot be had is a problem" (fun () ->
      match choose [ entry "acme::units" (1, 9, 0) ] [ "acme::units" ] with
      | ( _,
          [
            Cannot_load
              { name = { Path.owner = Some "acme"; name = "units" }; version = 1, 9, 0; _ };
          ] ) ->
          ()
      | _ -> fail "not reported");
  test "a record that names a version under another hash than the build's is a problem" (fun () ->
      let lock =
        [
          entry "acme::geometry" (1, 0, 0); { (entry "acme::units" (1, 0, 0)) with hash = "other" };
        ]
      in
      match choose lock [ "acme::geometry" ] with
      | _, problems ->
          if
            not
              (List.exists
                 (function
                   | Selection.Two_contents
                       { name = { Path.owner = Some "acme"; name = "units" }; _ } ->
                       true
                   | _ -> false)
                 problems)
          then fail "not reported");
  test "a project's package is used whatever the registry has by its name" (fun () ->
      let published =
        (("acme::walls", (1, 0, 0)), ([ ("acme::local", []) ], [ ("acme::local", (1, 0, 0)) ]))
        :: published
      in
      let packages =
        Selection.choose
          ~lock:[ entry "acme::walls" (1, 0, 0) ]
          ~roots:
            [
              ({ Path.owner = None; name = "app" }, { Path.owner = Some "acme"; name = "walls" });
              ({ Path.owner = None; name = "app" }, { Path.owner = Some "acme"; name = "local" });
            ]
          ~local:(fun name -> name = { Path.owner = Some "acme"; name = "local" })
          ~load:(load published)
      in
      if chosen packages <> [ ("acme::walls", (1, 0, 0)) ] then fail "chose another")

(* What each package holds *)

let () =
  let package name dependencies : Selection.package =
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
          usize_bits = 32;
        };
      record = [];
    }
  in
  let grant package capabilities = { Manifest.package; capabilities } in
  test "a package holds the capabilities the project grants it" (fun () ->
      let held =
        Selection.For_testing.holds
          ~project:
            [ grant { Path.owner = Some "truss"; name = "http" } [ "NetworkClient"; "Clock" ] ]
          [ package { Path.owner = Some "truss"; name = "http" } [] ]
      in
      if held <> [ ({ Path.owner = Some "truss"; name = "http" }, [ "Clock"; "NetworkClient" ]) ]
      then fail "holds another");
  test "a package holds only the granted capabilities that its user holds itself" (fun () ->
      let held =
        Selection.For_testing.holds
          ~project:[ grant { Path.owner = Some "truss"; name = "http" } [ "NetworkClient" ] ]
          [
            package
              { Path.owner = Some "truss"; name = "http" }
              [ ({ Path.owner = Some "truss"; name = "tls" }, [ "NetworkClient"; "Clock" ]) ];
            package { Path.owner = Some "truss"; name = "tls" } [];
          ]
      in
      if List.assoc { Path.owner = Some "truss"; name = "tls" } held <> [ "NetworkClient" ] then
        fail "holds [%s]"
          (String.concat "; " (List.assoc { Path.owner = Some "truss"; name = "tls" } held)));
  test "a package holds what any of its users grants it" (fun () ->
      let held =
        Selection.For_testing.holds
          ~project:
            [
              grant { Path.owner = Some "truss"; name = "http" } [ "NetworkClient" ];
              grant { Path.owner = Some "truss"; name = "tls" } [ "Random" ];
            ]
          [
            package
              { Path.owner = Some "truss"; name = "http" }
              [ ({ Path.owner = Some "truss"; name = "tls" }, [ "NetworkClient" ]) ];
            package { Path.owner = Some "truss"; name = "tls" } [];
          ]
      in
      if
        List.assoc { Path.owner = Some "truss"; name = "tls" } held <> [ "NetworkClient"; "Random" ]
      then fail "holds another");
  test "where a lock file differs from the one a build gives is told for each package" (fun () ->
      let written =
        [
          entry "acme::units" (1, 0, 0);
          { (entry "truss::http" (1, 0, 0)) with holds = [ "Clock" ] };
        ]
      and current = [ entry "acme::geometry" (1, 0, 0); entry "truss::http" (1, 0, 0) ] in
      let actual = String.concat " " (Selection.differences ~written ~current) in
      List.iter
        (fun part -> if not (contains actual part) then fail "%s is not in: %s" part actual)
        [
          "`acme::geometry` 1.0.0 is in the build and has no line";
          "Nothing in the build uses `acme::units`";
          "`truss::http` is said to hold Clock, and the manifests grant it nothing";
        ])
