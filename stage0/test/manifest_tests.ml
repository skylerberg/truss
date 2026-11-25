module Manifest = Manifest

let read_manifest_block () =
  let text = File_system.read (Harness.make_workspace_path "PACKAGES.md") in
  String.concat "\n" (Documents.list_block_after text "## Package manifest")

let expect_malformed_at line text =
  match Manifest.parse text with
  | exception Manifest.Malformed { line = actual; _ } when actual = line -> ()
  | exception Manifest.Malformed { line = actual; problem } ->
      let message = Project_catalog.describe_manifest_problem problem in
      Harness.fail "at line %d: %s" actual message
  | _ -> Harness.fail "accepted"

let () =
  Harness.test "PACKAGES.md's manifest gives the name and each dependency's capabilities" (fun () ->
      match Manifest.parse (read_manifest_block ()) with
      | {
       package =
         Some
           {
             name = { Path.owner = None; name = "weather" };
             truss = Some "0.1";
             dependencies =
               [
                 { package = { Path.owner = None; name = "forecast" }; capabilities = [] };
                 {
                   package = { Path.owner = Some "truss"; name = "postgres" };
                   capabilities =
                     [
                       Grant.Prelude "NetworkClient"; Grant.Prelude "Handles"; Grant.Prelude "Clock";
                     ];
                 };
               ];
           };
       time_limit_seconds = None;
       x86_64_level = None;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test
    "PACKAGES.md's project manifest is a project with a time limit and an x86-64 level, and no \
     package" (fun () ->
      let text = File_system.read (Harness.make_workspace_path "PACKAGES.md") in
      let manifest = String.concat "\n" (Documents.list_block_after text "## Projects") in
      if not (Manifest.has_project_table manifest) then Harness.fail "not a project";
      match Manifest.parse manifest with
      | { package = None; time_limit_seconds = Some 10; x86_64_level = Some V2 } -> ()
      | _ -> Harness.fail "read differently");
  Harness.test "a manifest has a package, a project, or both" (fun () ->
      let both = "[project]\n[package]\nname = \"a\"\n" in
      if not (Manifest.has_project_table both) then Harness.fail "not a project";
      (match Manifest.parse both with
      | { package = Some { name = { Path.owner = None; name = "a" }; _ }; _ } -> ()
      | _ -> Harness.fail "read differently");
      expect_malformed_at 1 "# nothing\n";
      expect_malformed_at 2 "[project]\n[dependencies]\njson = []\n");
  Harness.test "a manifest's text says whether it has a [project] table, whatever else it holds"
    (fun () ->
      if not (Manifest.has_project_table "[package]\nname = \n[project] # the root\n") then
        Harness.fail "not found";
      if Manifest.has_project_table "[package]\nname = \"project\"\n# [project]\n" then
        Harness.fail "found one");
  Harness.test "a [project] table written with spaces or quotes in its brackets makes a project"
    (fun () ->
      List.iter
        (fun text ->
          if not (Manifest.has_project_table text) then Harness.fail "%S is not a project" text)
        [ "[ project ]\n"; "[\"project\"]\n"; "[project]\n" ]);
  Harness.test "a grant names a prelude capability alike by its name and by its full path"
    (fun () ->
      let read_grant written =
        match
          Manifest.parse
            (Printf.sprintf "[package]\nname = \"a\"\n[dependencies]\nb = [\"%s\"]\n" written)
        with
        | { package = Some { dependencies = [ { capabilities; _ } ]; _ }; _ } -> capabilities
        | _ -> failwith "the grant is read differently"
      in
      if read_grant "Clock" <> read_grant "standard.capabilities.Clock" then
        Harness.fail "the two are different grants";
      if read_grant "acme.store.Ledger" = read_grant "Ledger" then
        Harness.fail "a capability outside the prelude is its name alone");
  Harness.test "the toolchain builds a package written for its own Truss or an older one" (fun () ->
      if not (Manifest.toolchain_builds Manifest.truss_version) then Harness.fail "refuses its own";
      if not (Manifest.toolchain_builds "0.0") then Harness.fail "refuses an older one";
      if Manifest.toolchain_builds "99.0" then Harness.fail "builds a newer one");
  Harness.test "truss is two numbers" (fun () ->
      expect_malformed_at 3 "[package]\nname = \"a\"\ntruss = \"1\"\n";
      expect_malformed_at 3 "[package]\nname = \"a\"\ntruss = \"1.2.3\"\n";
      expect_malformed_at 3 "[package]\nname = \"a\"\ntruss = 1\n");
  Harness.test "a manifest without a name is malformed, at its [package] table" (fun () ->
      expect_malformed_at 2 "\n[package]\ntruss = \"0.1\"\n");
  Harness.test "a line that is not key = value is malformed, at its line" (fun () ->
      expect_malformed_at 5 "[package]\nname = \"a\"\n\n[dependencies]\njson\n");
  Harness.test "a name is one lower_snake_case part or an owner and a name" (fun () ->
      List.iter
        (fun name -> if not (Manifest.is_valid_name name) then Harness.fail "%s is refused" name)
        [ "weather"; "weather_report"; "acme.geometry"; "acme.geometry_v2" ];
      List.iter
        (fun name -> if Manifest.is_valid_name name then Harness.fail "%s is accepted" name)
        [ ""; "Weather"; "a.b.c"; "a:b"; ".b"; "a."; "a__b"; "9a"; "a-b" ]);
  Harness.test "a package's name that is not one is malformed, at its line" (fun () ->
      expect_malformed_at 2 "[package]\nname = \"Weather\"\n");
  Harness.test "a dependency's name with an owner is written in quotes" (fun () ->
      expect_malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\ntruss.json = []\n");
  Harness.test "a version, as other languages' manifests have, is malformed, with the replacement"
    (fun () ->
      (match Manifest.parse "[package]\nname = \"a\"\nversion = \"1.0\"\n" with
      | exception Manifest.Malformed { line = 3; problem } ->
          let message = Project_catalog.describe_manifest_problem problem in
          if not (String.includes ~affix:"holds no version" message) then
            Harness.fail "said %s" message
      | _ -> Harness.fail "accepted");
      (match
         Manifest.parse "[package]\nname = \"a\"\n[dependencies]\njson = { version = \"2.1\" }\n"
       with
      | exception Manifest.Malformed { line = 4; problem } ->
          let message = Project_catalog.describe_manifest_problem problem in
          if not (String.includes ~affix:"json = []" message) then Harness.fail "said %s" message
      | _ -> Harness.fail "accepted");
      expect_malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\njson = \"2.1\"\n");
  Harness.test "a table or a key a manifest does not have is malformed" (fun () ->
      expect_malformed_at 3 "[package]\nname = \"a\"\n[profile]\nopt = \"3\"\n";
      expect_malformed_at 3 "[package]\nname = \"a\"\nlicense = \"MIT\"\n";
      expect_malformed_at 4 "[package]\nname = \"a\"\n[test]\nretries = 2\n";
      expect_malformed_at 4 "[package]\nname = \"a\"\n[project]\nmembers = [\"b\"]\n");
  Harness.test "a table or a key written twice is malformed, at the second" (fun () ->
      expect_malformed_at 3 "[package]\nname = \"a\"\nname = \"b\"\n";
      expect_malformed_at 3 "[package]\nname = \"a\"\n[package]\n");
  Harness.test "a list may be written over several lines, with a comma after its last item"
    (fun () ->
      match
        Manifest.parse
          "[package]\n\
           name = \"a\"\n\
           [dependencies]\n\
           http = [\n\
          \  \"NetworkClient\",\n\
          \  \"Clock\",\n\
           ]\n"
      with
      | {
       package =
         Some
           {
             dependencies =
               [
                 {
                   package = { Path.owner = None; name = "http" };
                   capabilities = [ Grant.Prelude "NetworkClient"; Grant.Prelude "Clock" ];
                 };
               ];
             _;
           };
       _;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test "comments are read past, but not a # in quotes" (fun () ->
      (match
         Manifest.parse
           "# The app\n[package]\nname = \"a\" # its name\n[dependencies]\nb = [\"Clock\"] # one\n"
       with
      | {
       package =
         Some
           {
             name = { Path.owner = None; name = "a" };
             dependencies =
               [
                 { package = { Path.owner = None; name = "b" }; capabilities = [ Prelude "Clock" ] };
               ];
             _;
           };
       _;
      } ->
          ()
      | _ -> Harness.fail "read differently");
      match Manifest.parse "[package]\nname = \"a\"\n[dependencies]\nb = [\"c#d\"]\n" with
      | exception Manifest.Malformed { line = 4; problem } ->
          let message = Project_catalog.describe_manifest_problem problem in
          if not (String.includes ~affix:"`c#d`" message) then Harness.fail "said %s" message
      | _ -> Harness.fail "accepted a capability named `c#d`");
  Harness.test "a grant that is neither a capability's name nor a path is malformed, at its line"
    (fun () -> expect_malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\nb = [\"a:b\"]\n");
  Harness.test "the first malformed line is reported, whatever the mistake on a later line"
    (fun () -> expect_malformed_at 2 "[package]\nname\n[dependencies]\nb = [\"c\"] %\n");
  Harness.test "a string that is not closed on its line is malformed" (fun () ->
      expect_malformed_at 2 "[package]\nname = \"a\n")

let () =
  let text =
    "[package]\n\
     name = \"a\"\n\n\
     [dependencies]\n\
     json = []\n\
     http = [\n\
    \  \"NetworkClient\",\n\
     ]\n\
     \"truss.toml\" = []\n"
  in
  Harness.test "a manifest without a dependency loses that entry's lines and no others" (fun () ->
      let without = Manifest.remove_dependency text { Path.owner = None; name = "http" } in
      if without <> "[package]\nname = \"a\"\n\n[dependencies]\njson = []\n\"truss.toml\" = []\n"
      then Harness.fail "wrote %S" without;
      let without = Manifest.remove_dependency text { Path.owner = Some "truss"; name = "toml" } in
      if
        String.includes ~affix:"toml" without
        || not (String.includes ~affix:"NetworkClient" without)
      then Harness.fail "wrote %S" without);
  Harness.test "a manifest without a dependency it does not list is unchanged" (fun () ->
      if Manifest.remove_dependency text { Path.owner = None; name = "yaml" } <> text then
        Harness.fail "changed")

let () =
  Harness.test "a dependency is added after a manifest's other entries, granted nothing" (fun () ->
      let text =
        "[package]\n\
         name = \"a\"\n\n\
         [dependencies]\n\
         json = [\n\
        \  \"Clock\",\n\
         ]\n\n\
         [test]\n\
         time_limit = 3\n"
      in
      let added = Manifest.add_dependency text { Path.owner = Some "acme"; name = "geometry" } in
      if
        added
        <> "[package]\n\
            name = \"a\"\n\n\
            [dependencies]\n\
            json = [\n\
           \  \"Clock\",\n\
            ]\n\
            \"acme.geometry\" = []\n\n\
            [test]\n\
            time_limit = 3\n"
      then Harness.fail "wrote %S" added;
      match Manifest.parse added with
      | {
       package =
         Some
           {
             dependencies =
               [
                 _; { package = { Path.owner = Some "acme"; name = "geometry" }; capabilities = [] };
               ];
             _;
           };
       _;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test "a dependency is added to a manifest with no dependencies, in a table of its own"
    (fun () ->
      let added =
        Manifest.add_dependency "[package]\nname = \"a\"" { Path.owner = None; name = "json" }
      in
      if added <> "[package]\nname = \"a\"\n\n[dependencies]\njson = []\n" then
        Harness.fail "wrote %S" added);
  Harness.test "a dependency a manifest already lists is not added again" (fun () ->
      let text = "[package]\nname = \"a\"\n[dependencies]\njson = [\"Clock\"]\n" in
      if Manifest.add_dependency text { Path.owner = None; name = "json" } <> text then
        Harness.fail "changed")
