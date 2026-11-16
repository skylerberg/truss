module Manifest = Manifest

let manifest_block () =
  let text = File_system.read (Harness.workspace_path "PACKAGES.md") in
  String.concat "\n" (Documents.block_after text "## Package manifest")

let contains text part = Substring.contains text part

let malformed_at line text =
  match Manifest.parse text with
  | exception Manifest.Malformed { line = actual; _ } when actual = line -> ()
  | exception Manifest.Malformed { line = actual; message } ->
      Harness.fail "at line %d: %s" actual message
  | _ -> Harness.fail "accepted"

let () =
  Harness.test "PACKAGES.md's manifest gives the name and each dependency's capabilities" (fun () ->
      match Manifest.parse (manifest_block ()) with
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
                   capabilities = [ "NetworkClient"; "Handles"; "Clock" ];
                 };
               ];
           };
       time_limit_seconds = None;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test "PACKAGES.md's project manifest is a project with a time limit, and no package"
    (fun () ->
      let text = File_system.read (Harness.workspace_path "PACKAGES.md") in
      let manifest = String.concat "\n" (Documents.block_after text "## Projects") in
      if not (Manifest.has_project_table manifest) then Harness.fail "not a project";
      match Manifest.parse manifest with
      | { package = None; time_limit_seconds = Some 10 } -> ()
      | _ -> Harness.fail "read differently");
  Harness.test "a manifest has a package, a project, or both" (fun () ->
      let both = "[project]\n[package]\nname = \"a\"\n" in
      if not (Manifest.has_project_table both) then Harness.fail "not a project";
      (match Manifest.parse both with
      | { package = Some { name = { Path.owner = None; name = "a" }; _ }; _ } -> ()
      | _ -> Harness.fail "read differently");
      malformed_at 1 "# nothing\n";
      malformed_at 2 "[project]\n[dependencies]\njson = []\n");
  Harness.test "a manifest's text says whether it has a [project] table, whatever else it holds"
    (fun () ->
      if not (Manifest.has_project_table "[package]\nname = \n[project] # the root\n") then
        Harness.fail "not found";
      if Manifest.has_project_table "[package]\nname = \"project\"\n# [project]\n" then
        Harness.fail "found one");
  Harness.test "the toolchain builds a package written for its own Truss or an older one" (fun () ->
      if not (Manifest.toolchain_builds Manifest.truss_version) then Harness.fail "refuses its own";
      if not (Manifest.toolchain_builds "0.0") then Harness.fail "refuses an older one";
      if Manifest.toolchain_builds "99.0" then Harness.fail "builds a newer one");
  Harness.test "truss is two numbers" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\ntruss = \"1\"\n";
      malformed_at 3 "[package]\nname = \"a\"\ntruss = \"1.2.3\"\n";
      malformed_at 3 "[package]\nname = \"a\"\ntruss = 1\n");
  Harness.test "a manifest without a name is malformed, at its [package] table" (fun () ->
      malformed_at 2 "\n[package]\ntruss = \"0.1\"\n");
  Harness.test "a line that is not key = value is malformed, at its line" (fun () ->
      malformed_at 5 "[package]\nname = \"a\"\n\n[dependencies]\njson\n");
  Harness.test "a name is one lower_snake_case part or an owner and a name" (fun () ->
      List.iter
        (fun name -> if not (Manifest.valid_name name) then Harness.fail "%s is refused" name)
        [ "weather"; "weather_report"; "acme::geometry"; "acme::geometry_v2" ];
      List.iter
        (fun name -> if Manifest.valid_name name then Harness.fail "%s is accepted" name)
        [ ""; "Weather"; "a::b::c"; "a:b"; "::b"; "a::"; "a__b"; "9a"; "a-b" ]);
  Harness.test "a package's name that is not one is malformed, at its line" (fun () ->
      malformed_at 2 "[package]\nname = \"Weather\"\n");
  Harness.test "a dependency's name with :: is written in quotes" (fun () ->
      malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\ntruss::json = []\n");
  Harness.test "a version, as other languages' manifests have, is malformed, with the replacement"
    (fun () ->
      (match Manifest.parse "[package]\nname = \"a\"\nversion = \"1.0\"\n" with
      | exception Manifest.Malformed { line = 3; message } ->
          if not (contains message "holds no version") then Harness.fail "said %s" message
      | _ -> Harness.fail "accepted");
      (match
         Manifest.parse "[package]\nname = \"a\"\n[dependencies]\njson = { version = \"2.1\" }\n"
       with
      | exception Manifest.Malformed { line = 4; message } ->
          if not (contains message "json = []") then Harness.fail "said %s" message
      | _ -> Harness.fail "accepted");
      malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\njson = \"2.1\"\n");
  Harness.test "a table or a key a manifest does not have is malformed" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\n[profile]\nopt = \"3\"\n";
      malformed_at 3 "[package]\nname = \"a\"\nlicense = \"MIT\"\n";
      malformed_at 4 "[package]\nname = \"a\"\n[test]\nretries = 2\n";
      malformed_at 4 "[package]\nname = \"a\"\n[project]\nmembers = [\"b\"]\n");
  Harness.test "a table or a key written twice is malformed, at the second" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\nname = \"b\"\n";
      malformed_at 3 "[package]\nname = \"a\"\n[package]\n");
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
                   capabilities = [ "NetworkClient"; "Clock" ];
                 };
               ];
             _;
           };
       _;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test "comments are read past, but not a # in quotes" (fun () ->
      match
        Manifest.parse
          "# The app\n[package]\nname = \"a\" # its name\n[dependencies]\nb = [\"c#d\"] # one\n"
      with
      | {
       package =
         Some
           {
             name = { Path.owner = None; name = "a" };
             dependencies =
               [ { package = { Path.owner = None; name = "b" }; capabilities = [ "c#d" ] } ];
             _;
           };
       _;
      } ->
          ()
      | _ -> Harness.fail "read differently");
  Harness.test "a string that is not closed on its line is malformed" (fun () ->
      malformed_at 2 "[package]\nname = \"a\n")

let () =
  let text =
    "[package]\n\
     name = \"a\"\n\n\
     [dependencies]\n\
     json = []\n\
     http = [\n\
    \  \"NetworkClient\",\n\
     ]\n\
     \"truss::toml\" = []\n"
  in
  Harness.test "a manifest without a dependency loses that entry's lines and no others" (fun () ->
      let without = Manifest.without_dependency text { Path.owner = None; name = "http" } in
      if without <> "[package]\nname = \"a\"\n\n[dependencies]\njson = []\n\"truss::toml\" = []\n"
      then Harness.fail "wrote %S" without;
      let without = Manifest.without_dependency text { Path.owner = Some "truss"; name = "toml" } in
      if contains without "toml" || not (contains without "NetworkClient") then
        Harness.fail "wrote %S" without);
  Harness.test "a manifest without a dependency it does not list is unchanged" (fun () ->
      if Manifest.without_dependency text { Path.owner = None; name = "yaml" } <> text then
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
      let added = Manifest.with_dependency text { Path.owner = Some "acme"; name = "geometry" } in
      if
        added
        <> "[package]\n\
            name = \"a\"\n\n\
            [dependencies]\n\
            json = [\n\
           \  \"Clock\",\n\
            ]\n\
            \"acme::geometry\" = []\n\n\
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
        Manifest.with_dependency "[package]\nname = \"a\"" { Path.owner = None; name = "json" }
      in
      if added <> "[package]\nname = \"a\"\n\n[dependencies]\njson = []\n" then
        Harness.fail "wrote %S" added);
  Harness.test "a dependency a manifest already lists is not added again" (fun () ->
      let text = "[package]\nname = \"a\"\n[dependencies]\njson = [\"Clock\"]\n" in
      if Manifest.with_dependency text { Path.owner = None; name = "json" } <> text then
        Harness.fail "changed")
