(* The tests of reading truss.toml. *)

open Harness
module Manifest = Type_checker.Manifest

let manifest_block () =
  let text = Documents.read "../../SYNTAX.md" in
  String.concat "\n" (Documents.block_after text "### Package manifest")

let contains text part = Documents.find text part ~occurrence:1 >= 0

let malformed_at line text =
  match Manifest.parse text with
  | exception Manifest.Malformed (found, _) when found = line -> ()
  | exception Manifest.Malformed (found, message) -> fail "at line %d: %s" found message
  | _ -> fail "accepted"

let () =
  test "SYNTAX.md's manifest gives the name and each dependency's capabilities" (fun () ->
      match Manifest.parse (manifest_block ()) with
      | {
       name = "weather";
       truss = Some "0.1";
       dependencies =
         [
           { package = "forecast"; capabilities = [] };
           { package = "truss::json"; capabilities = [] };
           { package = "truss::http"; capabilities = [ "NetworkClient"; "Clock" ] };
         ];
       usize_bits = 32;
       time_limit = 10;
       project = false;
      } ->
          ()
      | _ -> fail "read differently");
  test "SYNTAX.md's project manifest has a [project] table and a time limit" (fun () ->
      let text = Documents.read "../../SYNTAX.md" in
      let block = String.concat "\n" (Documents.block_after text "### Projects") in
      match Manifest.parse ("[package]\nname = \"a\"\n" ^ block) with
      | { project = true; time_limit = 10; _ } -> ()
      | _ -> fail "read differently");
  test "a package says it runs only on 64-bit targets with usize_bits" (fun () ->
      match Manifest.parse "[package]\nname = \"a\"\nusize_bits = 64\n" with
      | { usize_bits = 64; _ } -> ()
      | _ -> fail "read differently");
  test "usize_bits other than 32 or 64 is malformed, at its line" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\nusize_bits = 16\n");
  test "a manifest without a name is malformed, at its [package] table" (fun () ->
      malformed_at 2 "\n[package]\nusize_bits = 64\n");
  test "a line that is not key = value is malformed, at its line" (fun () ->
      malformed_at 5 "[package]\nname = \"a\"\n\n[dependencies]\njson\n");
  test "a name is one lower_snake_case part or an owner and a name" (fun () ->
      List.iter
        (fun name -> if not (Manifest.valid_name name) then fail "%s is refused" name)
        [ "weather"; "weather_report"; "acme::geometry"; "acme::geometry_v2" ];
      List.iter
        (fun name -> if Manifest.valid_name name then fail "%s is accepted" name)
        [ ""; "Weather"; "a::b::c"; "a:b"; "::b"; "a::"; "a__b"; "9a"; "a-b" ]);
  test "a package's name that is not one is malformed, at its line" (fun () ->
      malformed_at 2 "[package]\nname = \"Weather\"\n");
  test "a dependency's name with :: is written in quotes" (fun () ->
      malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\ntruss::json = []\n");
  test "a version, as other languages' manifests have, is malformed, with what to write" (fun () ->
      (match Manifest.parse "[package]\nname = \"a\"\nversion = \"1.0\"\n" with
      | exception Manifest.Malformed (3, message) ->
          if not (contains message "holds no version") then fail "said %s" message
      | _ -> fail "accepted");
      (match
         Manifest.parse "[package]\nname = \"a\"\n[dependencies]\njson = { version = \"2.1\" }\n"
       with
      | exception Manifest.Malformed (4, message) ->
          if not (contains message "json = []") then fail "said %s" message
      | _ -> fail "accepted");
      malformed_at 4 "[package]\nname = \"a\"\n[dependencies]\njson = \"2.1\"\n");
  test "a table or a key a manifest does not have is malformed" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\n[profile]\nopt = \"3\"\n";
      malformed_at 3 "[package]\nname = \"a\"\nlicense = \"MIT\"\n";
      malformed_at 4 "[package]\nname = \"a\"\n[test]\nretries = 2\n";
      malformed_at 4 "[package]\nname = \"a\"\n[project]\nmembers = [\"b\"]\n");
  test "a table or a key written twice is malformed, at the second" (fun () ->
      malformed_at 3 "[package]\nname = \"a\"\nname = \"b\"\n";
      malformed_at 3 "[package]\nname = \"a\"\n[package]\n");
  test "a list may be written over several lines, with a comma after its last item" (fun () ->
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
      | { dependencies = [ { package = "http"; capabilities = [ "NetworkClient"; "Clock" ] } ]; _ }
        ->
          ()
      | _ -> fail "read differently");
  test "comments are read past, but not a # in quotes" (fun () ->
      match
        Manifest.parse
          "# The app\n[package]\nname = \"a\" # its name\n[dependencies]\nb = [\"c#d\"] # one\n"
      with
      | { name = "a"; dependencies = [ { package = "b"; capabilities = [ "c#d" ] } ]; _ } -> ()
      | _ -> fail "read differently");
  test "a string that is not closed on its line is malformed" (fun () ->
      malformed_at 2 "[package]\nname = \"a\n")

let () = finish ()
