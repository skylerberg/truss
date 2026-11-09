(* The tests of reading truss.toml. See SYNTAX.md, "Package manifest". *)

open Harness
module Manifest = Type_checker.Manifest

let manifest_block () =
  let text = Documents.read "../../SYNTAX.md" in
  String.concat "\n" (Documents.block_after text "### Package manifest")

let () =
  test "SYNTAX.md's manifest gives the name and each dependency's capabilities" (fun () ->
      match Manifest.parse (manifest_block ()) with
      | {
       name = "weather";
       dependencies =
         [
           { package = "json"; capabilities = [] };
           { package = "http"; capabilities = [ "NetworkClient"; "Clock" ] };
         ];
       time_limit = 10;
      } ->
          ()
      | _ -> fail "read differently");
  test "a manifest without a name is malformed" (fun () ->
      match Manifest.parse "[package]\nversion = \"1.0\"\n" with
      | exception Manifest.Malformed (1, _) -> ()
      | _ -> fail "accepted");
  test "a line that is not key = value is malformed, at its line" (fun () ->
      match Manifest.parse "[package]\nname = \"a\"\n\n[dependencies]\njson\n" with
      | exception Manifest.Malformed (5, _) -> ()
      | _ -> fail "accepted");
  test "other sections are read past" (fun () ->
      match Manifest.parse "[package]\nname = \"a\"\n[profile]\nopt = \"3\"\n" with
      | { name = "a"; dependencies = [] } -> ()
      | _ -> fail "read differently");
  test "comments are read past, but not a # in quotes" (fun () ->
      match Manifest.parse "# The app\n[package]\nname = \"a#b\" # its name\n" with
      | { name = "a#b"; _ } -> ()
      | _ -> fail "read differently")

let () = finish ()
