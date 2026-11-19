let show_option = function Some text -> Printf.sprintf "Some %S" text | None -> "None"

let expect_relative_path ~root path expected =
  let actual = File_system.find_relative_path ~root path in
  if actual <> expected then
    Harness.fail "the relative path of %S under %S is %s, not %s" path root (show_option actual)
      (show_option expected)

let expect_parent path expected =
  let actual = File_system.find_parent path in
  if actual <> expected then
    Harness.fail "the parent of %S is %s, not %s" path (show_option actual) (show_option expected)

let () =
  Harness.test "joining the empty relative path gives the directory itself" (fun () ->
      Harness.expect_strings ~expected:[ "/project"; ""; "/" ]
        (List.map (fun directory -> File_system.join_path directory "") [ "/project"; ""; "/" ]));
  Harness.test "joining to the empty directory gives the relative path itself" (fun () ->
      Harness.expect_string ~expected:"main/main.truss" (File_system.join_path "" "main/main.truss"));
  Harness.test "joining writes one separator, whatever the directory ends with" (fun () ->
      Harness.expect_strings
        ~expected:[ "/a"; "/project/a"; "/project/a"; "main/a" ]
        (List.map
           (fun directory -> File_system.join_path directory "a")
           [ "/"; "/project"; "/project/"; "main" ]));
  Harness.test "the root's relative path is empty, with or without a trailing slash" (fun () ->
      expect_relative_path ~root:"/project" "/project" (Some "");
      expect_relative_path ~root:"/project" "/project/" (Some "");
      expect_relative_path ~root:"/project/" "/project" (Some "");
      expect_relative_path ~root:"" "" (Some "");
      expect_relative_path ~root:"/" "/" (Some ""));
  Harness.test "a path below the root has its relative path, without a trailing slash" (fun () ->
      expect_relative_path ~root:"/project" "/project/main/main.truss" (Some "main/main.truss");
      expect_relative_path ~root:"/project/" "/project/main/" (Some "main");
      expect_relative_path ~root:"main" "main/main.truss" (Some "main.truss"));
  Harness.test "a path that extends the root's last name is not under the root" (fun () ->
      expect_relative_path ~root:"/project" "/projects/main.truss" None;
      expect_relative_path ~root:"main" "mainly/main.truss" None);
  Harness.test "every absolute path is under the file-system root" (fun () ->
      expect_relative_path ~root:"/" "/project/main.truss" (Some "project/main.truss");
      expect_relative_path ~root:"/" "project" None);
  Harness.test "every relative path is under the empty directory, and no absolute path is"
    (fun () ->
      expect_relative_path ~root:"" "main/main.truss" (Some "main/main.truss");
      expect_relative_path ~root:"" "/main" None);
  Harness.test "a directory is inside itself and its ancestors, not its siblings" (fun () ->
      let cases = [ ("main", "main"); ("", "main"); ("main", "main/inner"); ("main", "other") ] in
      Harness.expect_strings
        ~expected:[ "true"; "true"; "true"; "false" ]
        (List.map
           (fun (directory, path) -> string_of_bool (File_system.is_inside ~directory path))
           cases));
  Harness.test "the parent of a top-level path is the empty directory or the file-system root"
    (fun () ->
      expect_parent "main.truss" (Some "");
      expect_parent "/project" (Some "/"));
  Harness.test "the parent of a nested path ignores a trailing slash" (fun () ->
      expect_parent "main/inner/" (Some "main");
      expect_parent "/project/main" (Some "/project"));
  Harness.test "the empty directory and the file-system root have no parent" (fun () ->
      expect_parent "" None;
      expect_parent "/" None)
