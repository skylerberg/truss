(* [truss new]: a directory with a manifest naming the package and a
   [main.truss] with an empty [main]. *)

let manifest name =
  Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"%s\"\n" name Manifest.truss_version

let main = {|fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
|}

(* The directory is named after the package, without its owner. *)
let run ~directory ~name =
  let directory_name =
    match Manifest.parse_name name with
    | Some package -> package.name
    | None ->
        Project.cannot_run
          "`%s` is not a package's name, which is a lower_snake_case name, such as `weather`, or \
           an owner and a name, such as `acme::weather`."
          name
  in
  let path = Filename.concat directory directory_name in
  if Sys.file_exists path then Project.cannot_run "%s already exists." (Project.shown path);
  (try Sys.mkdir path 0o755
   with Sys_error message -> Project.cannot_run "Cannot make %s: %s" (Project.shown path) message);
  Project.write_file (Filename.concat path Project.manifest_name) (manifest name);
  Project.write_file (Filename.concat path "main.truss") main;
  Output.printf "Made the package %s in %s.\n" name (Project.shown path);
  0
