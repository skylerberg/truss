(* [truss new]: a directory with a manifest naming the package and a
   [main.truss] with an empty [main]. *)

(* The directory is named after the package, so the name has one part. *)
let valid_name name = Type_checker.Manifest.name_parts name = Some [ name ]
let manifest name = Printf.sprintf "[package]\nname = \"%s\"\n" name

let main = {|fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
|}

let run ~directory ~name =
  if not (valid_name name) then
    Project.cannot_run
      "`%s` is not a lower_snake_case name, which a package's name must be, such as `weather` or \
       `weather_report`."
      name;
  let path = Filename.concat directory name in
  if Sys.file_exists path then Project.cannot_run "%s already exists." (Project.shown path);
  (try Sys.mkdir path 0o755
   with Sys_error message -> Project.cannot_run "Cannot make %s: %s" (Project.shown path) message);
  Project.write_file (Filename.concat path Project.manifest_name) (manifest name);
  Project.write_file (Filename.concat path "main.truss") main;
  Output.printf "Made the package %s in %s.\n" name (Project.shown path);
  0
