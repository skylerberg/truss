let render_manifest name =
  Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"%s\"\n" name Manifest.truss_version

let main = {|fn main(arguments: Slice[String]) -> ExitCode {
  ExitCode.success
}
|}

let run ~name =
  let directory_name =
    match Manifest.parse_name name with
    | Some package -> package.name
    | None ->
        Outcome.raise_cannot_run
          "`%s` is not a package's name, which is a lower_snake_case name, such as `weather`, or \
           an owner and a name, such as `acme.weather`."
          name
  in
  let path = directory_name in
  if Sys.file_exists path then
    Outcome.raise_cannot_run "%s already exists." (Shown_path.show_path path);
  (try Sys.mkdir path 0o755
   with Sys_error message ->
     Outcome.raise_cannot_run "Cannot create %s: %s" (Shown_path.show_path path) message);
  Command_packages.write_file
    (Filename.concat path Command_packages.manifest_name)
    (render_manifest name);
  Command_packages.write_file (Filename.concat path "main.truss") main;
  Output.printf "Created the package %s in %s.\n" name (Shown_path.show_path path);
  0
