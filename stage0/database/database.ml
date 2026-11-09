(* The code database's sessions: the inputs of a worktree, kept current, and
   the requests made of it. See DATABASE.md, "Sessions" and "Requests". *)

(* Sets a package's modules and manifest as inputs. *)
let load_package engine ~name ~dependencies (modules : (Path.module_ * string) list) =
  List.iter (fun (module_, text) -> Engine.set engine Workspace.file_text module_ text) modules;
  Engine.set engine Workspace.packages name
    { Workspace.name; dependencies; modules = List.map fst modules }

let load_standard engine =
  load_package engine ~name:Standard_library.package ~dependencies:[] Standard_library.modules

(* The frozen layer of the standard library, which every session in a
   process shares. *)
let standard_layer ?log () =
  let layer = Engine.frozen_layer ?log () in
  load_standard layer;
  layer

(* The modules of a package's directory: each [.truss] file, named by its
   path under the directory. *)
let read_directory ~package directory =
  let rec walk relative =
    let absolute =
      if relative = [] then directory
      else Filename.concat directory (String.concat Filename.dir_sep relative)
    in
    Array.to_list (Sys.readdir absolute)
    |> List.sort compare
    |> List.concat_map (fun entry ->
        let path = Filename.concat absolute entry in
        if Sys.is_directory path then walk (relative @ [ entry ])
        else if Filename.check_suffix entry ".truss" then
          let text = Source.text (Source.read_file path) in
          [
            ( ({ package; modules = relative @ [ Filename.chop_suffix entry ".truss" ] }
                : Path.module_),
              text );
          ]
        else [])
  in
  walk []
