(* The type checker's entry point: every stage, in order, over the
   definitions of a build. See TYPECHECKER.md, "Structure". The stages are
   linked together; each reads the earlier ones' results through their
   queries. *)

module Manifest = Manifest

(* Every diagnostic of a file, from the lexer to the package checks, in the
   file's offsets and in order. *)
let diagnostics database module_ =
  let file = Query.demand database Workspace.file module_ in
  List.sort_uniq
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    (file.diagnostics
    @ Resolve.diagnostics database module_
    @ Interface.diagnostics database module_
    @ Infer.diagnostics database module_
    @ Patterns.diagnostics database module_
    @ Usage.diagnostics database module_
    @ Ownership.diagnostics database module_
    @ Package_checks.diagnostics database module_)

(* Sets a package's modules and manifest as inputs. *)
let load_package database ~name ~dependencies (modules : (Path.module_ * string) list) =
  List.iter (fun (module_, text) -> Query.set database Workspace.file_text module_ text) modules;
  Query.set database Workspace.packages name
    { Workspace.name; dependencies; modules = List.map fst modules }

let load_standard database =
  load_package database ~name:Standard_library.package ~dependencies:[] Standard_library.modules

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
        else if Filename.check_suffix entry ".truss" then (
          let channel = open_in_bin path in
          let text = really_input_string channel (in_channel_length channel) in
          close_in channel;
          [
            ( ({ package; modules = relative @ [ Filename.chop_suffix entry ".truss" ] }
                : Path.module_),
              text );
          ])
        else [])
  in
  walk []
