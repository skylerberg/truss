(* A file's text, with its table of lines. Equality compares the table as
   it would anything else, so two reads of the same text are equal. *)
let source =
  Query.query ~name:"source" ~phase:Phases.project ~show:Path.show_file (fun database file ->
      match Query.demand database Project.file_text file with
      | Some text -> Source.create ~path:(Path.show_file file) text
      | None -> raise Not_found)

let package database name = Query.demand database Project.package name

(* A package's manifest, one field at a time: a result that reads
   only a package's modules is not recomputed when its dependencies
   change, and the other way round. *)
let modules =
  Query.query ~name:"package_modules" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.modules | None -> [])

(* A module's files, in order. Every file of a package is in a module, so a
   module that has no file is not one. *)
let package_files =
  Query.query ~name:"package_files" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.files | None -> [])

let files =
  Query.query ~name:"module_files" ~phase:Phases.project ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      List.filter
        (fun (file : Path.file) -> file.module_ = module_)
        (Query.demand database package_files module_.package))

let dependencies =
  Query.query ~name:"package_dependencies" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.dependencies | None -> [])

let usize_bits =
  Query.query ~name:"package_usize_bits" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.usize_bits | None -> 32)

let exists =
  Query.query ~name:"package_exists" ~phase:Phases.project ~show:Path.show_package
    (fun database name -> Option.is_some (package database name))

let split_module database names = Path.split_module ~is_package:(Query.demand database exists) names

let module_exists =
  Query.query ~name:"module_exists" ~phase:Phases.project ~saved:true ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      List.mem module_ (Query.demand database modules module_.package))
