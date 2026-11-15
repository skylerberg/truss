let source =
  Query.query ~name:"source" ~phase:Phases.project ~show:Path.show_file (fun database file ->
      match Query.demand database Project.file_text file with
      | Some text -> Source.create ~path:(Path.show_file file) text
      | None -> raise Not_found)

let package database name = Query.demand database Project.package name

let modules =
  Query.query ~name:"package_modules" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.modules | None -> [])

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

let dependency_names =
  Query.query ~name:"package_dependency_names" ~phase:Phases.project ~show:Path.show_package
    (fun database name ->
      List.map
        (fun (dependency : Manifest.dependency) -> dependency.package)
        (Query.demand database dependencies name))

let exists =
  Query.query ~name:"package_exists" ~phase:Phases.project ~show:Path.show_package
    (fun database name -> Option.is_some (package database name))

let split_module database names = Path.split_module ~is_package:(Query.demand database exists) names

let module_exists =
  Query.query ~name:"module_exists" ~phase:Phases.project ~saved:true ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      List.mem module_ (Query.demand database modules module_.package))
