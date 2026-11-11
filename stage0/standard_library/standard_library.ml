let modules = List.map (fun (modules, text) -> (Path.standard_module modules, text)) Files.files
