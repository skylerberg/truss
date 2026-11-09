let package = "standard"

let modules =
  List.map (fun (modules, text) -> (({ package; modules } : Path.module_), text)) Files.files
