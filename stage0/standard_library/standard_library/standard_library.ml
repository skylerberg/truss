let files =
  List.map
    (fun (modules, name, text) : (Path.file * string) ->
      ({ module_ = Path.standard_module modules; name }, text))
    Files.files
