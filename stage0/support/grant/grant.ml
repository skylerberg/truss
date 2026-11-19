type capability = Prelude of string | Full_path of { module_names : string list; name : string }

let prelude_capabilities =
  [
    "Console";
    "FileRead";
    "FileWrite";
    "NetworkClient";
    "NetworkServer";
    "Handles";
    "Clock";
    "Random";
    "Environment";
    "Processes";
    "Signals";
    "Tasks";
    "Log";
    "Panic";
    "RunForever";
  ]

let prelude_capability_module = Path.make_standard_module [ "capabilities" ]

let make_capability ~module_names name =
  if
    module_names = Path.list_module_parts prelude_capability_module
    && List.mem name prelude_capabilities
  then Prelude name
  else Full_path { module_names; name }

let parse_capability text =
  match Option.map List.rev (Path.parse_names text) with
  | None -> None
  | Some [ name ] -> Some (Prelude name)
  | Some (name :: reversed_module_names) ->
      Some (make_capability ~module_names:(List.rev reversed_module_names) name)
  | Some [] -> Compiler_bug.raise_bug ~stage:"Grant" "the path %S has no names" text

let show_capability = function
  | Prelude name -> name
  | Full_path { module_names; name } -> String.concat "::" (module_names @ [ name ])

let compare_capability : capability -> capability -> int = Stdlib.compare
