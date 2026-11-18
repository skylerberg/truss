let types =
  List.filter_map
    (fun (builtin : Intrinsic.builtin) ->
      match builtin with
      | Storage | View | Handle | Shared -> None
      | _ -> Some (Intrinsic.show_builtin builtin, Intrinsic.module_))
    Intrinsic.builtins
  @ List.concat_map
      (fun (modules, names) ->
        List.map (fun name -> (name, Path.make_standard_module modules)) names)
      [
        ([ "option" ], [ "Option" ]);
        ([ "result" ], [ "Result" ]);
        ([ "numbers"; "integers" ], [ "FixedWidthInteger"; "SignedInteger"; "UnsignedInteger" ]);
        ( [ "core" ],
          [
            "Equal";
            "Ordered";
            "Ordering";
            "Hash";
            "Hasher";
            "Default";
            "Display";
            "From";
            "TryFrom";
            "Copyable";
            "Plain";
            "Storable";
            "Add";
            "Subtract";
            "Multiply";
            "Divide";
            "Remainder";
            "Negate";
            "Index";
            "IndexMut";
            "IndexAssign";
            "Model";
            "Iterable";
            "Cursor";
            "Range";
            "ExitCode";
          ] );
        ([ "text" ], [ "String"; "StringSlice"; "TextBuilder"; "FromTemplate"; "Template" ]);
        ([ "list" ], [ "List"; "Slice"; "FromElements" ]);
        ([ "specification" ], [ "Sequence"; "FiniteSet"; "FiniteMap"; "Multiset" ]);
        ([ "map" ], [ "Map"; "FromEntries" ]);
        ([ "set" ], [ "Set" ]);
        ( [ "capabilities" ],
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
            "SystemError";
          ] );
        ([ "time" ], [ "Instant"; "Duration" ]);
        ([ "files" ], [ "Path" ]);
      ]

let variants = [ ("Some", "Option"); ("None", "Option"); ("Ok", "Result"); ("Err", "Result") ]
let find_type name = List.assoc_opt name types

let find_variant name =
  match List.assoc_opt name variants with
  | None -> None
  | Some type_ -> (
      match find_type type_ with
      | Some module_ -> Some (Path.Top { module_; name = type_ }, name)
      | None -> None)

let names = List.map fst types @ List.map fst variants
