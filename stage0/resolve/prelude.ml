(* The prelude: the names in scope in every file without a [use]. See
   DESIGN.md, "The standard library and prelude". It holds only
   UpperCamelCase names, so it can clash only with types. It is fixed for
   a language version, so it is a table here, naming the module of the
   standard library that defines each name. *)

let standard = "standard"
let in_standard modules : Path.module_ = { package = standard; modules }

(* Types, traits, and capabilities, each with the module that defines it. *)
let types =
  List.map (fun builtin -> (Intrinsic.builtin_name builtin, Intrinsic.module_)) Intrinsic.builtins
  @ List.concat_map
      (fun (modules, names) -> List.map (fun name -> (name, in_standard modules)) names)
      [
        ([ "option" ], [ "Option" ]);
        ([ "result" ], [ "Result" ]);
        ( [ "core" ],
          [
            "Equal"; "Ordered"; "Ordering"; "Hash"; "Hasher"; "Default"; "Display"; "From"; "TryFrom";
            "Copyable"; "Plain"; "Add"; "Subtract"; "Multiply"; "Divide"; "Remainder"; "Negate";
            "Index"; "Iterable"; "Cursor"; "Range"; "Indexed"; "Pair"; "ExitCode";
          ] );
        ([ "text" ], [ "String"; "StringSlice"; "TextBuilder"; "FromTemplate"; "Template"; "Literal" ]);
        ([ "list" ], [ "List"; "Slice" ]);
        ([ "map" ], [ "Map"; "Entry" ]);
        ([ "set" ], [ "Set" ]);
        ( [ "capabilities" ],
          [
            "Console"; "FileRead"; "FileWrite"; "NetworkClient"; "NetworkServer"; "Clock"; "Random";
            "Environment"; "Processes"; "Tasks"; "Panic"; "Instant"; "Duration"; "Path"; "Bytes";
            "FileError";
          ] );
      ]

(* The variants written bare everywhere, with the type they belong to. *)
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
