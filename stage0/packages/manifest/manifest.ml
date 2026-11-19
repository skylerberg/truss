type dependency = { package : Path.package; capabilities : Grant.capability list }
type package = { name : Path.package; truss : string option; dependencies : dependency list }
type t = { package : package option; time_limit_seconds : int option }

let default_time_limit_seconds = 10

exception Malformed of { line : int; message : string }

let raise_malformed line format =
  Printf.ksprintf (fun message -> raise (Malformed { line; message })) format

let is_lower_snake_case name =
  name <> ""
  && (match name.[0] with 'a' .. 'z' -> true | _ -> false)
  && String.for_all (function 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false) name
  && List.for_all (( <> ) "") (String.split_on_char '_' name)

let parse_name text =
  match Path.parse_package text with
  | Some package when List.for_all is_lower_snake_case (Path.list_package_parts package) ->
      Some package
  | _ -> None

let is_valid_name text = parse_name text <> None

type token =
  | Open
  | Close
  | Open_brace
  | Close_brace
  | Equals
  | Comma
  | Quoted of string
  | Bare of string
  | Line_break

let is_bare = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' | ':' -> true
  | _ -> false

let tokenize_line line text =
  let length = String.length text in
  let lexed = ref [] in
  let add token = lexed := (token, line) :: !lexed in
  let rec scan index =
    if index < length then
      match text.[index] with
      | ' ' | '\t' | '\r' -> scan (index + 1)
      | '#' -> ()
      | '[' -> add_punctuation Open index
      | ']' -> add_punctuation Close index
      | '{' -> add_punctuation Open_brace index
      | '}' -> add_punctuation Close_brace index
      | '=' -> add_punctuation Equals index
      | ',' -> add_punctuation Comma index
      | '"' -> scan_quoted (Buffer.create 16) (index + 1)
      | character when is_bare character ->
          let stop = ref index in
          while !stop < length && is_bare text.[!stop] do
            incr stop
          done;
          add (Bare (String.sub text index (!stop - index)));
          scan !stop
      | character -> raise_malformed line "`%c` cannot be written here." character
  and add_punctuation token index =
    add token;
    scan (index + 1)
  and scan_quoted buffer index =
    if index >= length then raise_malformed line "This string is not closed on its line."
    else
      match text.[index] with
      | '"' ->
          add (Quoted (Buffer.contents buffer));
          scan (index + 1)
      | '\\' when index + 1 < length && (text.[index + 1] = '"' || text.[index + 1] = '\\') ->
          Buffer.add_char buffer text.[index + 1];
          scan_quoted buffer (index + 2)
      | character ->
          Buffer.add_char buffer character;
          scan_quoted buffer (index + 1)
  in
  scan 0;
  List.rev ((Line_break, line) :: !lexed)

type value = Text of string | Number of int | List of string list | Inline_table
type entry = { key : string; quoted : bool; value : value; line : int; last_line : int }
type table = { name : string; line : int; entries : entry list }
type statement = Header of table | Entry of entry

let value_expected = "a string in quotes, a whole number, or a list in brackets"

let rec skip_line_breaks = function
  | (Line_break, _) :: rest -> skip_line_breaks rest
  | rest -> rest

let rec list_items line items rest =
  match skip_line_breaks rest with
  | (Close, _) :: rest -> (List.rev items, rest)
  | (Quoted item, _) :: rest -> (
      match skip_line_breaks rest with
      | (Comma, _) :: rest -> list_items line (item :: items) rest
      | (Close, _) :: rest -> (List.rev (item :: items), rest)
      | (_, line) :: _ -> raise_malformed line "Expected `,` or `]` after a list's item."
      | [] -> raise_malformed line "This list is not closed with `]`.")
  | (_, line) :: _ -> raise_malformed line "A list holds strings in quotes, with `,` between them."
  | [] -> raise_malformed line "This list is not closed with `]`."

let rec skip_past_brace line = function
  | (Close_brace, _) :: rest -> rest
  | (Line_break, _) :: _ | [] -> raise_malformed line "This table is not closed with `}`."
  | _ :: rest -> skip_past_brace line rest

let parse_value line = function
  | (Quoted text, _) :: rest -> (Text text, rest)
  | (Bare text, _) :: rest when int_of_string_opt text <> None -> (Number (int_of_string text), rest)
  | (Open, _) :: rest ->
      let items, rest = list_items line [] rest in
      (List items, rest)
  | (Open_brace, _) :: rest -> (Inline_table, skip_past_brace line rest)
  | _ -> raise_malformed line "Expected a value after `=`: %s." value_expected

let expect_end_of_line line = function
  | (Line_break, last_line) :: rest -> (last_line, rest)
  | _ -> raise_malformed line "Expected the line to end here."

let parse_statement line = function
  | (Open, _) :: ((Bare name | Quoted name), _) :: (Close, _) :: rest ->
      (Header { name; line; entries = [] }, snd (expect_end_of_line line rest))
  | (((Bare key | Quoted key) as token), _) :: (Equals, _) :: rest ->
      let value, rest = parse_value line rest in
      let last_line, rest = expect_end_of_line line rest in
      let quoted = match token with Quoted _ -> true | _ -> false in
      (Entry { key; quoted; value; line; last_line }, rest)
  | _ ->
      raise_malformed line
        "Expected a table, such as `[package]`, or a line of the form `key = value`."

let read_tables text =
  let problems = ref [] in
  let report line message = problems := (line, message) :: !problems in
  let tokens =
    List.concat
      (List.mapi
         (fun index line_text ->
           match tokenize_line (index + 1) line_text with
           | tokens -> tokens
           | exception Malformed { line; message } ->
               report line message;
               [ (Line_break, line) ])
         (String.split_on_char '\n' text))
  in
  let rec skip_through line = function
    | (_, token_line) :: rest when token_line <= line -> skip_through line rest
    | rest -> rest
  in
  let close tables = function
    | Some table -> { table with entries = List.rev table.entries } :: tables
    | None -> tables
  in
  let rec parse_statements tables current = function
    | [] -> List.rev (close tables current)
    | (Line_break, _) :: rest -> parse_statements tables current rest
    | (_, line) :: _ as tokens -> (
        match (parse_statement line tokens, current) with
        | (Header table, rest), _ -> parse_statements (close tables current) (Some table) rest
        | (Entry entry, rest), Some table ->
            parse_statements tables (Some { table with entries = entry :: table.entries }) rest
        | (Entry entry, rest), None ->
            report entry.line
              (Printf.sprintf
                 "`%s` is in no table. A manifest starts with a table, such as `[package]`."
                 entry.key);
            parse_statements tables current rest
        | exception Malformed { line; message } ->
            report line message;
            parse_statements tables current (skip_through line tokens))
  in
  let tables = parse_statements [] None tokens in
  (tables, List.stable_sort (fun (left, _) (right, _) -> Int.compare left right) !problems)

let parse_tables text =
  match read_tables text with
  | tables, [] -> tables
  | _, (line, message) :: _ -> raise (Malformed { line; message })

let name_expected =
  "a `lower_snake_case` name, or an owner and a name joined by `::`, such as `weather` or \
   `acme::geometry`"

let read_text (entry : entry) =
  match entry.value with
  | Text text -> text
  | _ -> raise_malformed entry.line "`%s` is a string in quotes." entry.key

let read_number (entry : entry) =
  match entry.value with
  | Number number -> number
  | _ -> raise_malformed entry.line "`%s` is a whole number." entry.key

let parse_version text =
  match List.map int_of_string_opt (String.split_on_char '.' text) with
  | [ Some major; Some minor ]
    when String.for_all (function '0' .. '9' | '.' -> true | _ -> false) text ->
      Some (major, minor)
  | _ -> None

let truss_version = "0.1"

let toolchain_builds version =
  match (parse_version version, parse_version truss_version) with
  | Some wanted, Some toolchain -> compare wanted toolchain <= 0
  | _ -> false

let parse_granted_capability (entry : entry) written =
  match Grant.parse_capability written with
  | Some capability -> capability
  | None ->
      raise_malformed entry.line
        "`%s` names no capability. A grant names a capability of the prelude by its name, such as \
         `Clock`, and any other by its full path."
        written

let parse_dependency (entry : entry) : dependency =
  let package =
    match parse_name entry.key with
    | Some package -> package
    | None ->
        raise_malformed entry.line "`%s` is not a package's name, which is %s." entry.key
          name_expected
  in
  if (not entry.quoted) && package.owner <> None then
    raise_malformed entry.line "A name with `::` is written in quotes: `\"%s\" = []`." entry.key;
  match entry.value with
  | List capabilities ->
      { package; capabilities = List.map (parse_granted_capability entry) capabilities }
  | Inline_table ->
      raise_malformed entry.line
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`. A \
         manifest holds no versions: `truss add` writes them in `truss.lock`."
        (if entry.quoted then Printf.sprintf "%S" entry.key else entry.key)
  | Text _ ->
      raise_malformed entry.line
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`, not a \
         version. `truss add` writes versions in `truss.lock`."
        (if entry.quoted then Printf.sprintf "%S" entry.key else entry.key)
  | Number _ ->
      raise_malformed entry.line "A dependency's entry is the list of capabilities it is granted."

let parse text =
  let tables = parse_tables text in
  let seen = Hashtbl.create 4 in
  List.iter
    (fun (table : table) ->
      if Hashtbl.mem seen table.name then
        raise_malformed table.line "The table `[%s]` is already written above." table.name;
      Hashtbl.replace seen table.name ();
      let keys = Hashtbl.create 8 in
      List.iter
        (fun (entry : entry) ->
          if Hashtbl.mem keys entry.key then
            raise_malformed entry.line "`%s` is already written above." entry.key;
          Hashtbl.replace keys entry.key ())
        table.entries)
    tables;
  let find_table name = List.find_opt (fun (table : table) -> table.name = name) tables in
  let list_entries name = match find_table name with Some table -> table.entries | None -> [] in
  List.iter
    (fun (table : table) ->
      if not (List.mem table.name [ "package"; "dependencies"; "test"; "project" ]) then
        raise_malformed table.line
          "A manifest has no table `[%s]`. Its tables are `[package]`, `[dependencies]`, \
           `[project]`, and `[test]`."
          table.name)
    tables;
  let name = ref None and truss = ref None in
  List.iter
    (fun (entry : entry) ->
      match entry.key with
      | "name" ->
          let text = read_text entry in
          name :=
            Some
              (match parse_name text with
              | Some package -> package
              | None -> raise_malformed entry.line "A package's name is %s." name_expected)
      | "truss" ->
          let text = read_text entry in
          if parse_version text = None then
            raise_malformed entry.line
              "`truss` is the version of Truss the package is written for, as two numbers, such as \
               `\"%s\"`."
              truss_version;
          truss := Some text
      | "version" ->
          raise_malformed entry.line
            "A manifest holds no version. The registry gives a package its version when it is \
             published. Delete this line."
      | key ->
          raise_malformed entry.line "`[package]` has no key `%s`. Its keys are `name` and `truss`."
            key)
    (list_entries "package");
  let time_limit_seconds = ref None in
  List.iter
    (fun (entry : entry) ->
      match entry.key with
      | "time_limit" ->
          let seconds = read_number entry in
          if seconds <= 0 then
            raise_malformed entry.line "`time_limit` is a whole number of seconds, more than 0.";
          time_limit_seconds := Some seconds
      | key -> raise_malformed entry.line "`[test]` has no key `%s`. Its key is `time_limit`." key)
    (list_entries "test");
  List.iter
    (fun (entry : entry) -> raise_malformed entry.line "`[project]` has no key `%s`." entry.key)
    (list_entries "project");
  let package =
    match (find_table "package", !name) with
    | Some _, Some name ->
        Some
          {
            name;
            truss = !truss;
            dependencies = List.map parse_dependency (list_entries "dependencies");
          }
    | Some table, None ->
        raise_malformed table.line "`[package]` names its package, with `name = \"...\"` under it."
    | None, _ -> (
        match find_table "dependencies" with
        | Some table ->
            raise_malformed table.line
              "`[dependencies]` are a package's, and this manifest has no `[package]`."
        | None -> None)
  in
  if package = None && find_table "project" = None then
    raise_malformed 1 "A manifest has a `[package]` table, a `[project]` table, or both.";
  { package; time_limit_seconds = !time_limit_seconds }

let has_project_table text =
  List.exists (fun (table : table) -> table.name = "project") (fst (read_tables text))

let find_dependencies_table text =
  List.find_opt (fun (table : table) -> table.name = "dependencies") (parse_tables text)

let find_dependency_entry (table : table) package =
  List.find_opt (fun (entry : entry) -> parse_name entry.key = Some package) table.entries

let remove_dependency text package =
  match
    Option.bind (find_dependencies_table text) (fun table -> find_dependency_entry table package)
  with
  | None -> text
  | Some entry ->
      String.split_on_char '\n' text
      |> List.filteri (fun index _ -> index + 1 < entry.line || index + 1 > entry.last_line)
      |> String.concat "\n"

let add_dependency text (package : Path.package) =
  let name = Path.show_package package in
  let entry =
    Printf.sprintf "%s = []" (if package.owner <> None then Printf.sprintf "%S" name else name)
  in
  match find_dependencies_table text with
  | Some table when find_dependency_entry table package <> None -> text
  | Some table ->
      let after =
        match List.rev table.entries with last :: _ -> last.last_line | [] -> table.line
      in
      String.concat "\n"
        (List.concat
           (List.mapi
              (fun index line -> if index + 1 = after then [ line; entry ] else [ line ])
              (String.split_on_char '\n' text)))
  | None ->
      let text = if text = "" || text.[String.length text - 1] = '\n' then text else text ^ "\n" in
      text ^ "\n[dependencies]\n" ^ entry ^ "\n"
