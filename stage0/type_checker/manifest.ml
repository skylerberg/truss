(* Reading a manifest, [truss.toml], in the part of TOML a manifest is
   written in: tables, and keys whose values are a string, a whole number,
   or a list of strings.

     [package]
     name = "weather"
     truss = "0.1"

     [dependencies]
     forecast = []
     "truss::http" = ["NetworkClient", "Clock"]

     [test]
     time_limit = 10 *)

type package = {
  name : string;
  truss : string option;
  dependencies : Workspace.dependency list;
  usize_bits : int;
}

type t = { package : package option; project : bool; time_limit : int option }

let default_time_limit = 10

exception Malformed of int * string

let malformed line format =
  Printf.ksprintf (fun message -> raise (Malformed (line, message))) format

let is_lower_snake_case name =
  name <> ""
  && (match name.[0] with 'a' .. 'z' -> true | _ -> false)
  && String.for_all (function 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false) name
  && List.for_all (( <> ) "") (String.split_on_char '_' name)

(* [acme::geometry] is [Some ["acme"; "geometry"]]. *)
let name_parts name =
  match String.split_on_char ':' name with
  | [ one ] when is_lower_snake_case one -> Some [ one ]
  | [ owner; ""; one ] when is_lower_snake_case owner && is_lower_snake_case one ->
      Some [ owner; one ]
  | _ -> None

let valid_name name = name_parts name <> None

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

(* Each token with its line, counting from 1. *)
let tokens text =
  let length = String.length text in
  let found = ref [] in
  let line = ref 1 in
  let add token = found := (token, !line) :: !found in
  let rec scan index =
    if index < length then
      match text.[index] with
      | ' ' | '\t' | '\r' -> scan (index + 1)
      | '\n' ->
          add Line_break;
          incr line;
          scan (index + 1)
      | '#' ->
          let stop = try String.index_from text index '\n' with Not_found -> length in
          scan stop
      | '[' -> punctuation Open index
      | ']' -> punctuation Close index
      | '{' -> punctuation Open_brace index
      | '}' -> punctuation Close_brace index
      | '=' -> punctuation Equals index
      | ',' -> punctuation Comma index
      | '"' -> quoted (Buffer.create 16) (index + 1)
      | character when is_bare character ->
          let stop = ref index in
          while !stop < length && is_bare text.[!stop] do
            incr stop
          done;
          add (Bare (String.sub text index (!stop - index)));
          scan !stop
      | character -> malformed !line "`%c` cannot be written here." character
  and punctuation token index =
    add token;
    scan (index + 1)
  and quoted buffer index =
    if index >= length || text.[index] = '\n' then
      malformed !line "This string is not closed on its line."
    else
      match text.[index] with
      | '"' ->
          add (Quoted (Buffer.contents buffer));
          scan (index + 1)
      | '\\' when index + 1 < length && (text.[index + 1] = '"' || text.[index + 1] = '\\') ->
          Buffer.add_char buffer text.[index + 1];
          quoted buffer (index + 2)
      | character ->
          Buffer.add_char buffer character;
          quoted buffer (index + 1)
  in
  scan 0;
  List.rev !found

type value = Text of string | Number of int | List of string list | Inline_table
type entry = { key : string; quoted : bool; value : value; line : int; last_line : int }
type table = { name : string; line : int; entries : entry list }

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
      | (_, line) :: _ -> malformed line "Expected `,` or `]` after a list's item."
      | [] -> malformed line "This list is not closed with `]`.")
  | (_, line) :: _ -> malformed line "A list holds strings in quotes, with `,` between them."
  | [] -> malformed line "This list is not closed with `]`."

let rec after_brace line = function
  | (Close_brace, _) :: rest -> rest
  | (Line_break, _) :: _ | [] -> malformed line "This table is not closed with `}`."
  | _ :: rest -> after_brace line rest

let value line = function
  | (Quoted text, _) :: rest -> (Text text, rest)
  | (Bare text, _) :: rest when int_of_string_opt text <> None -> (Number (int_of_string text), rest)
  | (Open, _) :: rest ->
      let items, rest = list_items line [] rest in
      (List items, rest)
  | (Open_brace, _) :: rest -> (Inline_table, after_brace line rest)
  | _ -> malformed line "Expected a value after `=`: %s." value_expected

let end_of_line line = function
  | (Line_break, _) :: rest -> rest
  | [] -> []
  | _ -> malformed line "Expected the line to end here."

let tables text =
  let rec statements tables current = function
    | [] -> List.rev (close tables current)
    | (Line_break, _) :: rest -> statements tables current rest
    | (Open, line) :: ((Bare name | Quoted name), _) :: (Close, _) :: rest ->
        statements (close tables current)
          (Some { name; line; entries = [] })
          (end_of_line line rest)
    | (((Bare key | Quoted key) as token), line) :: (Equals, _) :: rest -> (
        let found, rest = value line rest in
        let quoted = match token with Quoted _ -> true | _ -> false in
        let last_line = match rest with (_, last) :: _ -> last | [] -> max_int in
        match current with
        | Some table ->
            statements tables
              (Some
                 {
                   table with
                   entries = { key; quoted; value = found; line; last_line } :: table.entries;
                 })
              (end_of_line line rest)
        | None ->
            malformed line
              "`%s` is in no table. A manifest starts with a table, such as `[package]`." key)
    | (_, line) :: _ ->
        malformed line "Expected a table, such as `[package]`, or a line of the form `key = value`."
  and close tables = function
    | Some table -> { table with entries = List.rev table.entries } :: tables
    | None -> tables
  in
  statements [] None (tokens text)

let name_expected =
  "a `lower_snake_case` name, or an owner and a name joined by `::`, such as `weather` or \
   `acme::geometry`"

let text_of (entry : entry) =
  match entry.value with
  | Text text -> text
  | _ -> malformed entry.line "`%s` is a string in quotes." entry.key

let number_of (entry : entry) =
  match entry.value with
  | Number number -> number
  | _ -> malformed entry.line "`%s` is a whole number." entry.key

let version_of text =
  match List.map int_of_string_opt (String.split_on_char '.' text) with
  | [ Some major; Some minor ]
    when String.for_all (function '0' .. '9' | '.' -> true | _ -> false) text ->
      Some (major, minor)
  | _ -> None

let truss_version = "0.1"

let toolchain_builds version =
  match (version_of version, version_of truss_version) with
  | Some wanted, Some toolchain -> compare wanted toolchain <= 0
  | _ -> false

let dependency (entry : entry) : Workspace.dependency =
  if not (valid_name entry.key) then
    malformed entry.line "`%s` is not a package's name, which is %s." entry.key name_expected;
  if (not entry.quoted) && String.contains entry.key ':' then
    malformed entry.line "A name with `::` is written in quotes: `\"%s\" = []`." entry.key;
  match entry.value with
  | List capabilities -> { package = entry.key; capabilities }
  | Inline_table ->
      malformed entry.line
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`. A \
         manifest holds no versions: `truss add` writes them in `truss.lock`."
        (if entry.quoted then Printf.sprintf "%S" entry.key else entry.key)
  | Text _ ->
      malformed entry.line
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`, not a \
         version. `truss add` writes versions in `truss.lock`."
        (if entry.quoted then Printf.sprintf "%S" entry.key else entry.key)
  | Number _ ->
      malformed entry.line "A dependency's entry is the list of capabilities it is granted."

let parse text =
  let tables = tables text in
  let seen = Hashtbl.create 4 in
  List.iter
    (fun (table : table) ->
      if Hashtbl.mem seen table.name then
        malformed table.line "The table `[%s]` is already written above." table.name;
      Hashtbl.replace seen table.name ();
      let keys = Hashtbl.create 8 in
      List.iter
        (fun (entry : entry) ->
          if Hashtbl.mem keys entry.key then
            malformed entry.line "`%s` is already written above." entry.key;
          Hashtbl.replace keys entry.key ())
        table.entries)
    tables;
  let table name = List.find_opt (fun (table : table) -> table.name = name) tables in
  let entries name = match table name with Some table -> table.entries | None -> [] in
  List.iter
    (fun (table : table) ->
      if not (List.mem table.name [ "package"; "dependencies"; "test"; "project" ]) then
        malformed table.line
          "A manifest has no table `[%s]`. Its tables are `[package]`, `[dependencies]`, \
           `[project]`, and `[test]`."
          table.name)
    tables;
  let name = ref None and truss = ref None and usize_bits = ref 32 in
  List.iter
    (fun (entry : entry) ->
      match entry.key with
      | "name" ->
          let text = text_of entry in
          if not (valid_name text) then malformed entry.line "A package's name is %s." name_expected;
          name := Some text
      | "truss" ->
          let text = text_of entry in
          if version_of text = None then
            malformed entry.line
              "`truss` is the version of Truss the package is written for, as two numbers, such as \
               `\"%s\"`."
              truss_version;
          truss := Some text
      | "usize_bits" -> (
          match entry.value with
          | Number ((32 | 64) as bits) -> usize_bits := bits
          | _ -> malformed entry.line "`usize_bits` is 32 or 64.")
      | "version" ->
          malformed entry.line
            "A manifest holds no version. The registry gives a package its version when it is \
             published. Delete this line."
      | key ->
          malformed entry.line
            "`[package]` has no key `%s`. Its keys are `name`, `truss`, and `usize_bits`." key)
    (entries "package");
  let time_limit = ref None in
  List.iter
    (fun (entry : entry) ->
      match entry.key with
      | "time_limit" ->
          let seconds = number_of entry in
          if seconds <= 0 then
            malformed entry.line "`time_limit` is a whole number of seconds, more than 0.";
          time_limit := Some seconds
      | key -> malformed entry.line "`[test]` has no key `%s`. Its key is `time_limit`." key)
    (entries "test");
  List.iter
    (fun (entry : entry) -> malformed entry.line "`[project]` has no key `%s`." entry.key)
    (entries "project");
  let package =
    match (table "package", !name) with
    | Some _, Some name ->
        Some
          {
            name;
            truss = !truss;
            dependencies = List.map dependency (entries "dependencies");
            usize_bits = !usize_bits;
          }
    | Some table, None ->
        malformed table.line "`[package]` names its package, with `name = \"...\"` under it."
    | None, _ -> (
        match table "dependencies" with
        | Some table ->
            malformed table.line
              "`[dependencies]` are a package's, and this manifest has no `[package]`."
        | None -> None)
  in
  let project = table "project" <> None in
  if package = None && not project then
    malformed 1 "A manifest has a `[package]` table, a `[project]` table, or both.";
  { package; project; time_limit = !time_limit }

(* Whether a manifest's text has a [[project]] table, told without reading
   the rest, so that a manifest with a mistake elsewhere still says where
   its project's root is. *)
let has_project_table text =
  List.exists
    (fun line ->
      let line =
        match String.index_opt line '#' with Some index -> String.sub line 0 index | None -> line
      in
      String.trim line = "[project]")
    (String.split_on_char '\n' text)

let without_dependency text name =
  let entry =
    Option.bind
      (List.find_opt (fun (table : table) -> table.name = "dependencies") (tables text))
      (fun table -> List.find_opt (fun (entry : entry) -> entry.key = name) table.entries)
  in
  match entry with
  | None -> text
  | Some entry ->
      String.split_on_char '\n' text
      |> List.filteri (fun index _ -> index + 1 < entry.line || index + 1 > entry.last_line)
      |> String.concat "\n"

let with_dependency text name =
  let entry =
    Printf.sprintf "%s = []" (if String.contains name ':' then Printf.sprintf "%S" name else name)
  in
  match List.find_opt (fun (table : table) -> table.name = "dependencies") (tables text) with
  | Some table when List.exists (fun (entry : entry) -> entry.key = name) table.entries -> text
  | Some table ->
      let lines = String.split_on_char '\n' text in
      let after =
        match List.rev table.entries with last :: _ -> last.last_line | [] -> table.line
      in
      let after = min after (List.length lines) in
      String.concat "\n"
        (List.concat
           (List.mapi
              (fun index line -> if index + 1 = after then [ line; entry ] else [ line ])
              lines))
  | None ->
      let text = if text = "" || text.[String.length text - 1] = '\n' then text else text ^ "\n" in
      text ^ "\n[dependencies]\n" ^ entry ^ "\n"
