(* Reading a package's manifest, [truss.toml]: the subset of TOML a
   manifest uses. See SYNTAX.md, "Package manifest".

     [package]
     name = "weather"
     version = "0.3.0"

     [dependencies]
     http = { version = "4.0", capabilities = ["NetworkClient", "Clock"] } *)

type t = { name : string; dependencies : Workspace.dependency list }

exception Malformed of int * string

let trim = String.trim

let unquote line text =
  let text = trim text in
  let length = String.length text in
  if length >= 2 && text.[0] = '"' && text.[length - 1] = '"' then String.sub text 1 (length - 2)
  else raise (Malformed (line, "a value in quotes"))

(* [{ version = "4.0", capabilities = ["A", "B"] }] *)
let table line text =
  let text = trim text in
  let length = String.length text in
  if length < 2 || text.[0] <> '{' || text.[length - 1] <> '}' then
    raise (Malformed (line, "a table in braces"));
  let inner = String.sub text 1 (length - 2) in
  (* Split on the commas outside brackets. *)
  let parts = ref [] and depth = ref 0 and start = ref 0 in
  String.iteri
    (fun index character ->
      match character with
      | '[' -> incr depth
      | ']' -> decr depth
      | ',' when !depth = 0 ->
          parts := String.sub inner !start (index - !start) :: !parts;
          start := index + 1
      | _ -> ())
    inner;
  parts := String.sub inner !start (String.length inner - !start) :: !parts;
  List.filter_map
    (fun part ->
      if trim part = "" then None
      else
        match String.index_opt part '=' with
        | Some equals ->
            Some
              ( trim (String.sub part 0 equals),
                trim (String.sub part (equals + 1) (String.length part - equals - 1)) )
        | None -> raise (Malformed (line, "`key = value`")))
    (List.rev !parts)

let list line text =
  let text = trim text in
  let length = String.length text in
  if length < 2 || text.[0] <> '[' || text.[length - 1] <> ']' then
    raise (Malformed (line, "a list in brackets"));
  List.filter_map
    (fun item -> if trim item = "" then None else Some (unquote line item))
    (String.split_on_char ',' (String.sub text 1 (length - 2)))

(* A line without its [#] comment, which a [#] inside quotes does not
   start. *)
let without_comment line =
  let quoted = ref false and stop = ref (String.length line) in
  String.iteri
    (fun index character ->
      if !stop = String.length line then
        match character with
        | '"' -> quoted := not !quoted
        | '#' when not !quoted -> stop := index
        | _ -> ())
    line;
  String.sub line 0 !stop

let parse text =
  let section = ref "" and name = ref None and dependencies = ref [] in
  List.iteri
    (fun index raw ->
      let line = index + 1 in
      let text = trim (without_comment raw) in
      if text = "" then ()
      else if text.[0] = '[' then section := text
      else
        match String.index_opt text '=' with
        | None -> raise (Malformed (line, "`key = value`"))
        | Some equals -> (
            let key = trim (String.sub text 0 equals)
            and value = String.sub text (equals + 1) (String.length text - equals - 1) in
            match !section with
            | "[package]" -> if key = "name" then name := Some (unquote line value)
            | "[dependencies]" ->
                let entries = table line value in
                let capabilities =
                  match List.assoc_opt "capabilities" entries with
                  | Some value -> list line value
                  | None -> []
                in
                dependencies := { Workspace.package = key; capabilities } :: !dependencies
            (* Other sections, such as a build profile, are read past. *)
            | _ -> ()))
    (String.split_on_char '\n' text);
  match !name with
  | Some name -> { name; dependencies = List.rev !dependencies }
  | None -> raise (Malformed (1, "a [package] section with a name"))
