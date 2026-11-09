(* The JSON the commands write with --json. See CLI.md, "Common options".
   Strings are written as diagnostics write them, so the output is always
   valid UTF-8. *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | List of t list
  | Object of (string * t) list
  | Raw of string  (** JSON written elsewhere, such as a diagnostic's *)

let rec write buffer = function
  | Null -> Buffer.add_string buffer "null"
  | Bool value -> Buffer.add_string buffer (if value then "true" else "false")
  | Int value -> Buffer.add_string buffer (string_of_int value)
  | String value -> Buffer.add_string buffer (Diagnostic.json_string value)
  | Raw text -> Buffer.add_string buffer text
  | List values ->
      Buffer.add_char buffer '[';
      List.iteri
        (fun index value ->
          if index > 0 then Buffer.add_char buffer ',';
          write buffer value)
        values;
      Buffer.add_char buffer ']'
  | Object fields ->
      Buffer.add_char buffer '{';
      List.iteri
        (fun index (name, value) ->
          if index > 0 then Buffer.add_char buffer ',';
          Buffer.add_string buffer (Diagnostic.json_string name);
          Buffer.add_char buffer ':';
          write buffer value)
        fields;
      Buffer.add_char buffer '}'

let to_string value =
  let buffer = Buffer.create 1024 in
  write buffer value;
  Buffer.contents buffer

let option f = function Some value -> f value | None -> Null

(* A command's document: the format version, its diagnostics, and its own
   fields. *)
let document ~diagnostics fields =
  Object (("format", Int 1) :: ("diagnostics", List diagnostics) :: fields)

let print value = print_endline (to_string value)
