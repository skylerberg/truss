type span = { start : int; stop : int }

let span start stop =
  if start < 0 || stop < start then invalid_arg (Printf.sprintf "Source.span %d %d" start stop);
  { start; stop }

let zero_width position = span position position

type t = { path : string; text : string; line_starts : int array }

let compute_line_starts text =
  let starts = Dynarray.of_list [ 0 ] in
  let length = String.length text in
  String.iteri
    (fun index character ->
      match character with
      | '\n' -> Dynarray.add_last starts (index + 1)
      | '\r' when index + 1 >= length || text.[index + 1] <> '\n' ->
          Dynarray.add_last starts (index + 1)
      | _ -> ())
    text;
  Dynarray.to_array starts

let create ~path text = { path; text; line_starts = compute_line_starts text }
let read_file path = create ~path (In_channel.with_open_bin path In_channel.input_all)
let path source = source.path
let text source = source.text

let byte_order_mark_length source =
  if String.starts_with ~prefix:"\xEF\xBB\xBF" source.text then 3 else 0

(* The index of the line holding [offset], counting from 0. *)
let line_index source offset =
  let starts = source.line_starts in
  let rec search low high =
    if low >= high then low
    else
      let middle = (low + high + 1) / 2 in
      if starts.(middle) <= offset then search middle high else search low (middle - 1)
  in
  search 0 (Array.length starts - 1)

let line_start source offset = source.line_starts.(line_index source offset)

let line_end source offset =
  let index = line_index source offset in
  if index + 1 < Array.length source.line_starts then
    let next = source.line_starts.(index + 1) in
    if next >= 2 && source.text.[next - 2] = '\r' && source.text.[next - 1] = '\n' then next - 2
    else next - 1
  else String.length source.text

type units = Bytes | Scalar_values | Utf_16_code_units

(* Where the columns of a line start counting: after the byte order mark on
   the first line. *)
let first_column source index =
  max source.line_starts.(index) (if index = 0 then byte_order_mark_length source else 0)

(* The width in [units] of the character at [at], and its width in bytes. *)
let step units text at =
  let decoded = String.get_utf_8_uchar text at in
  let width = max 1 (Uchar.utf_decode_length decoded) in
  match units with
  | Bytes -> (width, width)
  | Scalar_values -> (1, width)
  | Utf_16_code_units ->
      ((if Uchar.to_int (Uchar.utf_decode_uchar decoded) >= 0x10000 then 2 else 1), width)

let location units source offset =
  let offset = max 0 (min offset (String.length source.text)) in
  let index = line_index source offset in
  let rec count at column =
    if at >= offset then column
    else
      let counted, width = step units source.text at in
      count (at + width) (column + counted)
  in
  (index, count (first_column source index) 0)

let position source offset =
  let line, column = location Scalar_values source offset in
  (line + 1, column + 1)

let offset units source ~line ~column =
  if line >= Array.length source.line_starts then String.length source.text
  else
    let stop = line_end source source.line_starts.(line) in
    let rec walk at counted =
      if at >= stop || counted >= column then at
      else
        let units, width = step units source.text at in
        walk (at + width) (counted + units)
    in
    walk (first_column source line) 0

let starts_line source offset =
  offset = line_start source offset || offset = byte_order_mark_length source
