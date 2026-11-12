type span = { start : int; stop : int }

let span start stop =
  if start < 0 || stop < start then invalid_arg (Printf.sprintf "Source.span %d %d" start stop);
  { start; stop }

let zero_width position = span position position

type t = { path : string; text : string; line_starts : int array }

let byte_order_mark = "\xEF\xBB\xBF"

let compute_line_starts text =
  let first =
    if String.starts_with ~prefix:byte_order_mark text then String.length byte_order_mark else 0
  in
  let starts = Dynarray.of_list [ first ] in
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

let position source offset =
  let index = line_index source offset in
  let column = ref 1 in
  for byte = source.line_starts.(index) to min offset (String.length source.text) - 1 do
    (* Count every byte except UTF-8 continuation bytes. *)
    if Char.code source.text.[byte] land 0xC0 <> 0x80 then incr column
  done;
  (index + 1, !column)

let starts_line source offset = offset = line_start source offset
