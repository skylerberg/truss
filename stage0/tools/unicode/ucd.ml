let read_lines directory name =
  In_channel.with_open_bin (Filename.concat directory name) In_channel.input_lines

let strip_byte_order_mark line =
  if String.starts_with ~prefix:"\xEF\xBB\xBF" line then String.sub line 3 (String.length line - 3)
  else line

let strip_comment line =
  match String.index_opt line '#' with Some index -> String.sub line 0 index | None -> line

let records directory name =
  read_lines directory name
  |> List.filter_map (fun line ->
      let line = strip_comment (strip_byte_order_mark line) in
      if String.trim line = "" then None
      else Some (List.map String.trim (String.split_on_char ';' line)))

let code_point text = int_of_string ("0x" ^ text)

let code_point_range text =
  match String.index_opt text '.' with
  | Some index ->
      ( code_point (String.sub text 0 index),
        code_point (String.sub text (index + 2) (String.length text - index - 2)) )
  | None ->
      let value = code_point text in
      (value, value)

let merge ranges =
  let sorted = List.sort compare ranges in
  let rec loop merged = function
    | [] -> List.rev merged
    | (first, last) :: rest -> (
        match merged with
        | (merged_first, merged_last) :: merged_rest when first <= merged_last + 1 ->
            loop ((merged_first, max last merged_last) :: merged_rest) rest
        | _ -> loop ((first, last) :: merged) rest)
  in
  loop [] sorted
