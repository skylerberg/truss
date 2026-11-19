let list_truss_blocks text =
  let rec loop inside current blocks = function
    | [] -> List.rev blocks
    | line :: rest ->
        let trimmed = String.trim line in
        if inside then
          if String.starts_with ~prefix:"```" trimmed then
            loop false [] (List.rev current :: blocks) rest
          else loop true (line :: current) blocks rest
        else loop (trimmed = "```truss") [] blocks rest
  in
  let dedent block =
    let count_leading line =
      let rec count index =
        if index < String.length line && line.[index] = ' ' then count (index + 1) else index
      in
      count 0
    in
    let indentation =
      match List.find_opt (fun line -> String.trim line <> "") block with
      | Some line -> count_leading line
      | None -> 0
    in
    String.concat "\n" (List.map (String.drop_first indentation) block)
  in
  List.map dedent (loop false [] [] (String.split_on_char '\n' text))

let list_block_after document marker =
  let rec skip_past_marker = function
    | [] -> []
    | line :: rest -> if String.includes ~affix:marker line then rest else skip_past_marker rest
  in
  let rec skip_past_fence = function
    | [] -> []
    | line :: rest -> if String.starts_with ~prefix:"```" line then rest else skip_past_fence rest
  in
  let rec take_until_fence lines = function
    | [] -> List.rev lines
    | line :: rest ->
        if String.starts_with ~prefix:"```" line then List.rev lines
        else take_until_fence (line :: lines) rest
  in
  take_until_fence [] (skip_past_fence (skip_past_marker (String.split_on_char '\n' document)))

let list_words lines =
  List.sort_uniq compare
    (List.filter (( <> ) "") (List.concat_map (String.split_on_char ' ') lines))
