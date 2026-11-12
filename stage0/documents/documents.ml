let read path =
  let channel = open_in_bin path in
  let text = really_input_string channel (in_channel_length channel) in
  close_in channel;
  text

let truss_blocks text =
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
    let leading line =
      let rec count index =
        if index < String.length line && line.[index] = ' ' then count (index + 1) else index
      in
      count 0
    in
    let indentation =
      match List.find_opt (fun line -> String.trim line <> "") block with
      | Some line -> leading line
      | None -> 0
    in
    String.concat "\n"
      (List.map
         (fun line ->
           if String.length line >= indentation then
             String.sub line indentation (String.length line - indentation)
           else "")
         block)
  in
  List.map dedent (loop false [] [] (String.split_on_char '\n' text))

let block_after document marker =
  let rec after_marker = function
    | [] -> []
    | line :: rest -> if Substring.contains line marker then rest else after_marker rest
  in
  let rec after_fence = function
    | [] -> []
    | line :: rest -> if String.starts_with ~prefix:"```" line then rest else after_fence rest
  in
  let rec until_fence lines = function
    | [] -> List.rev lines
    | line :: rest ->
        if String.starts_with ~prefix:"```" line then List.rev lines
        else until_fence (line :: lines) rest
  in
  until_fence [] (after_fence (after_marker (String.split_on_char '\n' document)))

let words lines =
  List.sort_uniq compare
    (List.filter (( <> ) "") (List.concat_map (String.split_on_char ' ') lines))

let between document first second =
  let start = Option.get (Substring.find document first) + String.length first in
  let rest = String.sub document start (String.length document - start) in
  String.sub rest 0 (Option.get (Substring.find rest second))
  |> String.split_on_char '\n' |> List.map String.trim |> String.concat " "

let backticked text =
  match String.split_on_char '`' text with
  | [] -> []
  | _ :: rest -> List.filteri (fun index _ -> index mod 2 = 0) rest
