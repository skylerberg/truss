let make_absolute path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

let normalize path =
  let parts = String.split_on_char '/' (make_absolute path) in
  let segments =
    List.fold_left
      (fun segments part ->
        match part with
        | "" | "." -> segments
        | ".." -> ( match segments with _ :: rest -> rest | [] -> [])
        | part -> part :: segments)
      [] parts
  in
  "/" ^ String.concat "/" (List.rev segments)

let make_relative ~from path =
  let split path = List.filter (( <> ) "") (String.split_on_char '/' path) in
  let rec drop from path =
    match (from, path) with
    | from_part :: from', path_part :: path' when from_part = path_part -> drop from' path'
    | _ -> (from, path)
  in
  let up, down = drop (split from) (split path) in
  match List.map (fun _ -> "..") up @ down with [] -> "." | parts -> String.concat "/" parts

let resolve_real_path path = try Unix.realpath path with Unix.Unix_error _ -> normalize path
let show_path path = make_relative ~from:(resolve_real_path (Sys.getcwd ())) (normalize path)
