(* Paths as a command shows them: relative to the current directory. *)

let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

(* The path with [.] and [..] segments resolved and no trailing
   separator. *)
let normalize path =
  let parts = String.split_on_char '/' (absolute path) in
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

(* [path] relative to [from], both normalized, such as [forecast.truss] or
   [../weather/forecast.truss]. *)
let relative ~from path =
  let split path = List.filter (( <> ) "") (String.split_on_char '/' path) in
  let rec drop from path =
    match (from, path) with
    | from_part :: from', path_part :: path' when from_part = path_part -> drop from' path'
    | _ -> (from, path)
  in
  let up, down = drop (split from) (split path) in
  match List.map (fun _ -> "..") up @ down with [] -> "." | parts -> String.concat "/" parts

let real path = try Unix.realpath path with Unix.Unix_error _ -> normalize path
let shown path = relative ~from:(real (Sys.getcwd ())) (normalize path)
