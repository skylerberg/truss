type t = int * int * int

let parse text =
  let parse_number part =
    if part <> "" && String.for_all (function '0' .. '9' -> true | _ -> false) part then
      int_of_string_opt part
    else None
  in
  match List.map parse_number (String.split_on_char '.' text) with
  | [ Some major; Some minor; Some patch ] -> Some (major, minor, patch)
  | _ -> None

let show (major, minor, patch) = Printf.sprintf "%d.%d.%d" major minor patch
let compare : t -> t -> int = Stdlib.compare

let find_major_suffix (package : Path.package) =
  match String.split_last ~sep:"_v" package.name with
  | Some (base, digits) when digits <> "" && String.for_all Char.Ascii.is_digit digits -> (
      match int_of_string_opt digits with
      | Some major when major >= 2 -> Some (base, major)
      | _ -> None)
  | _ -> None

let parse_major package =
  match find_major_suffix package with Some (_, major) -> major | None -> 1

let make_next_major_name (package : Path.package) =
  let base, major = Option.value (find_major_suffix package) ~default:(package.name, 1) in
  { package with name = Printf.sprintf "%s_v%d" base (major + 1) }
