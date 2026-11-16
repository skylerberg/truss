type t = int * int * int

let parse text =
  let number part =
    if part <> "" && String.for_all (function '0' .. '9' -> true | _ -> false) part then
      int_of_string_opt part
    else None
  in
  match List.map number (String.split_on_char '.' text) with
  | [ Some major; Some minor; Some patch ] -> Some (major, minor, patch)
  | _ -> None

let show (major, minor, patch) = Printf.sprintf "%d.%d.%d" major minor patch
let compare : t -> t -> int = Stdlib.compare

let parse_major (package : Path.package) =
  match String.split_last ~sep:"_v" package.name with
  | Some (_, digits) when digits <> "" && String.for_all Char.Ascii.is_digit digits -> (
      match int_of_string_opt digits with Some major when major >= 1 -> major | _ -> 1)
  | _ -> 1

let make_first_version name = (parse_major name, 0, 0)
