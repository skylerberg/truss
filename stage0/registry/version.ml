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

let major_of_name name =
  let last = match List.rev (Path.package_parts name) with last :: _ -> last | [] -> name in
  let rec suffix index =
    if index < 0 then None
    else
      match last.[index] with
      | '0' .. '9' -> suffix (index - 1)
      | 'v' when index >= 1 && last.[index - 1] = '_' && index < String.length last - 1 ->
          int_of_string_opt (String.sub last (index + 1) (String.length last - index - 1))
      | _ -> None
  in
  match suffix (String.length last - 1) with Some number when number >= 1 -> number | _ -> 1

let first name = (major_of_name name, 0, 0)
