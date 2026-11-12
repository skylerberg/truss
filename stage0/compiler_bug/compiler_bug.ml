type t = { stage : string; message : string; doing : string list }

exception Bug of t

let bug ~stage format =
  Printf.ksprintf (fun message -> raise (Bug { stage; message; doing = [] })) format

let while_doing ~stage doing work =
  let broken message = raise (Bug { stage; message; doing = [ doing ] }) in
  try work () with
  | Bug bug -> raise (Bug { bug with doing = bug.doing @ [ doing ] })
  | Invalid_argument message -> broken ("Invalid_argument: " ^ message)
  | Failure message -> broken ("Failure: " ^ message)
  | Not_found -> broken "Not_found"
  | Division_by_zero -> broken "Division_by_zero"
  | Assert_failure (file, line, column) ->
      broken (Printf.sprintf "Assert_failure at %s:%d:%d" file line column)

let to_string bug =
  String.concat ""
    (Printf.sprintf "%s: %s" bug.stage bug.message
    :: List.map (fun doing -> "\n  while " ^ doing) bug.doing)

let () = Printexc.register_printer (function Bug bug -> Some (to_string bug) | _ -> None)
