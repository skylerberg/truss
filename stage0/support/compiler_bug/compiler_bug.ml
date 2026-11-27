type t = { stage : string; message : string; doing : string list }

exception Bug of t

let raise_bug ~stage format =
  Printf.ksprintf (fun message -> raise (Bug { stage; message; doing = [] })) format

let run_while_doing ~stage describe_doing work =
  let raise_broken message = raise (Bug { stage; message; doing = [ describe_doing () ] }) in
  try work () with
  | Bug bug -> raise (Bug { bug with doing = bug.doing @ [ describe_doing () ] })
  | Invalid_argument message -> raise_broken ("Invalid_argument: " ^ message)
  | Failure message -> raise_broken ("Failure: " ^ message)
  | Not_found -> raise_broken "Not_found"
  | Division_by_zero -> raise_broken "Division_by_zero"
  | Assert_failure (file, line, column) ->
      raise_broken (Printf.sprintf "Assert_failure at %s:%d:%d" file line column)

let to_string bug =
  String.concat ""
    (Printf.sprintf "%s: %s" bug.stage bug.message
    :: List.map (fun doing -> "\n  while " ^ doing) bug.doing)

let () = Printexc.register_printer (function Bug bug -> Some (to_string bug) | _ -> None)
