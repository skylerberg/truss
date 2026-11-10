type t = { stage : string; message : string; doing : string list }

exception Bug of t

let bug ~stage format =
  Printf.ksprintf (fun message -> raise (Bug { stage; message; doing = [] })) format

type site = { definition : Path.t; line : int; column : int }
type unsupported = { what : string; at : site option }

exception Unsupported of unsupported

let unsupported ?at format = Printf.ksprintf (fun what -> raise (Unsupported { what; at })) format

let within ~stage doing f =
  let broken message = raise (Bug { stage; message; doing = [ doing ] }) in
  try f () with
  | Bug bug -> raise (Bug { bug with doing = bug.doing @ [ doing ] })
  | Invalid_argument message -> broken ("Invalid_argument: " ^ message)
  | Failure message -> broken ("Failure: " ^ message)
  | Not_found -> broken "Not_found"
  | Division_by_zero -> broken "Division_by_zero"

let to_string bug =
  String.concat ""
    (Printf.sprintf "%s: %s" bug.stage bug.message
    :: List.map (fun doing -> "\n  while " ^ doing) bug.doing)
