type t = {
  out : string -> unit;
  err : string -> unit;
  terminal : bool;
  columns : int option;
  mutable json : bool;
}

let make_output () =
  {
    out = print_string;
    err =
      (fun text ->
        prerr_string text;
        flush stderr);
    terminal = Unix.isatty Unix.stderr && Sys.getenv_opt "TERM" <> Some "dumb";
    columns = Option.bind (Sys.getenv_opt "COLUMNS") int_of_string_opt;
    json = false;
  }

let current = ref (make_output ())

let with_ output work =
  let previous = !current in
  current := output;
  Fun.protect ~finally:(fun () -> current := previous) work

let print text = !current.out text
let print_line text = print (text ^ "\n")
let printf format = Printf.ksprintf print format
let eprint text = !current.err text
let eprint_line text = eprint (text ^ "\n")
let eprintf format = Printf.ksprintf eprint format
let terminal () = !current.terminal
let columns () = !current.columns
let json () = !current.json
let set_json json = !current.json <- json

let show_list = function
  | [] -> ""
  | [ only ] -> only
  | [ first; second ] -> first ^ " and " ^ second
  | several -> (
      match List.rev several with
      | last :: rest -> String.concat ", " (List.rev rest) ^ ", and " ^ last
      | [] -> "")
