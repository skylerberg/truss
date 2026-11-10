(* Where a command writes. A command run in its own process writes to its
   standard output and error. One run in the background process writes its
   output to a buffer, which goes back with the answer, and its errors,
   such as the status line, straight to the client as progress, so they show
   while it works. *)

type t = {
  out : string -> unit;
  err : string -> unit;
  terminal : bool;  (** Whether the client's standard error is a terminal *)
  columns : int option;  (** The client's terminal width, when its shell says *)
}

let local () =
  {
    out = print_string;
    err =
      (fun text ->
        prerr_string text;
        flush stderr);
    terminal = Unix.isatty Unix.stderr && Sys.getenv_opt "TERM" <> Some "dumb";
    columns = Option.bind (Sys.getenv_opt "COLUMNS") int_of_string_opt;
  }

let current = ref (local ())

(* Runs [f] writing to [output], and comes back to where it wrote before. *)
let with_ output f =
  let previous = !current in
  current := output;
  Fun.protect ~finally:(fun () -> current := previous) f

let print text = !current.out text
let print_line text = print (text ^ "\n")
let printf format = Printf.ksprintf print format
let eprint text = !current.err text
let eprint_line text = eprint (text ^ "\n")
let eprintf format = Printf.ksprintf eprint format
let terminal () = !current.terminal
let columns () = !current.columns
