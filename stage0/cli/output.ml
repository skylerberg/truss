(* A command's output streams. A command in its own process writes to its
   standard output and standard error. A command in the background process
   writes its output to a buffer, sent with the response, and writes its
   standard error, such as the status line, to the client immediately, so
   it appears while the command runs. *)

type t = {
  out : string -> unit;
  err : string -> unit;
  terminal : bool;  (** Whether the client's standard error is a terminal *)
  columns : int option;  (** The client's terminal width, when its shell exports [COLUMNS] *)
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

(* Runs [f] with [output] as the current streams, then restores the
   previous streams. *)
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
