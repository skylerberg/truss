(* The line on standard error that shows how a long step is getting on,
   redrawn in place. It is drawn only when standard error is a terminal, and
   erased when the step ends, so logs hold only the report. See CLI.md,
   "Testing". *)

type t = { enabled : bool; mutable drawn : bool }

let create ~enabled =
  {
    enabled = enabled && Unix.isatty Unix.stderr && Sys.getenv_opt "TERM" <> Some "dumb";
    drawn = false;
  }

(* The terminal's width, from [COLUMNS] when the shell exports it. A line
   that wrapped could not be erased, so it is cut to fit. *)
let width () =
  match Option.bind (Sys.getenv_opt "COLUMNS") int_of_string_opt with
  | Some columns when columns > 10 -> columns - 1
  | _ -> 79

(* The text cut to [limit] characters, counting each UTF-8 sequence once. *)
let cut text limit =
  let rec go index count =
    if index >= String.length text then text
    else if Char.code text.[index] land 0xC0 = 0x80 then go (index + 1) count
    else if count = limit then String.sub text 0 index
    else go (index + 1) (count + 1)
  in
  go 0 0

let erase_line = "\r\027[K"

let show t text =
  if t.enabled then begin
    prerr_string (erase_line ^ cut text (width ()));
    flush stderr;
    t.drawn <- true
  end

let clear t =
  if t.drawn then begin
    prerr_string erase_line;
    flush stderr;
    t.drawn <- false
  end
