(* A progress line on standard error, redrawn in place during a long step.
   It is drawn only when standard error is a terminal, and erased when the
   step ends, so logs contain only the report. *)

type t = { enabled : bool; mutable drawn : bool }

let create ~enabled = { enabled = enabled && Output.terminal (); drawn = false }

(* The terminal's width, from [COLUMNS] when the shell exports it. A
   wrapped line could not be erased, so the line is truncated to fit. *)
let width () =
  match Output.columns () with Some columns when columns > 10 -> columns - 1 | _ -> 79

(* Truncates the text to [limit] code points. *)
let cut text limit =
  let rec cut_at index count =
    if index >= String.length text then text
    else if Char.code text.[index] land 0xC0 = 0x80 then cut_at (index + 1) count
    else if count = limit then String.sub text 0 index
    else cut_at (index + 1) (count + 1)
  in
  cut_at 0 0

let erase_line = "\r\027[K"

let show status text =
  if status.enabled then begin
    Output.eprint (erase_line ^ cut text (width ()));
    status.drawn <- true
  end

let clear status =
  if status.drawn then begin
    Output.eprint erase_line;
    status.drawn <- false
  end
