(* The line on standard error that shows how a long step is getting on,
   redrawn in place. It is drawn only when standard error is a terminal, and
   erased when the step ends, so logs hold only the report. *)

type t = { enabled : bool; mutable drawn : bool }

let create ~enabled = { enabled = enabled && Output.terminal (); drawn = false }

(* The terminal's width, from [COLUMNS] when the shell exports it. A line
   that wrapped could not be erased, so it is cut to fit. *)
let width () =
  match Output.columns () with Some columns when columns > 10 -> columns - 1 | _ -> 79

(* The text cut to [limit] characters, counting each UTF-8 sequence once. *)
let cut text limit =
  let rec cut_at index count =
    if index >= String.length text then text
    else if Char.code text.[index] land 0xC0 = 0x80 then cut_at (index + 1) count
    else if count = limit then String.sub text 0 index
    else cut_at (index + 1) (count + 1)
  in
  cut_at 0 0

let erase_line = "\r\027[K"

let show t text =
  if t.enabled then begin
    Output.eprint (erase_line ^ cut text (width ()));
    t.drawn <- true
  end

let clear t =
  if t.drawn then begin
    Output.eprint erase_line;
    t.drawn <- false
  end
