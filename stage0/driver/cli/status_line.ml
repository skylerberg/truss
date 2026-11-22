type t = { enabled : bool; mutable drawn : bool }

let create ~enabled = { enabled = enabled && Output.is_terminal (); drawn = false }

let measure_width () =
  match Output.columns () with Some columns when columns > 10 -> columns - 1 | _ -> 79

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
    Output.eprint (erase_line ^ cut text (measure_width ()));
    status.drawn <- true
  end

let clear status =
  if status.drawn then begin
    Output.eprint erase_line;
    status.drawn <- false
  end

module For_testing = struct
  let cut = cut
end
