type piece = { first : int; stop : int }

let stop (tokens : Token.t array) ~first =
  let rec scan index depth =
    if index >= Array.length tokens then index
    else
      match tokens.(index).kind with
      | End_of_file -> index
      | Newline when depth = 0 ->
          if index + 1 < Array.length tokens && tokens.(index + 1).kind = Punctuation (Open Curly)
          then scan (index + 1) depth
          else index
      | Punctuation (Open _) -> scan (index + 1) (depth + 1)
      | Punctuation (Close _) -> if depth = 0 then index else scan (index + 1) (depth - 1)
      | _ -> scan (index + 1) depth
  in
  scan first 0

let split_pieces (tokens : Token.t array) =
  let rec collect index pieces =
    if index >= Array.length tokens then List.rev pieces
    else
      match tokens.(index).kind with
      | End_of_file -> List.rev pieces
      | Newline -> collect (index + 1) pieces
      | _ ->
          let stop = max (index + 1) (stop tokens ~first:index) in
          collect stop ({ first = index; stop } :: pieces)
  in
  collect 0 []
