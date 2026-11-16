type t = { prefix : string list; last : string; member : string option }

let parse text =
  let refuse () =
    Outcome.raise_cannot_run
      "`%s` is not a path, such as `weather::forecast::parse` or \
       `weather::forecast::Forecast.summary`."
      text
  in
  match Option.map List.rev (Path.parse_names text) with
  | Some (last :: rest) -> (
      let prefix = List.rev rest in
      match String.split_on_char '.' last with
      | [ last ] -> { prefix; last; member = None }
      | [ last; member ] when last <> "" && member <> "" -> { prefix; last; member = Some member }
      | _ -> refuse ())
  | Some [] | None -> refuse ()
