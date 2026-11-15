type t = { names : string list; member : string option }

let parse text =
  let names = String.split_on_char ':' text |> List.filter (( <> ) "") in
  match List.rev names with
  | last :: rest -> (
      match String.index_opt last '.' with
      | Some dot ->
          {
            names = List.rev (String.sub last 0 dot :: rest);
            member = Some (String.sub last (dot + 1) (String.length last - dot - 1));
          }
      | None -> { names; member = None })
  | [] -> { names = []; member = None }

let prefix argument = match List.rev argument.names with _ :: rest -> List.rev rest | [] -> []
