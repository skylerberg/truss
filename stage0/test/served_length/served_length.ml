let () =
  match Sys.argv with
  | [| _; "__serve"; key |] ->
      Workspace.serve ~key ~handle:(fun ~report_progress (request : string) ->
          report_progress "working";
          String.length request)
  | [| _; key; request |] -> (
      match
        (Workspace.call ~key
           ~report_progress:(fun text -> print_endline ("progress " ^ text))
           request
          : (int, string) result)
      with
      | Ok length -> Printf.printf "length %d\n" length
      | Error message ->
          prerr_endline message;
          exit 1)
  | _ ->
      prerr_endline "usage: served_length KEY REQUEST";
      exit 2
