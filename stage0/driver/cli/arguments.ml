let move_leading_options = function
  | program :: arguments ->
      let rec split leading = function
        | ("-C" as option) :: directory :: rest -> split (directory :: option :: leading) rest
        | option :: rest
          when option = "--no-server"
               || (String.length option > 2 && String.starts_with ~prefix:"-C" option) ->
            split (option :: leading) rest
        | command :: rest when not (String.starts_with ~prefix:"-" command) ->
            command :: List.rev_append leading rest
        | rest -> List.rev_append leading rest
      in
      program :: split [] arguments
  | [] -> []
