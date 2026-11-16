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

let extract_program_arguments = function
  | program :: "run" :: rest ->
      let rec list_options = function
        | "--" :: rest -> "--" :: rest
        | ("-C" as option) :: value :: rest -> option :: value :: list_options rest
        | (("--release" | "--json" | "--no-server" | "--help" | "-h") as option) :: rest ->
            option :: list_options rest
        | option :: rest
          when String.starts_with ~prefix:"-C" option || String.starts_with ~prefix:"--help=" option
          ->
            option :: list_options rest
        | [] -> []
        | first :: rest -> "--" :: first :: rest
      in
      program :: "run" :: list_options rest
  | arguments -> arguments

let prepare arguments = extract_program_arguments (move_leading_options arguments)
