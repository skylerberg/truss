let move_leading_directory = function
  | program :: "-C" :: directory :: command :: rest
    when not (String.starts_with ~prefix:"-" command) ->
      program :: command :: "-C" :: directory :: rest
  | arguments -> arguments

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

let prepare arguments = extract_program_arguments (move_leading_directory arguments)
