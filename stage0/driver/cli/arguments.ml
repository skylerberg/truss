let leading_directory = function
  | program :: "-C" :: directory :: command :: rest
    when not (String.starts_with ~prefix:"-" command) ->
      program :: command :: "-C" :: directory :: rest
  | arguments -> arguments

let program_arguments = function
  | program :: "run" :: rest ->
      let rec options = function
        | "--" :: rest -> "--" :: rest
        | ("-C" as option) :: value :: rest -> option :: value :: options rest
        | (("--release" | "--json" | "--no-server" | "--help" | "-h") as option) :: rest ->
            option :: options rest
        | option :: rest
          when String.starts_with ~prefix:"-C" option || String.starts_with ~prefix:"--help=" option
          ->
            option :: options rest
        | [] -> []
        | first :: rest -> "--" :: first :: rest
      in
      program :: "run" :: options rest
  | arguments -> arguments

let prepare arguments = program_arguments (leading_directory arguments)
