type t = Lexing of Lexing.t | Parsing of Parsing.t

let locate = function Lexing { at; _ } -> at | Parsing { at; _ } -> at

let describe = function
  | Lexing diagnostic -> Lexing_description.describe diagnostic
  | Parsing diagnostic -> Parsing_description.describe diagnostic

let render ~text diagnostic = Description.render_file ~text (describe diagnostic)
