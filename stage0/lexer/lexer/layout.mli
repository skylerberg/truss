type input =
  | Next of {
      kind : Token.kind;
      span : Source.span;
      first_line_break : Source.span option;
      blank_line : bool;
      unterminated_string : bool;
    }
  | End of {
      position : int;
      first_line_break : Source.span option;
      blank_line : bool;
      ends_unterminated : bool;
    }

val file :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  recovery:bool ->
  (unit -> input) ->
  Token.t array * bool

val interpolation :
  source:Source.t -> diagnostics:Diagnostic.Collector.t -> (unit -> input) -> Token.t array

val starts_definition : Source.t -> int -> bool
