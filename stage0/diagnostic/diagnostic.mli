(** Errors with spans and exact fixes, shared by every stage of the compiler.

    Every diagnostic is an error: Truss has no warnings. Each has a stable
    code, so that tools and agents match on codes rather than on message
    text. *)

type span = Source.span = private { start : int; stop : int }

(** The codes, one constructor each, so that a misspelled code cannot
    compile. {!Code.name} gives the stable name tools see, such as
    ["lexer.unterminated_string"]. *)
module Code : sig
  type t =
    | Invalid_utf8
    | Carriage_return
    | Forbidden_character
    | Comment
    | Semicolon
    | Unexpected_character
    | Strict_equality
    | Character_literal
    | Name_case
    | Name_not_ascii
    | Number_suffix
    | Number_uppercase_prefix
    | Number_uppercase_exponent
    | Number_missing_digits
    | Number_invalid_digit
    | Number_followed_by_name
    | Number_underscore
    | Number_leading_zero
    | Unterminated_string
    | Invalid_escape
    | Line_break_in_interpolation
    | Empty_interpolation
    | Interpolation_too_deep
    | Raw_string_quotes
    | Raw_string_closing_not_alone
    | Raw_string_indentation
    | Unclosed_bracket
    | Unmatched_closing_bracket
    | Too_many_diagnostics

  val name : t -> string
end

type edit = { span : span; replacement : string }
(** Replace the bytes of [span] with [replacement]. An empty span inserts. *)

type fix = { title : string; edits : edit list }

type t = {
  code : Code.t;
  message : string;
  span : span;
  notes : (span * string) list;
  fixes : fix list;  (** Alternatives. Most diagnostics have at most one. *)
}

val make : ?notes:(span * string) list -> ?fixes:fix list -> code:Code.t -> span -> string -> t

val fix : string -> edit list -> fix
val replace : span -> string -> edit
val insert : int -> string -> edit
val delete : span -> edit

val apply_fix : string -> fix -> string
(** Applies a fix's edits to the text it was made for. Raises
    [Invalid_argument] if the edits overlap. *)

(** Collects the diagnostics of one file. Every diagnostic is kept, so that
    later checks, such as of fixes, see all of them; only {!shown} limits how
    many are listed. *)
module Collector : sig
  type diagnostic := t
  type t

  val create : unit -> t
  val add : t -> diagnostic -> unit

  val to_list : t -> diagnostic list
  (** In order of position. *)
end

val limit : int

val shown : t list -> t list
(** The diagnostics to list: at most {!limit}, and then, if there were more,
    one with the code [Too_many_diagnostics] that counts the rest, so that a
    binary file opened by mistake gives a short report. *)

(** {1 Showing diagnostics} *)

val render : Source.t -> t -> string
(** For people: the position, the code and message, the line of source with
    the span marked, and the notes and fixes. *)

val to_json : Source.t -> t list -> string
(** For tools: a JSON array. Spans carry byte offsets as well as lines and
    columns, and fixes are always byte ranges. The output is always valid
    UTF-8: a byte that is not valid UTF-8, which can only come from quoted
    source text, is written as U+FFFD. *)

val quote : string -> string
(** Text in double quotes, with quotes, backslashes, control characters, and
    bytes that are not valid UTF-8 escaped, so that text in any script stays
    readable and the result is valid UTF-8. *)
