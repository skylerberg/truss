(** Errors with spans and exact fixes, shared by every stage of the compiler.

    Every diagnostic is an error: Truss has no warnings. Each has a stable
    [code], such as ["lexer.unterminated_string"], so that tools and agents
    match on codes rather than on message text. *)

type span = Source.span = { start : int; stop : int }

type edit = { span : span; replacement : string }
(** Replace the bytes of [span] with [replacement]. An empty span inserts. *)

type fix = { title : string; edits : edit list }

type t = {
  code : string;
  message : string;
  span : span;
  notes : (span * string) list;
  fixes : fix list;  (** Alternatives. Most diagnostics have at most one. *)
}

val make : ?notes:(span * string) list -> ?fixes:fix list -> code:string -> span -> string -> t

val fix : string -> edit list -> fix
val replace : span -> string -> edit
val insert : int -> string -> edit
val delete : span -> edit

val apply_fix : string -> fix -> string
(** Applies a fix's edits to the text it was made for. The edits must not
    overlap. *)

(** Collects the diagnostics of one file. *)
module Collector : sig
  type diagnostic := t
  type t

  val create : unit -> t
  val add : t -> diagnostic -> unit

  type mark

  val mark : t -> mark
  val reset : t -> mark -> unit
  (** Drops every diagnostic added since the mark, for a stage that tries
      something and then backs off. *)

  val count : t -> int

  val to_list : t -> diagnostic list
  (** In order of position. At most {!limit} are kept, and if more were
      added, a last diagnostic with the code ["too_many_diagnostics"] counts
      the rest, so that a binary file opened by mistake gives a short
      report. *)
end

val limit : int

(** {1 Showing diagnostics} *)

val render : Source.t -> t -> string
(** For people: the position, the code and message, the line of source with
    the span marked, and the notes and fixes. *)

val to_json : Source.t -> t list -> string
(** For tools: a JSON array. Spans carry byte offsets as well as lines and
    columns, and fixes are always byte ranges. *)

val quote : string -> string
(** Text in double quotes, with only quotes, backslashes, and control
    characters escaped, so that text in any script stays readable. *)
