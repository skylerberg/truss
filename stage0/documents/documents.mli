(** Reading the Markdown documents at the root of the repository, for the tests that check the code
    against them and for the tools that use their examples as input. *)

val read : string -> string
(** The bytes of a file. *)

val truss_blocks : string -> string list
(** The ```truss blocks of a document's text, each with the indentation of blocks inside list items
    removed. *)

val find : string -> string -> occurrence:int -> int
(** [find text part ~occurrence] is the offset of the [occurrence]th occurrence of [part], counting
    from 1, or -1. *)

val block_after : string -> string -> string list
(** [block_after text marker] is the lines of the first fenced block after the first line containing
    [marker]. *)

val between : string -> string -> string -> string
(** [between text first second] is the prose between two markers, with line breaks made spaces. *)

val words : string list -> string list
(** The distinct words of some lines, sorted. *)

val backticked : string -> string list
(** The parts of a text written between backticks. *)
