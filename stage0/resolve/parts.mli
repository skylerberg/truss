(** Which parts of a definition the parser built as written.

    A part is one signature, one body, or one type's definition, of a definition or of a member that
    a trait or an [impl] holds itself: an associated type or a law. A method written inside one is a
    definition of its own, with parts of its own. A part is broken when one of the definition's
    recovered spans lies in it: a span with width lies in every part it overlaps, and a zero-width
    one at [p] lies in the part that starts at [p] if there is one, and otherwise in the part with
    [start <= p < stop]. A broken part is never checked, since its tree is not what the source says.
*)

type part =
  | Header  (** A definition's signature, or a type's whole definition. *)
  | Body  (** A definition's body: a function's block, or a constant's value. *)
  | Member_header of int  (** The member at that index, up to its body if it has one. *)
  | Member_body of int  (** A law's body. *)

val broken : Syntax.definition -> part -> bool

val reported : Syntax.definition -> part -> Diagnostic.reported option
(** The report of a broken part: the parser's, or the lexer's, where the parser recovered. [None]
    for a part that is as written. *)

val error_node : Syntax.span -> Diagnostic.reported
(** The report of an [Error] node, by its span: the parser builds one only where it recovered. *)
