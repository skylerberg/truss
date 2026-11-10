(** Which parts of a definition the parser built as written.

    A part is one signature, one body, or one type's definition, of a definition or of a member of a
    trait, an [impl], or a capability. It is broken when one of the definition's recovered spans
    lies in it: a span with width lies in every part it overlaps, and a zero-width one at [p] lies
    in the part that starts at [p] if there is one, and otherwise in the part with
    [start <= p < stop]. A broken part is never checked, since its tree is not what the source says.
*)

type part =
  | Header  (** A definition's signature, or a type's whole definition. *)
  | Body  (** A definition's body: a function's block, or a constant's value. *)
  | Member_header of int  (** The signature of the member at that index. *)
  | Member_body of int

val broken : Syntax.definition -> part -> bool
