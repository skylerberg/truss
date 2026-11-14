module References = References

type unfinished = { keyword : [ `Todo | `Echo ]; id : Syntax.id option; span : Syntax.span }

val unfinished : (Resolve.Names.key, unfinished list) Query.query
(** Each [todo] and [echo] of a definition, in source order. *)

type hole = { offset : int; expected : string option; scope : (string * string) list }

val holes : Query.context -> Resolve.Names.key -> hole list
(** Each [todo] of a definition, with its expected type and the bindings in scope there. *)

type explanation = {
  text : string;
  meaning : string option;
  refers_to : Path.t option;
  type_ : string option;
}

val explain_at :
  path:Path.t ->
  Syntax.definition ->
  Resolve.resolved ->
  Infer.tables option ->
  text:string ->
  int ->
  explanation option
