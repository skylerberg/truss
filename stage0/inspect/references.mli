type target = Definition of Path.t | Module of Path.module_

type occurrence = { span : Syntax.span; target : target }
(** A name, in its definition's offsets, and what it refers to. *)

val declared_name : Syntax.definition -> Syntax.name option

val occurrences : (Resolve.Names.key, occurrence list) Query.query
(** Every occurrence in a definition, in order, including its own declared name. *)

val uses : (Path.file, (Path.module_ * Source.span) list) Query.query
(** Each [use] line of a file, with the module it names and the span of its path in the file's
    offsets. *)

val names_definition : Path.t -> target -> bool
(** Whether a target is the definition or, for a method, any version of it. *)
