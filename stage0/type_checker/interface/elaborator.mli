type t

val create :
  Lookups.t -> Resolve.resolved -> spans:Source.Definition_span.t array -> Environment.scope -> t

val read_span : t -> Syntax.id -> Source.Definition_span.t
val list_bounds : t -> Types.parameter -> Types.trait_reference list
val find_self_type : t -> Types.ty option
val list_diagnostics : t -> Diagnostic.in_definition list
val list_named_types : t -> (Syntax.id * Types.ty) list

val record_diagnostic :
  Diagnostic.in_definition list ref ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  Diagnostic.reported

val list_trait_closure : Lookups.t -> Path.t -> Path.t list
val show_path : Syntax.path -> string
val elaborate_type : t -> Syntax.type_expression -> Types.ty

val elaborate_header :
  Lookups.t -> Resolve.Names.key -> (Environment.header, Diagnostic.in_definition list) result

val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
