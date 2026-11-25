type file_diagnostic =
  | Syntax of Syntax_catalog.Syntax_diagnostic.t
  | Import of Catalog.Resolve.import

type placed = { file : Path.file; base : int; stop : int; spans : Source.Definition_span.t array }
type lookups = { read_placed : Resolve.Names.key -> placed; read_file_text : Path.file -> string }

val render_description : lookups -> Resolve.Names.key -> Catalog.description -> Diagnostic.t
val render : lookups -> Resolve.Names.key -> Catalog.diagnostic -> Diagnostic.t
val locate : lookups -> Resolve.Names.key -> Core.origin -> Source.span
val describe_file_diagnostic : file_diagnostic -> Source.span Description.t
val render_file_diagnostic : text:string -> file_diagnostic -> Diagnostic.t
