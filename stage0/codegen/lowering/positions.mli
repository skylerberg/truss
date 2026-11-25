type t
type location = { file : Path.file; line : int; column : int }

val create :
  Resolve.Names.lookups -> source:Resolve.Names.source -> read_source:(Path.file -> Source.t) -> t

val locate : t -> Path.t -> int -> location
val locate_site : t -> Lowered.site -> location
