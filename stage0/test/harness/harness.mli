val test : string -> (unit -> unit) -> unit
val always : string -> (unit -> unit) -> unit
val wanted : string -> bool
val fail : ('a, unit, string, unit) format4 -> 'a
val with_environment : (string * string) list -> (unit -> 'a) -> 'a
val scratch : string -> string
val write_files : string -> (string * string) list -> unit
val expect_string : expected:string -> string -> unit
val expect_strings : expected:string list -> string list -> unit
val markdown_documents : unit -> string list
val truss_files : unit -> string list
val workspace_path : string -> string
