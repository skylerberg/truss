val test : string -> (unit -> unit) -> unit
val test_always : string -> (unit -> unit) -> unit
val share : (int * int) option
val is_wanted : string -> bool
val fail : ('a, unit, string, 'b) format4 -> 'a
val make_scratch_directory : string -> string
val write_files : string -> (string * string) list -> unit
val expect_string : expected:string -> string -> unit
val expect_strings : expected:string list -> string list -> unit
val list_markdown_documents : unit -> string list
val list_truss_files : unit -> string list
val make_workspace_path : string -> string
