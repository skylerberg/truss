val test : string -> (unit -> unit) -> unit
val always : string -> (unit -> unit) -> unit
val wanted : string -> bool
val fail : ('a, unit, string, unit) format4 -> 'a
val expect_results_current : Engine.t -> unit

val expect_not_recomputed :
  Engine.t ->
  first:(unit -> unit) ->
  again:(unit -> unit) ->
  ('key, 'value) Query.query ->
  'key list ->
  unit

val scratch : string -> string
val write_files : string -> (string * string) list -> unit
val git : string -> string list -> unit
val expect_string : expected:string -> string -> unit
val expect_strings : expected:string list -> string list -> unit
val markdown_documents : unit -> string list
val truss_files : unit -> string list
val workspace_path : string -> string
