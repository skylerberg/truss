(* Every instance reachable from the roots, roots first, each once, in the
   order it is first reached. [lookup] gives an instance's compiled form. *)
val reachable :
  lookup:(Instance.key -> Emit_c.fragment) -> Instance.key list -> Emit_c.fragment list

val running :
  lookup:(Instance.key -> Emit_c.fragment) ->
  Instance.key list ->
  (Emit_c.fragment * Instance.key list) list

(* The hash of an instance's C, by itself, with each name it holds written as
   a number, as {!Emit_c.text} writes it. It holds no name, so renaming or
   moving a definition changes no hash. *)
val own_hash : Emit_c.fragment -> string

module Keys : Map.S with type key = Instance.key

val groups :
  edges:(Instance.key -> Instance.key list) -> Instance.key list -> Instance.key list Keys.t

(* The key of everything an instance that is in no group can reach: its own
   hash, and the key of each instance it refers to, in order. *)
val unit_key : own:string -> string list -> string

val group_key :
  link:(Instance.key -> string * Instance.key list) ->
  deep:(Instance.key -> string) ->
  members:Instance.key list ->
  Instance.key ->
  string
