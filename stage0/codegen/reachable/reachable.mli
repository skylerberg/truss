val reachable :
  lookup:(Instance.key -> Emit_c.fragment) -> Instance.key list -> Emit_c.fragment list

val running :
  lookup:(Instance.key -> Emit_c.fragment) ->
  Instance.key list ->
  (Emit_c.fragment * Instance.key list) list

val own_hash : Emit_c.fragment -> string

module Keys : Map.S with type key = Instance.key

val reach_keys :
  link:(Instance.key -> string * Instance.key list) ->
  known:(Instance.key -> string option) ->
  Instance.key ->
  (Instance.key * string) list
