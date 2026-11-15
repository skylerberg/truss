val reachable :
  lookup:(Instance.key -> Emit_c.fragment) -> Instance.key list -> Emit_c.fragment list

val running :
  lookup:(Instance.key -> Emit_c.fragment) ->
  Instance.key list ->
  (Emit_c.fragment * Instance.key list) list

val own_hash : Emit_c.fragment -> string

module Keys : Map.S with type key = Instance.key

val component_keys :
  link:(Instance.key -> string * Instance.key list) ->
  deep:(Instance.key -> string) ->
  Instance.key list ->
  (Instance.key * string) list
