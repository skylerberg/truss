val derive :
  read_hash_and_references:(Instance.key -> string * Instance.key list) ->
  read_known_key:(Instance.key -> string) ->
  Instance.key list ->
  (Instance.key * string) list
