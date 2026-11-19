val derive :
  read_hash_and_references:(Lowered.Item.t -> string * Lowered.Item.t list) ->
  read_known_key:(Lowered.Item.t -> string) ->
  Lowered.Item.t list ->
  (Lowered.Item.t * string) list
