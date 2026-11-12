val input :
  name:string ->
  show:('a -> string) ->
  ?equal:('b -> 'b -> bool) ->
  ?about:('a -> Nodes.subject option) ->
  unit ->
  ('a, 'b) Nodes.input

val read : Nodes.context -> ('key, 'value) Nodes.input -> 'key -> 'value option
val set : Nodes.t -> ('key, 'value) Nodes.input -> 'key -> 'value -> unit
val remove : Nodes.t -> ('key, 'value) Nodes.input -> 'key -> unit

val query :
  name:string ->
  show:('a -> string) ->
  phase:int ->
  ?saved:bool ->
  ?portable:bool ->
  ?equal:('b -> 'b -> bool) ->
  ?about:('a -> Nodes.subject option) ->
  (Nodes.context -> 'a -> 'b) ->
  ('a, 'b) Nodes.query

val demand : Nodes.context -> ('key, 'value) Nodes.query -> 'key -> 'value
val observed_node : Nodes.t -> ('key, 'value) Nodes.query -> 'key -> Nodes.node
val known : Nodes.context -> ('key, 'value) Nodes.query -> 'key -> 'value option
