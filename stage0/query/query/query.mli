type context = Incremental.context
type part = Incremental.part = Tree | Resolved | Interface | Shape | Signature | Body | Ownership
type subject = Incremental.subject = { path : Path.t; part : part }

val show_part : part -> string

type ('key, 'value) input = ('key, 'value) Incremental.input

val input :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  unit ->
  ('key, 'value) input

type phase

val phase : name:string -> after:phase list -> phase
val phase_rank : phase -> int

type ('key, 'value) query = ('key, 'value) Incremental.query

val query :
  name:string ->
  show:('key -> string) ->
  phase:phase ->
  ?saved:bool ->
  ?portable:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query

val recursive_query :
  name:string ->
  show:('key -> string) ->
  phase:phase ->
  ?saved:bool ->
  ?portable:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (('key, 'value) query -> context -> 'key -> 'value) ->
  ('key, 'value) query

val find : context -> ('key, 'value) input -> 'key -> 'value option
val demand : context -> ('key, 'value) query -> 'key -> 'value

exception Cycle of string list
