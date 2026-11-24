val at : Core.origin -> Nodes.node Description.location
val over : Core.origin Description.range -> Nodes.node Description.location
val quote : Core.origin -> Nodes.node Description.piece
val quote_over : Core.origin Description.range -> Nodes.node Description.piece
val after : Core.origin -> Nodes.node Description.location
val replace : Core.origin -> Nodes.node Description.piece list -> Nodes.node Description.edit
val insert_before : Core.origin -> Nodes.node Description.piece list -> Nodes.node Description.edit
val insert_after : Core.origin -> Nodes.node Description.piece list -> Nodes.node Description.edit

val delete :
  Core.origin Description.boundary ->
  Core.origin Description.boundary ->
  Nodes.node Description.edit

val remove_entry :
  Core.origin Description.range -> Core.origin Description.siblings -> Nodes.node Description.edit

val remove_lines : Core.origin Description.range -> Nodes.node Description.edit

val list_spelling_fixes :
  Core.origin -> written:string -> string list -> Nodes.node Description.fix list

val write_hidden : Path.t -> Language.Visibility.t -> string
val describe_call : Core.origin -> Nodes.node Description.piece list

val add_lines_after :
  Core.origin -> Nodes.node Description.piece list list -> Nodes.node Description.edit

val show_field_path : string -> string list -> string
val show_function_name : Path.t -> string
