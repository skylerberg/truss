open Description
open Nodes

val at : Core.origin -> node location
val over : Core.origin range -> node location
val quote : Core.origin -> node piece
val quote_over : Core.origin range -> node piece
val after : Core.origin -> node location
val replace : Core.origin -> node piece list -> node edit
val insert_before : Core.origin -> node piece list -> node edit
val insert_after : Core.origin -> node piece list -> node edit
val delete : Core.origin boundary -> Core.origin boundary -> node edit
val remove_entry : Core.origin range -> Core.origin siblings -> node edit
val remove_lines : Core.origin range -> node edit
val list_spelling_fixes : Core.origin -> written:string -> string list -> node fix list
val write_hidden : Path.t -> Language.Visibility.t -> string
val describe_call : Core.origin -> node piece list
val add_lines_after : Core.origin -> node piece list list -> node edit
val example_names : string list
val example : string -> Core.origin
val find_example_name : Core.origin -> string option
val example_module : Path.module_
val example_package : Path.package
val example_path : Path.t
val example_key : Path.key
val example_type : Types.ty
val example_trait : Types.trait_reference
val example_capability : Types.capability
val example_condition : Types.condition
