type t
type schema = Main | Attached of string
type cell = Sql.argument = Blob of string | Text of string | Integer of int | Null

val identify : string -> int
val create_memory : unit -> t
val open_file : string -> t
val copy : t -> t
val copy_file : string -> t
val save : t -> into:string -> unit
val attach : t -> string -> schema
val detach : t -> string -> unit
val list_attached : t -> string list
val locate_attached : t -> string -> schema option
val replace_routes : t -> (Path.package * schema) list -> unit
val list_project : t -> Path.package list
val replace_project : t -> Path.package list -> unit
val locate_schema : t -> Path.package -> schema
val commit : t -> unit
val close : t -> unit
val close_uncommitted : t -> unit
val find_meta : t -> string -> string option
val write_meta : t -> string -> string -> unit

type fact

val make_fact :
  table:string -> id_column:string -> fixed:(string * cell) list -> columns:string list -> fact

type 'row current = Current of 'row | Absent | Stale

val guard_fact : fact -> table:string -> id_column:string -> fact
val find_fact : t -> schema -> fact -> id:int -> stages:int list -> cell array current
val find_stored_fact : t -> fact -> id:int -> cell array option
val replace_fact : t -> fact -> id:int -> cell list -> unit
val remove_fact : t -> fact -> id:int -> unit

type diagnostic = {
  definition : int option;
  file : int option;
  is_error : bool;
  code : string;
  detail : string;
}

val has_diagnostic : t -> stage:int -> unit:int -> bool
val mark_reported_units_stale : t -> stage:int -> unit
val replace_diagnostics : t -> stage:int -> unit:int -> package:string -> diagnostic list -> bool
val has_unchecked_body : t -> package:string -> skipped_kind:int option -> bool

val list_code_packages :
  t -> package:string -> unit_kind:int -> target_kind:int -> test_kind:int -> string list option

val find_definition_key_anywhere : t -> id:int -> string option

type endpoint = { kind : int; id : int; name : string }
type edge = { target : endpoint; markers : int }

val list_edges : t -> schema -> source:endpoint -> edge list

type edge_change = { changed : endpoint; before : int; after : int }

val replace_edges : t -> source:endpoint -> edge list -> edge_change list
val has_source : t -> target:endpoint -> source_kind:int -> markers:int -> bool
val list_sources : t -> target:endpoint -> markers:int -> endpoint list
val list_definitions_naming : t -> target:endpoint -> markers:int -> string list
val list_names_of_edges_into : t -> kind:int -> id:int -> markers:int -> string list
val has_unresolved : t -> file:int -> bool
val mark_sources_stale : t -> target:endpoint -> markers:int -> unit

val mark_stage_of_sources_stale :
  t -> target:endpoint -> source_kind:int -> markers:int -> stage:int -> unit

val mark_position_holders_stale : t -> target:endpoint -> markers:int -> stages:int -> unit

type proof_graph = { unit_kind : int; node_kind : int; markers : int }
type proof_edge = { source : int; target : int; markers : int }

val list_cycle_nodes : t -> proof_graph -> seeds:int list -> int list
val list_proof_edges : t -> proof_graph -> nodes:int list -> proof_edge list

type read_edge = { source_kind : int; source : int; target_kind : int; target : int }

val list_edges_from :
  t -> schema -> source_kinds:int list -> sources:int list -> markers:int -> read_edge list

val list_edges_into :
  t -> target_kinds:int list -> targets:int list -> markers:int -> read_edge list

val list_definitions_identified : t -> ids:int list -> (int * int * string) list
val mark_paths_stale : t -> stage:int -> paths:int list -> unit
val list_keys_of_paths : t -> paths:int list -> (int * string) list
val mark_groups_stale : t -> stage:int -> path:int -> unit

type item = { id : int; key : string; label : string; definition : int option }

val insert_item : t -> item -> bool
val find_item_key : t -> id:int -> string option
val list_item_keys : t -> string list
val remove_item : t -> id:int -> unit

type item_graph = {
  lower_kind : int;
  evaluate_kind : int;
  item_kind : int;
  references : int;
  claims : int;
  claim_kinds : int list;
}

val mark_items_stale : t -> stage:int -> unit

type linked = {
  linked_id : int;
  linked_key : string;
  sites : string option;
  text_hash : string option;
  is_unevaluated : bool;
  is_unit_stale : bool;
}

val list_linked : t -> item_graph -> profile:int -> unit_kind:int -> roots:int list -> linked list

type claim_edges = Every_edge | Settled_edges of { packages : string list option }

val is_item_claimed : t -> item_graph -> item:int -> over:claim_edges -> bool

val list_claimed_among :
  t -> item_graph -> items:int list -> packages:string list option -> int list

val merge : string list -> into:string -> unit

type placed = { file : string; base : int; stop : int; spans : string }

type located = {
  stage : int;
  definition : (string * placed) option;
  is_in_test : bool;
  detail : string;
}

val list_file_diagnostics : t -> schema -> file:int -> test_kind:int -> located list
val has_error : t -> package:string -> last_stage:int -> hidden_stage:int option -> bool

type scope = Everything | Packages of string list | Files of int list

val find_unproven_definition : t -> scope:scope -> origin:int -> string option

type hole = { home : int; location : string }

val list_holes : t -> schema -> definition:int -> hole list
val replace_holes : t -> definition:int -> hole list -> unit

type verdict = {
  code : string;
  site : string;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : string option;
}

val list_file_verdicts : t -> file:int -> (string * placed * verdict) list
val find_placed : t -> schema -> definition:int -> placed option
val replace_verdicts : t -> definition:int -> verdict list -> bool

type solver_run = { input_hash : string; output : string }

val list_solver_runs : t -> definition:int -> solver_run list
val replace_solver_runs : t -> definition:int -> solver_run list -> unit

val list_differing_rows :
  t ->
  table:string ->
  columns:string list ->
  before:schema option ->
  after:schema option ->
  cell array list

val mark_readers_of_targets : t -> targets:endpoint list -> markers:int -> unit

val list_unread :
  t ->
  table:string ->
  id_column:string ->
  section:int option ->
  target_kinds:int list ->
  string list

val count_differing_rows : t -> other:schema -> (string * int) list
val keep_for_dependents : t -> markers:int -> unit
val mark_stale : t -> stage:int -> id:int -> unit
val unmark_stale : t -> stage:int -> id:int -> bool
val is_stale : t -> stage:int -> id:int -> bool

type unit_entity =
  | File_unit
  | Module_unit
  | Definition_unit
  | Path_unit
  | Dependency_unit
  | Item_unit

val list_stale : t -> stage:int -> entity:unit_entity -> scope:scope -> int list

type entry = {
  file : int;
  position : int;
  module_ : int;
  file_name : string;
  name : string;
  kind : int;
  visibility : int;
  is_generic : bool;
}

val list_file_entries : t -> file:int -> entry list
val replace_file_entries : t -> file:int -> entry list -> unit
val find_entry : t -> schema -> module_:int -> name:string -> entry option
val list_module_entries : t -> schema -> module_:int -> entry list

type definition = {
  id : int;
  key : string;
  package : string;
  module_ : int;
  path : int;
  ordinal : int;
  name : string;
  owner : int option;
  member : string option;
  kind : int;
  visibility : int;
  is_generic : bool;
  origin : int;
  synthesized_from : int option;
  container : int option;
  file : int option;
  position : int option;
  base : int option;
  stop : int option;
  text_hash : int option;
}

type selection =
  | Of_module of int
  | Of_file of int
  | Of_package of string
  | Of_container of int
  | Of_path of int

val find_definition : t -> schema -> id:int -> definition option
val list_definitions : t -> schema -> selection -> definition list

val find_source_definition :
  t -> target:endpoint -> source_kind:int -> markers:int -> from_:int -> definition option

val list_target_definitions :
  t -> source:endpoint -> target_kind:int -> markers:int -> origin:int -> (definition * int) list

val list_package_member_keys :
  t -> schema -> package:string -> member:string -> kind:int -> origin:int -> string list

val replace_definition : t -> definition -> unit
val remove_definition : t -> id:int -> unit

type syntax = { tree : string; spans : string; syntax_errors : string }

val find_syntax : t -> schema -> definition:int -> syntax option
val find_tree : t -> schema -> definition:int -> string option
val find_spans : t -> schema -> definition:int -> string option
val find_syntax_errors : t -> schema -> definition:int -> string option
val replace_syntax : t -> definition:int -> syntax -> unit

type dependency = { id : int; package : string; dependency : string; capabilities : string }

val replace_package : t -> name:string -> id:int -> dependencies:dependency list -> unit
val remove_package : t -> name:string -> unit
val list_packages : t -> schema -> string list
val list_dependencies : t -> schema -> package:string -> dependency list
val find_dependency : t -> id:int -> dependency option

type file = {
  id : int;
  package : string;
  module_ : int;
  name : string;
  key : string;
  text : string;
}

val find_file : t -> schema -> id:int -> file option
val list_files : t -> schema -> selection -> file list
val replace_file : t -> file -> unit
val remove_file : t -> id:int -> unit
val list_imports : t -> schema -> file:int -> (string * string) list
val replace_imports : t -> file:int -> (string * string) list -> unit

type impl = {
  definition : int;
  module_ : int;
  position : int;
  trait : int;
  type_ : int;
  entry : string;
}

type impl_selection = Impls_of_trait of int | Impls_of_type of int | Impls_of_module of int

val list_impls : t -> schema -> package:string -> impl_selection -> impl list
val replace_module_impls : t -> package:string -> module_:int -> impl list -> unit

type law_proof = { definition : int; module_ : int; trait : int; law : string; type_ : int }

val list_law_proofs :
  t -> schema -> package:string -> trait:int -> law:string -> type_:int -> int list

val replace_module_law_proofs :
  t -> package:string -> module_:int -> law_proof list -> law_proof list

val has_module : t -> schema -> module_:int -> bool
val find_place : t -> schema -> definition:int -> (string * int) option
val find_file_order : t -> schema -> definition:int -> (string * int) option
val find_text : t -> schema -> definition:int -> string option
val find_definition_key : t -> schema -> id:int -> string option
val list_member_keys : t -> schema -> owner:int -> member:string -> origin:int -> string list

type declared = { kind : int; visibility : int; is_generic : bool }

val find_declared : t -> schema -> id:int -> declared option

type placement = { file : int option; container : int option }

val find_placement : t -> schema -> id:int -> placement option

val list_containers_of_member :
  t ->
  schema ->
  package:string ->
  member:string ->
  container_kind:int ->
  (string * string * int) list

val replace_module : t -> id:int -> package:string -> name:string -> key:string -> unit
val remove_module : t -> id:int -> unit
val find_module_key : t -> schema -> id:int -> string option
