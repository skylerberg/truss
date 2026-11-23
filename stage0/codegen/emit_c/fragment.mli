type kind = Functions of { nested : int; weight : int } | Static_data | Table_entries of Path.t

type function_text = {
  symbol : string;
  header : string;
  opening : Lowered.site option;
  body : C_text.segment list;
}

type function_pieces = {
  symbol : C_text.reference;
  header : C_text.t;
  opening : Lowered.site option;
  body : C_text.t;
  name_local : Lowered.local -> string;
}

type t = {
  item : Lowered.Item.t;
  kind : kind;
  functions : function_text list;
  definition : string;
  types : C_text.key list;
  environments : (C_text.key * string C_types.defined) list;
  prototypes : (string * string) list;
  statics : string list;
  sites : Lowered.site list;
  capabilities : Path.t list;
  helpers : C_runtime.helper list;
  references : Lowered.Item.t list;
  calls : (Path.t * int) list;
  called : Lowered.Item.t list;
  failures : (C_runtime.failure * Lowered.site) list;
  hash : string;
}

val make :
  Emission.t ->
  kind:kind ->
  references:Lowered.Item.t list ->
  functions:function_pieces list ->
  definition:C_text.t ->
  t
