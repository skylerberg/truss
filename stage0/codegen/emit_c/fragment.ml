let ( ++ ) = C_text.( ++ )

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

let is_environment : C_text.key -> bool = function Environment _ -> true | _ -> false

let resolve ~prefix ~name_item ~name_type ~name_site ~name_local : C_text.reference -> string =
  function
  | Item item -> name_item item
  | Type_name key -> name_type key
  | Site site -> name_site site
  | Local local -> name_local local
  | Byte_constant index -> Printf.sprintf "%s_bytes_%d" prefix index
  | Nested_function index -> Printf.sprintf "%s_Nested_%d" prefix index
  | Nested_body index -> Printf.sprintf "%s_Nested_%d_body" prefix index
  | Static index -> Printf.sprintf "%s_static_%d" prefix index
  | Helper helper -> C_runtime.render_helper_name helper
  | Capability capability -> C_runtime.render_capability_symbol capability

let raise_local_outside_function local =
  C_runtime.raise_bug "local %d is named outside the function that holds it" local

let make (emission : Emission.t) ~kind ~references ~functions ~definition =
  let item = emission.item in
  let resolve =
    resolve ~prefix:(Mangling.make_symbol item) ~name_item:Mangling.make_symbol
      ~name_type:C_text.render_key_name ~name_site:C_runtime.render_site_symbol
  in
  let render_outside text =
    C_text.render text ~resolve:(resolve ~name_local:raise_local_outside_function)
  in
  let type_keys = C_types.list_keys emission.types in
  let functions =
    List.map
      (fun (pieces : function_pieces) : function_text ->
        let resolve = resolve ~name_local:pieces.name_local in
        {
          symbol = resolve pieces.symbol;
          header = C_text.render pieces.header ~resolve;
          opening = pieces.opening;
          body = C_text.render_segments pieces.body ~site:pieces.opening ~resolve;
        })
      functions
  and definition = render_outside definition
  and environments =
    List.filter_map
      (fun key ->
        if is_environment key then
          Some (key, C_types.map_defined render_outside (C_types.define emission.types key))
        else None)
      type_keys
  and prototypes =
    List.rev_map
      (fun (symbol, declaration) -> (render_outside symbol, render_outside declaration))
      emission.prototypes
  and statics =
    List.map render_outside
      (List.map
         (fun (index, text) ->
           Text "static const uint8_t " ++ Name (Byte_constant index)
           ++ Text (C_values.render_bytes_initializer text ^ ";\n"))
         (Emission.list_bytes emission)
      @ List.rev emission.statics)
  in
  {
    item;
    kind;
    functions;
    definition;
    types = List.filter (fun key -> not (is_environment key)) type_keys;
    environments;
    prototypes;
    statics;
    sites = List.sort_uniq compare emission.sites;
    capabilities = List.sort_uniq Path.compare emission.capabilities;
    helpers = emission.helpers_used;
    references;
    calls = List.rev emission.calls;
    called = List.rev emission.called;
    failures = List.rev emission.failures;
    hash =
      Blake3.derive_key ~context:"truss 2026-11-23 item fragment hash"
        (String.concat "\n"
           (List.concat_map
              (fun (text : function_text) ->
                text.header :: List.map (fun (segment : C_text.segment) -> segment.text) text.body)
              functions
           @ definition
             :: List.concat_map
                  (fun (key, (defined : string C_types.defined)) ->
                    [
                      C_text.render_key_name key;
                      (match defined.definition with
                      | Struct { body; _ } | Typedef body | Code_typedef body -> body);
                    ])
                  environments
           @ List.map snd prototypes @ statics));
  }
