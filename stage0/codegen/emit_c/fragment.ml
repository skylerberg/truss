type kind =
  | Functions of { nested : int; weight : int }
  | Static_data
  | Table_entries of Path.t option

type t = {
  item : Lowered.Item.t;
  kind : kind;
  functions : (string * string) list;
  definition : string;
  types : C_types.key list;
  environments : (C_types.key * C_types.defined) list;
  prototypes : (string * string) list;
  statics : string list;
  sites : Lowered.site list;
  helpers : string list;
  references : Lowered.Item.t list;
  calls : (Path.t * int) list;
  called : Lowered.Item.t list;
  failures : (C_runtime.failure * Lowered.site) list;
}

let is_identifier_start character =
  character = '_' || (character >= 'a' && character <= 'z') || (character >= 'A' && character <= 'Z')

let is_identifier_part character =
  is_identifier_start character || (character >= '0' && character <= '9')

let iter_identifiers text ~on_identifier ~on_other =
  let length = String.length text in
  let rec scan position =
    if position < length then
      if is_identifier_start text.[position] then begin
        let stop = ref position in
        while !stop < length && is_identifier_part text.[!stop] do
          incr stop
        done;
        on_identifier (String.sub text position (!stop - position));
        scan !stop
      end
      else begin
        on_other text.[position];
        scan (position + 1)
      end
  in
  scan 0

let name_bytes (emission : Emission.t) ~texts =
  let named = Hashtbl.create 64 in
  List.iter
    (fun text ->
      iter_identifiers text
        ~on_identifier:(fun identifier -> Hashtbl.replace named identifier ())
        ~on_other:ignore)
    texts;
  Hashtbl.fold (fun text index entries -> (index, text) :: entries) emission.bytes []
  |> List.sort compare
  |> List.filter_map (fun (index, text) ->
      let name = Emission.render_bytes_symbol emission index in
      if Hashtbl.mem named name then Some (C_values.render_bytes_definition (text, name)) else None)

let make (emission : Emission.t) ~item ~kind ~functions ~definition ~references =
  let type_keys = List.rev emission.types.order in
  let environments =
    List.filter_map
      (fun key ->
        match key with
        | C_types.Environment _ -> Some (key, C_types.define emission.types key)
        | _ -> None)
      type_keys
  in
  {
    item;
    kind;
    functions;
    definition;
    types = List.filter (function C_types.Environment _ -> false | _ -> true) type_keys;
    environments;
    prototypes = List.rev emission.prototypes;
    statics =
      name_bytes emission ~texts:(definition :: List.map snd functions) @ List.rev emission.statics;
    sites = List.sort_uniq compare emission.sites;
    helpers = emission.types.helpers_used;
    references;
    calls = List.rev emission.calls;
    called = List.rev emission.called;
    failures = List.rev emission.failures;
  }
