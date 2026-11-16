module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = C_types.key
end))

module Path_table = Hashtbl.Make (Path)

type build = C_runtime.build = Development | Release
type linkage = C_runtime.linkage = External | Internal

let site_struct = C_runtime.site_struct
let version = 28

type failure = C_runtime.failure = Echo | Todo

type kind =
  | Functions of { nested : int; weight : int }
  | Static_data
  | Table_entries of Path.t option

type fragment = {
  key : Instance.key;
  kind : kind;
  functions : (string * string) list;
  definition : string;
  types : C_types.key list;
  environments : (C_types.key * C_types.defined) list;
  prototypes : (string * string) list;
  statics : string list;
  sites : Lowered.site list;
  helpers : string list;
  references : Instance.key list;
  calls : (Path.t * int) list;
  called : Instance.key list;
  failures : (failure * Lowered.site) list;
}

let key fragment = fragment.key
let references fragment = fragment.references
let called fragment = fragment.called
let failures fragment = fragment.failures

module Instance_table = Hashtbl.Make (Instance)

let walk ~lookup ~follows_only_called_entries roots =
  let visited = Instance_table.create 256 in
  let queue = Queue.create () in
  List.iter (fun root -> Queue.add (root, []) queue) roots;
  let reachable = ref [] in
  let tables = Path_table.create 16 and called_slots = Path_table.create 16 in
  let enqueue_entry table (slot, chain) =
    match List.nth_opt table.references slot with
    | Some entry -> Queue.add (entry, chain) queue
    | None ->
        Compiler_bug.raise_bug ~stage:"Emit_c" "a call of method %d of %s" slot
          (Instance.to_string table.key)
  in
  while not (Queue.is_empty queue) do
    let key, chain = Queue.pop queue in
    if not (Instance_table.mem visited key) then begin
      Instance_table.replace visited key ();
      match lookup key with
      | None -> ()
      | Some fragment -> (
          let chain = key :: chain in
          reachable := (fragment, List.rev chain) :: !reachable;
          let enqueue_references () =
            List.iter (fun reference -> Queue.add (reference, chain) queue) fragment.references
          in
          match fragment.kind with
          | Table_entries (Some capability) when follows_only_called_entries ->
              Path_table.add tables capability fragment;
              List.iter (enqueue_entry fragment)
                (List.rev (Path_table.find_all called_slots capability))
          | _ when follows_only_called_entries ->
              List.iter
                (fun (capability, slot) ->
                  if not (List.mem_assoc slot (Path_table.find_all called_slots capability)) then begin
                    Path_table.add called_slots capability (slot, chain);
                    List.iter
                      (fun table -> enqueue_entry table (slot, chain))
                      (List.rev (Path_table.find_all tables capability))
                  end)
                fragment.calls;
              enqueue_references ()
          | _ -> enqueue_references ())
    end
  done;
  List.rev !reachable

let list_linked ~lookup roots =
  List.map fst
    (walk ~lookup:(fun key -> Some (lookup key)) ~follows_only_called_entries:false roots)

let trace_reachable ~lookup roots = walk ~lookup ~follows_only_called_entries:true roots
let small = 24

let is_small fragment =
  match fragment.kind with
  | Functions { nested; weight } -> nested = 0 && weight <= small
  | Static_data | Table_entries _ -> false

let is_identifier_start character =
  character = '_' || (character >= 'a' && character <= 'z') || (character >= 'A' && character <= 'Z')

let is_identifier_part character =
  is_identifier_start character || (character >= '0' && character <= '9')

let iter_identifiers text ~identifier ~other =
  let length = String.length text in
  let rec scan position =
    if position < length then
      if is_identifier_start text.[position] then begin
        let stop = ref position in
        while !stop < length && is_identifier_part text.[!stop] do
          incr stop
        done;
        identifier (String.sub text position (!stop - position));
        scan !stop
      end
      else begin
        other text.[position];
        scan (position + 1)
      end
  in
  scan 0

let render_fragment fragment =
  let names = Hashtbl.create 64 in
  let number prefix list =
    List.iteri
      (fun position name ->
        if not (Hashtbl.mem names name) then
          Hashtbl.replace names name (Printf.sprintf "%s%d" prefix position))
      list
  in
  let self = Instance.make_symbol fragment.key in
  number "@instance_" (List.map Instance.make_symbol fragment.references);
  number "@type_"
    (List.map C_types.render_key_name
       (fragment.types
       @ List.concat_map
           (fun (_, (defined : C_types.defined)) -> defined.references)
           fragment.environments));
  number "@site_" (List.map C_runtime.render_site_symbol fragment.sites);
  let rename identifier =
    if String.starts_with ~prefix:self identifier then
      "@self"
      ^ String.sub identifier (String.length self) (String.length identifier - String.length self)
    else Option.value (Hashtbl.find_opt names identifier) ~default:identifier
  in
  let whole =
    String.concat "\n"
      (List.concat_map (fun (header, body) -> [ header; body ]) fragment.functions
      @ [ fragment.definition ]
      @ List.map
          (fun (key, (defined : C_types.defined)) ->
            C_types.render_key_name key
            ^
            match defined.definition with
            | Struct { body; _ } -> body
            | Typedef text | Code_typedef text -> text)
          fragment.environments
      @ List.map snd fragment.prototypes @ fragment.statics @ fragment.helpers)
  in
  let buffer = Buffer.create (String.length whole) in
  iter_identifiers whole
    ~identifier:(fun identifier -> Buffer.add_string buffer (rename identifier))
    ~other:(Buffer.add_char buffer);
  Buffer.contents buffer

module Builder = Builder

let render_bytes_definition (text, name) =
  let bytes =
    List.init (String.length text) (fun index -> string_of_int (Char.code text.[index]))
  in
  Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
    (max 1 (String.length text))
    (if bytes = [] then "0" else String.concat ", " bytes)

let name_bytes context ~texts =
  let named = Hashtbl.create 64 in
  List.iter
    (fun text ->
      iter_identifiers text
        ~identifier:(fun identifier -> Hashtbl.replace named identifier ())
        ~other:ignore)
    texts;
  Hashtbl.fold (fun text index entries -> (index, text) :: entries) context.bytes []
  |> List.sort compare
  |> List.filter_map (fun (index, text) ->
      let name = C_values.render_bytes_symbol context index in
      if Hashtbl.mem named name then Some (render_bytes_definition (text, name)) else None)

type compiled = Code of Builder.instance | Data of Lowered.data | Table of Lowered.table

let make_fragment env (compiled : compiled) =
  let key, context =
    match compiled with
    | Code code -> (code.C_instance.key, code.context)
    | Data data -> (data.data_key, C_types.make_context env (Instance.make_symbol data.data_key))
    | Table table ->
        (table.table_key, C_types.make_context env (Instance.make_symbol table.table_key))
  in
  let functions, definition, kind =
    match compiled with
    | Code code ->
        let nested = List.sort compare code.nested in
        ( List.map snd nested @ [ code.own ],
          "",
          Functions { nested = List.length nested; weight = code.weight } )
    | Data data -> ([], C_data.render_data context data, Static_data)
    | Table table -> ([], C_data.render_table context table, Table_entries table.capability)
  in
  let types = List.rev context.order in
  let environments =
    List.filter_map
      (fun key ->
        match key with C_types.Environment _ -> Some (key, C_types.define context key) | _ -> None)
      types
  in
  {
    key;
    kind;
    functions;
    definition;
    types = List.filter (function C_types.Environment _ -> false | _ -> true) types;
    environments;
    prototypes = List.rev context.prototypes;
    statics =
      name_bytes context ~texts:(definition :: List.map snd functions) @ List.rev context.statics;
    sites = List.sort_uniq compare context.sites;
    helpers = context.helpers_used;
    references =
      (match compiled with
      | Table table -> List.map fst table.entries
      | Code _ | Data _ ->
          List.filter (fun other -> not (Instance.equal other key)) (List.rev context.instances));
    calls = List.rev context.calls;
    called = List.rev context.called;
    failures = List.rev context.failures;
  }

let render_file env build (fragments : (fragment * linkage) list) =
  let context = C_types.make_context env "" in
  let local_types = Key_table.create 16 in
  List.iter
    (fun ((fragment : fragment), _) ->
      List.iter (C_types.register context) fragment.types;
      List.iter
        (fun (key, (defined : C_types.defined)) ->
          Key_table.replace local_types key defined;
          C_types.register context key;
          List.iter (C_types.register context) defined.references)
        fragment.environments)
    fragments;
  let linkage_text = function Internal -> "static inline " | External -> "" in
  let own =
    List.concat_map
      (fun ((fragment : fragment), linkage) ->
        let count = List.length fragment.functions in
        List.mapi
          (fun position (header, body) ->
            let linkage = if position < count - 1 then Internal else linkage in
            (linkage_text linkage ^ header, body))
          fragment.functions)
      fragments
  in
  let symbol_of header =
    let before = String.sub header 0 (String.index header '(') in
    match String.rindex_opt before ' ' with
    | Some space -> String.sub before (space + 1) (String.length before - space - 1)
    | None -> before
  in
  let declared = Hashtbl.create 64 in
  let declarations = Buffer.create 4096 in
  List.iter
    (fun (header, _) ->
      Hashtbl.replace declared (symbol_of header) ();
      Buffer.add_string declarations (header ^ ";\n"))
    own;
  List.iter
    (fun ((fragment : fragment), _) ->
      List.iter
        (fun (symbol, declaration) ->
          if not (Hashtbl.mem declared symbol) then begin
            Hashtbl.replace declared symbol ();
            Buffer.add_string declarations declaration
          end)
        fragment.prototypes)
    fragments;
  let definitions = ref C_types.Keys.empty in
  let define_key key =
    match Key_table.find_opt local_types key with
    | Some defined -> defined
    | None -> C_types.define context key
  in
  let rec close () =
    let pending =
      List.filter (fun key -> not (C_types.Keys.mem key !definitions)) (List.rev context.order)
    in
    if pending <> [] then begin
      List.iter
        (fun key -> definitions := C_types.Keys.add key (define_key key) !definitions)
        pending;
      close ()
    end
  in
  close ();
  let keys = List.rev context.order in
  let defined key = C_types.Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer C_runtime.runtime_declarations;
  Buffer.add_string buffer
    (match build with
    | Development -> "#define T_UNREACHABLE() t_runtime_compiler_bug()\n"
    | Release -> "#define T_UNREACHABLE() __builtin_unreachable()\n");
  let helpers_used =
    List.sort_uniq String.compare
      (context.helpers_used
      @ List.concat_map (fun ((fragment : fragment), _) -> fragment.helpers) fragments)
  in
  List.iter
    (fun (name, text) -> if List.mem name helpers_used then Buffer.add_string buffer text)
    C_runtime.helpers;
  List.iter
    (fun key ->
      match (defined key).definition with
      | Struct _ ->
          Buffer.add_string buffer
            (Printf.sprintf "typedef struct %s %s;\n" (C_types.render_key_name key)
               (C_types.render_key_name key))
      | Typedef _ | Code_typedef _ -> ())
    keys;
  let emitted = ref C_types.Keys.empty in
  let rec emit_typedef key =
    if not (C_types.Keys.mem key !emitted) then
      match (defined key).definition with
      | Struct _ -> ()
      | (Typedef _ | Code_typedef _) as definition ->
          emitted := C_types.Keys.add key () !emitted;
          List.iter emit_typedef (defined key).references;
          Buffer.add_string buffer
            (match definition with
            | Typedef c_type ->
                Printf.sprintf "typedef %s %s;\n" c_type (C_types.render_key_name key)
            | Code_typedef text -> text
            | Struct _ -> "")
  in
  List.iter emit_typedef keys;
  let rec emit key =
    if not (C_types.Keys.mem key !emitted) then begin
      emitted := C_types.Keys.add key () !emitted;
      match (defined key).definition with
      | Struct { body; holds } ->
          List.iter emit holds;
          Buffer.add_string buffer
            (Printf.sprintf "struct %s {\n%s};\n" (C_types.render_key_name key) body)
      | Typedef _ | Code_typedef _ -> ()
    end
  in
  List.iter emit keys;
  List.iter
    (fun key ->
      let layout =
        match key with
        | C_types.Type ty -> Some (Memory_layout.of_type env ty)
        | Block (ty, variant) -> Some (Memory_layout.lay_out_block env ty variant)
        | Code _ | Environment _ | Evidence _ -> None
      in
      Option.iter
        (fun (layout : Memory_layout.t) ->
          Buffer.add_string buffer
            (Printf.sprintf "_Static_assert(sizeof(%s) == %d && _Alignof(%s) == %d, \"layout\");\n"
               (C_types.render_key_name key) layout.size (C_types.render_key_name key)
               layout.alignment))
        layout)
    keys;
  List.iter
    (fun site ->
      Buffer.add_string buffer
        (Printf.sprintf "extern const struct t_site %s;\n" (C_runtime.render_site_symbol site)))
    (List.sort_uniq compare
       (List.concat_map (fun ((fragment : fragment), _) -> fragment.sites) fragments));
  Buffer.add_buffer buffer declarations;
  List.iter
    (fun ((fragment : fragment), _) -> List.iter (Buffer.add_string buffer) fragment.statics)
    fragments;
  List.iter
    (fun ((fragment : fragment), _) -> Buffer.add_string buffer fragment.definition)
    fragments;
  List.iter (fun (header, body) -> Buffer.add_string buffer (header ^ body)) own;
  Buffer.contents buffer

type position = { file : string; line : int; column : int }

let render_sites_file ~position:resolve fragments =
  let positions =
    List.map
      (fun site -> (site, resolve site))
      (List.sort_uniq compare (List.concat_map (fun fragment -> fragment.sites) fragments))
  in
  let file_symbols =
    List.mapi
      (fun index file -> (file, Printf.sprintf "t_file_%d" index))
      (List.sort_uniq String.compare
         (List.map (fun (_, (position : position)) -> position.file) positions))
  in
  String.concat ""
    ((C_runtime.runtime_declarations :: List.map render_bytes_definition file_symbols)
    @ List.map
        (fun (site, (position : position)) ->
          Printf.sprintf "const struct t_site %s = { %s, %d, %d, %d };\n"
            (C_runtime.render_site_symbol site)
            (List.assoc position.file file_symbols)
            (String.length position.file) position.line position.column)
        positions)

module For_testing = struct
  let c fragment =
    String.concat ""
      (List.map (fun (header, body) -> header ^ body) fragment.functions @ [ fragment.definition ])
end
