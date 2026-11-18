module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = C_types.key
end))

module Path_table = Hashtbl.Make (Path)

type profile = Development | Release
type linkage = C_runtime.linkage = External | Internal

let site_structs = C_runtime.site_structs
let version = 28

type failure = C_runtime.failure = Echo | Todo
type fragment = Fragment.t

let item (fragment : fragment) = fragment.item
let references (fragment : fragment) = fragment.references
let called (fragment : fragment) = fragment.called
let failures (fragment : fragment) = fragment.failures

module Item_table = Hashtbl.Make (Lowered.Item)

let walk ~lookup ~follows_only_called_entries roots =
  let visited = Item_table.create 256 in
  let queue = Queue.create () in
  List.iter (fun root -> Queue.add (root, []) queue) roots;
  let reachable = ref [] in
  let tables = Path_table.create 16 and called_slots = Path_table.create 16 in
  let enqueue_entry (table : fragment) (slot, chain) =
    match List.nth_opt table.references slot with
    | Some entry -> Queue.add (entry, chain) queue
    | None ->
        Compiler_bug.raise_bug ~stage:"Emit_c" "a call of method %d of %s" slot
          (Lowered.Item.to_string table.item)
  in
  while not (Queue.is_empty queue) do
    let item, chain = Queue.pop queue in
    if not (Item_table.mem visited item) then begin
      Item_table.replace visited item ();
      match lookup item with
      | None -> ()
      | Some (fragment : fragment) -> (
          let chain = item :: chain in
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
    (walk ~lookup:(fun item -> Some (lookup item)) ~follows_only_called_entries:false roots)

let trace_reachable ~lookup roots = walk ~lookup ~follows_only_called_entries:true roots
let small = 24

let is_small (fragment : fragment) =
  match fragment.kind with
  | Functions { nested; weight } -> nested = 0 && weight <= small
  | Static_data | Table_entries _ -> false

let render_fragment (fragment : fragment) =
  let names = Hashtbl.create 64 in
  let number prefix list =
    List.iteri
      (fun position name ->
        if not (Hashtbl.mem names name) then
          Hashtbl.replace names name (Printf.sprintf "%s%d" prefix position))
      list
  in
  let self = Mangling.make_symbol fragment.item in
  number "@item_" (List.map Mangling.make_symbol fragment.references);
  number "@type_"
    (List.map C_types.render_key_name
       (fragment.types
       @ List.concat_map
           (fun (_, (defined : C_types.defined)) -> defined.references)
           fragment.environments));
  number "@site_" (List.map C_runtime.render_site_symbol fragment.sites);
  let rename identifier =
    if String.starts_with ~prefix:self identifier then
      "@self" ^ String.drop_first (String.length self) identifier
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
  Fragment.iter_identifiers whole
    ~on_identifier:(fun identifier -> Buffer.add_string buffer (rename identifier))
    ~on_other:(Buffer.add_char buffer);
  Buffer.contents buffer

module Ir_builder = Ir_builder

let make_symbol = Mangling.make_symbol

let make_data_fragment env (data : Lowered.data) =
  let emission = Emission.create env ~prefix:(Mangling.make_symbol data.data_item) in
  let definition = C_data.render_data emission data in
  Fragment.make emission ~item:data.data_item ~kind:Static_data ~functions:[] ~definition
    ~references:(Emission.list_referenced_items emission ~referrer:data.data_item)

let make_table_fragment env (table : Lowered.table) =
  let emission = Emission.create env ~prefix:(Mangling.make_symbol table.table_item) in
  let definition = C_data.render_table emission table in
  Fragment.make emission ~item:table.table_item ~kind:(Table_entries table.capability) ~functions:[]
    ~definition ~references:(List.map fst table.entries)

let render_file env profile (fragments : (fragment * linkage) list) =
  let types = C_types.create env in
  let local_types = Key_table.create 16 in
  List.iter
    (fun ((fragment : fragment), _) ->
      List.iter (C_types.register types) fragment.types;
      List.iter
        (fun (key, (defined : C_types.defined)) ->
          Key_table.replace local_types key defined;
          C_types.register types key;
          List.iter (C_types.register types) defined.references)
        fragment.environments)
    fragments;
  let render_linkage = function Internal -> "static inline " | External -> "" in
  let function_texts =
    List.concat_map
      (fun ((fragment : fragment), linkage) ->
        let count = List.length fragment.functions in
        List.mapi
          (fun position (header, body) ->
            let linkage = if position < count - 1 then Internal else linkage in
            (render_linkage linkage ^ header, body))
          fragment.functions)
      fragments
  in
  let render_symbol header =
    let before = String.sub header 0 (String.index header '(') in
    match String.split_last ~sep:" " before with Some (_, symbol) -> symbol | None -> before
  in
  let declared = Hashtbl.create 64 in
  let declarations = Buffer.create 4096 in
  List.iter
    (fun (header, _) ->
      Hashtbl.replace declared (render_symbol header) ();
      Buffer.add_string declarations (header ^ ";\n"))
    function_texts;
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
    | None -> C_types.define types key
  in
  let rec close () =
    let pending =
      List.filter (fun key -> not (C_types.Keys.mem key !definitions)) (List.rev types.order)
    in
    if pending <> [] then begin
      List.iter
        (fun key -> definitions := C_types.Keys.add key (define_key key) !definitions)
        pending;
      close ()
    end
  in
  close ();
  let keys = List.rev types.order in
  let read_defined key = C_types.Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer C_runtime.runtime_declarations;
  Buffer.add_string buffer
    (match profile with
    | Development ->
        "#define T_UNREACHABLE() t_runtime_compiler_bug()\n\
         #define T_OBLIGATION_FAILED(message, length, site, trace) t_runtime_panic(message, \
         length, site, trace)\n"
    | Release ->
        "#define T_UNREACHABLE() __builtin_unreachable()\n\
         #define T_OBLIGATION_FAILED(message, length, site, trace) ((void)(message), \
         (void)(length), (void)(site), (void)(trace), __builtin_unreachable())\n");
  let helpers_used =
    List.sort_uniq String.compare
      (types.helpers_used
      @ List.concat_map (fun ((fragment : fragment), _) -> fragment.helpers) fragments)
  in
  List.iter
    (fun (name, text) -> if List.mem name helpers_used then Buffer.add_string buffer text)
    C_runtime.helpers;
  List.iter
    (fun key ->
      match (read_defined key).definition with
      | Struct _ ->
          Buffer.add_string buffer
            (Printf.sprintf "typedef struct %s %s;\n" (C_types.render_key_name key)
               (C_types.render_key_name key))
      | Typedef _ | Code_typedef _ -> ())
    keys;
  let emitted = ref C_types.Keys.empty in
  let rec emit_typedef key =
    if not (C_types.Keys.mem key !emitted) then
      match (read_defined key).definition with
      | Struct _ -> ()
      | (Typedef _ | Code_typedef _) as definition ->
          emitted := C_types.Keys.add key () !emitted;
          List.iter emit_typedef (read_defined key).references;
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
      match (read_defined key).definition with
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
  List.iter (fun (header, body) -> Buffer.add_string buffer (header ^ body)) function_texts;
  Buffer.contents buffer

type position = { file : string; line : int; column : int }

let render_sites_file ~resolve_position:resolve fragments =
  let positions =
    List.map
      (fun site -> (site, resolve site))
      (List.sort_uniq compare
         (List.concat_map (fun (fragment : fragment) -> fragment.sites) fragments))
  in
  let file_symbols =
    List.mapi
      (fun index file -> (file, Printf.sprintf "t_file_%d" index))
      (List.sort_uniq String.compare
         (List.map (fun (_, (position : position)) -> position.file) positions))
  in
  String.concat ""
    ((C_runtime.runtime_declarations :: List.map C_values.render_bytes_definition file_symbols)
    @ List.map
        (fun (site, (position : position)) ->
          Printf.sprintf "const struct t_site %s = { %s, %d, %d, %d };\n"
            (C_runtime.render_site_symbol site)
            (List.assoc position.file file_symbols)
            (String.length position.file) position.line position.column)
        positions)

module For_testing = struct
  let render_c (fragment : fragment) =
    String.concat ""
      (List.map (fun (header, body) -> header ^ body) fragment.functions @ [ fragment.definition ])
end
