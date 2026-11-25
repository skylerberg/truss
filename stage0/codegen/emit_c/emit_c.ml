module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = C_text.key
end))

module Path_table = Hashtbl.Make (Path)

type linkage = C_runtime.linkage = External | Internal

let shared_structs = C_runtime.shared_structs
let version = 29

type failure = C_runtime.failure = Echo | Todo
type fragment = Fragment.t

let item (fragment : fragment) = fragment.item
let references (fragment : fragment) = fragment.references
let called (fragment : fragment) = fragment.called
let sites (fragment : fragment) = fragment.sites
let failures (fragment : fragment) = fragment.failures
let hash (fragment : fragment) = fragment.hash

module Item_table = Hashtbl.Make (Lowered.Item)

let trace_reachable ~lookup roots =
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
          match fragment.kind with
          | Table_entries capability ->
              Path_table.add tables capability fragment;
              List.iter (enqueue_entry fragment)
                (List.rev (Path_table.find_all called_slots capability))
          | Functions _ | Static_data ->
              List.iter
                (fun (capability, slot) ->
                  if not (List.mem_assoc slot (Path_table.find_all called_slots capability)) then begin
                    Path_table.add called_slots capability (slot, chain);
                    List.iter
                      (fun table -> enqueue_entry table (slot, chain))
                      (List.rev (Path_table.find_all tables capability))
                  end)
                fragment.calls;
              List.iter (fun reference -> Queue.add (reference, chain) queue) fragment.references)
    end
  done;
  List.rev !reachable

let small = 24

let is_small (fragment : fragment) =
  match fragment.kind with
  | Functions { nested; weight } -> nested = 0 && weight <= small
  | Static_data | Table_entries _ -> false

module Ir_builder = Ir_builder

let make_symbol = Mangling.make_symbol

let make_data_fragment env (data : Lowered.data) =
  let emission = Emission.create env ~item:data.data_item in
  let definition = C_data.render_data emission data in
  Fragment.make emission ~kind:Static_data
    ~references:(Emission.list_references emission)
    ~functions:[] ~definition

let make_table_fragment env (table : Lowered.table) =
  let emission = Emission.create env ~item:table.table_item in
  let definition = C_data.render_table emission table in
  Fragment.make emission ~kind:(Table_entries table.capability)
    ~references:(List.map fst table.entries) ~functions:[] ~definition

let render_type_text text =
  C_text.render text ~resolve:(function
    | Type_name key -> C_text.render_key_name key
    | _ -> C_runtime.raise_bug "a type definition that names something other than a type")

type position = { file : string; line : int; column : int }

let generated_file = "<generated>"

let render_string_literal text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun character ->
      if character = '"' || character = '\\' || character < ' ' || character > '~' then
        Buffer.add_string buffer (Printf.sprintf "\\%03o" (Char.code character))
      else Buffer.add_char buffer character)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

type presumed_location = { presumed_file : string; presumed_line : int }

type line_writer = {
  buffer : Buffer.t;
  resolve_position : Lowered.site -> position;
  mutable presumed : presumed_location option;
  mutable is_at_line_start : bool;
}

let write_line_control writer ~file ~line =
  Buffer.add_string writer.buffer (Printf.sprintf "#line %d %s\n" line (render_string_literal file));
  writer.presumed <- Some { presumed_file = file; presumed_line = line }

let place_line writer (site : Lowered.site option) =
  match (site, writer.presumed) with
  | None, Some { presumed_file; _ } when presumed_file = generated_file -> ()
  | None, _ -> write_line_control writer ~file:generated_file ~line:1
  | Some site, presumed ->
      let { file; line; _ } = writer.resolve_position site in
      if presumed <> Some { presumed_file = file; presumed_line = line } then
        write_line_control writer ~file ~line

let write_segment writer ({ site; text } : C_text.segment) =
  let length = String.length text in
  let rec write_from start =
    if start < length then begin
      if writer.is_at_line_start then place_line writer site;
      match String.index_from_opt text start '\n' with
      | Some newline ->
          Buffer.add_substring writer.buffer text start (newline + 1 - start);
          writer.is_at_line_start <- true;
          writer.presumed <-
            Option.map
              (fun presumed -> { presumed with presumed_line = presumed.presumed_line + 1 })
              writer.presumed;
          write_from (newline + 1)
      | None ->
          Buffer.add_substring writer.buffer text start (length - start);
          writer.is_at_line_start <- false
    end
  in
  write_from 0

let render_file env (profile : Profile.t) ~resolve_position (fragments : (fragment * linkage) list)
    =
  let types = C_types.create env ~owner:None in
  let local_types = Key_table.create 16 in
  List.iter
    (fun ((fragment : fragment), _) ->
      List.iter (C_types.register types) fragment.types;
      List.iter
        (fun (key, (defined : string C_types.defined)) ->
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
          (fun position (text : Fragment.function_text) ->
            let linkage = if position < count - 1 then Internal else linkage in
            { text with header = render_linkage linkage ^ text.header })
          fragment.functions)
      fragments
  in
  let declared = Hashtbl.create 64 in
  let declarations = Buffer.create 4096 in
  List.iter
    (fun (text : Fragment.function_text) ->
      Hashtbl.replace declared text.symbol ();
      Buffer.add_string declarations (text.header ^ ";\n"))
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
    | None -> C_types.map_defined render_type_text (C_types.define types key)
  in
  let rec close () =
    let pending =
      List.filter (fun key -> not (C_types.Keys.mem key !definitions)) (C_types.list_keys types)
    in
    if pending <> [] then begin
      List.iter
        (fun key -> definitions := C_types.Keys.add key (define_key key) !definitions)
        pending;
      close ()
    end
  in
  close ();
  let keys = C_types.list_keys types in
  let read_defined key = C_types.Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer C_runtime.runtime_declarations;
  Buffer.add_string buffer
    (match profile with
    | Development ->
        "#define TRUSS_UNREACHABLE() truss_runtime_compiler_bug()\n\
         #define TRUSS_FAIL_OBLIGATION_WHEN(condition, message, length, site, trace) ((condition) \
         ? truss_runtime_panic(message, length, site, trace) : (void)0)\n"
    | Release ->
        "#define TRUSS_UNREACHABLE() __builtin_unreachable()\n\
         #define TRUSS_FAIL_OBLIGATION_WHEN(condition, message, length, site, trace) \
         ((void)(condition), (void)(message), (void)(length), (void)(site), (void)(trace))\n");
  let helpers_used =
    List.concat_map (fun ((fragment : fragment), _) -> fragment.helpers) fragments
  in
  List.iter
    (fun (helper, text) -> if List.mem helper helpers_used then Buffer.add_string buffer text)
    C_runtime.helpers;
  List.iter
    (fun key ->
      match (read_defined key).definition with
      | Struct _ ->
          Buffer.add_string buffer
            (Printf.sprintf "typedef struct %s %s;\n" (C_text.render_key_name key)
               (C_text.render_key_name key))
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
                Printf.sprintf "typedef %s %s;\n" c_type (C_text.render_key_name key)
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
            (Printf.sprintf "struct %s {\n%s};\n" (C_text.render_key_name key) body)
      | Typedef _ | Code_typedef _ -> ()
    end
  in
  List.iter emit keys;
  List.iter
    (fun key ->
      let layout =
        match key with
        | C_text.Type ty -> Some (Memory_layout.of_type env ty)
        | Block (ty, variant) -> Some (Memory_layout.lay_out_block env ty variant)
        | Code _ | Environment _ | Evidence _ | Capabilities _ -> None
      in
      Option.iter
        (fun (layout : Memory_layout.t) ->
          Buffer.add_string buffer
            (Printf.sprintf "_Static_assert(sizeof(%s) == %d && _Alignof(%s) == %d, \"layout\");\n"
               (C_text.render_key_name key) layout.size (C_text.render_key_name key)
               layout.alignment))
        layout)
    keys;
  List.iter
    (fun site ->
      Buffer.add_string buffer
        (Printf.sprintf "extern const struct truss_site %s;\n" (C_runtime.render_site_symbol site)))
    (List.sort_uniq compare
       (List.concat_map (fun ((fragment : fragment), _) -> fragment.sites) fragments));
  List.iter
    (fun capability ->
      Buffer.add_string buffer
        (Printf.sprintf "__attribute__((weak)) const uint8_t %s = 0;\n"
           (C_runtime.render_capability_symbol capability)))
    (List.sort_uniq Path.compare
       (List.concat_map (fun ((fragment : fragment), _) -> fragment.capabilities) fragments));
  Buffer.add_buffer buffer declarations;
  List.iter
    (fun ((fragment : fragment), _) -> List.iter (Buffer.add_string buffer) fragment.statics)
    fragments;
  List.iter
    (fun ((fragment : fragment), _) -> Buffer.add_string buffer fragment.definition)
    fragments;
  let list_segments (text : Fragment.function_text) : C_text.segment list =
    { site = text.opening; text = text.header } :: text.body
  in
  match profile with
  | Development ->
      List.iter
        (fun text ->
          List.iter
            (fun ({ text; _ } : C_text.segment) -> Buffer.add_string buffer text)
            (list_segments text))
        function_texts;
      Buffer.contents buffer
  | Release ->
      let writer =
        {
          buffer = Buffer.create (2 * Buffer.length buffer);
          resolve_position;
          presumed = None;
          is_at_line_start = true;
        }
      in
      write_segment writer { site = None; text = Buffer.contents buffer };
      List.iter (fun text -> List.iter (write_segment writer) (list_segments text)) function_texts;
      Buffer.contents writer.buffer

let list_copies ~is_worked_on ~find_fragment (fragment : fragment) =
  match fragment.item with
  | Code _ as caller ->
      List.filter_map
        (fun (called : Lowered.Item.t) ->
          match called with
          | Code { path; _ }
            when (not (Lowered.Item.equal called caller))
                 && not (is_worked_on (Path.locate_package path)) ->
              Option.bind (find_fragment called) (fun copy ->
                  if is_small copy then Some copy else None)
          | _ -> None)
        (List.sort_uniq Lowered.Item.compare fragment.called)
  | _ -> []

let render_unit env (profile : Profile.t) ~resolve_position ~is_worked_on ~find_fragment fragment =
  let copies =
    match profile with
    | Development -> list_copies ~is_worked_on ~find_fragment fragment
    | Release -> []
  in
  render_file env profile ~resolve_position
    ((fragment, External) :: List.map (fun copy -> (copy, Internal)) copies)

let render_sites_file ~resolve_position:resolve sites =
  let positions = List.map (fun site -> (site, resolve site)) (List.sort_uniq compare sites) in
  let file_symbols =
    List.mapi
      (fun index file -> (file, Printf.sprintf "truss_file_%d" index))
      (List.sort_uniq String.compare
         (List.map (fun (_, (position : position)) -> position.file) positions))
  in
  String.concat ""
    (C_runtime.runtime_declarations
     :: List.map
          (fun (file, symbol) ->
            Printf.sprintf "static const uint8_t %s%s;\n" symbol
              (C_values.render_bytes_initializer file))
          file_symbols
    @ List.map
        (fun (site, (position : position)) ->
          Printf.sprintf "const struct truss_site %s = { %s, %d, %d, %d };\n"
            (C_runtime.render_site_symbol site)
            (List.assoc position.file file_symbols)
            (String.length position.file) position.line position.column)
        positions)

module For_testing = struct
  let render_c (fragment : fragment) =
    String.concat ""
      (List.concat_map
         (fun (text : Fragment.function_text) ->
           text.header :: List.map (fun ({ text; _ } : C_text.segment) -> text) text.body)
         fragment.functions
      @ [ fragment.definition ])
end
