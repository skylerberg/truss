open C_runtime
open C_types
open C_data

type build = C_runtime.build = Development | Release
type linkage = C_runtime.linkage = External | Internal

let anchor_struct = C_runtime.anchor_struct
let runtime_declarations = C_runtime.runtime_declarations
let anchor_symbol = C_runtime.anchor_symbol
let version = 26

type site = C_runtime.site = { definition : Path.t; line : int; column : int }
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
  types : key list;
  environments : (key * defined) list;
  prototypes : (string * string) list;
  statics : string list;
  anchors : (string * Path.t) list;
  helpers : string list;
  references : Instance.key list;
  calls : (Path.t * int) list;
  called : Instance.key list;
  failures : (failure * site) list;
}

let key fragment = fragment.key
let references fragment = fragment.references
let calls fragment = fragment.calls
let called fragment = fragment.called
let failures fragment = fragment.failures

let table fragment =
  match fragment.kind with Table_entries capability -> Some capability | _ -> None

let small = 24

let is_small fragment =
  match fragment.kind with
  | Functions { nested; weight } -> nested = 0 && weight <= small
  | Static_data | Table_entries _ -> false

let text fragment =
  let names = Hashtbl.create 64 in
  let number prefix list =
    List.iteri
      (fun position name ->
        if not (Hashtbl.mem names name) then
          Hashtbl.replace names name (Printf.sprintf "%s%d" prefix position))
      list
  in
  let self = Instance.symbol fragment.key in
  number "@instance_" (List.map Instance.symbol fragment.references);
  number "@type_"
    (List.map key_name
       (fragment.types
       @ List.concat_map (fun (_, (defined : defined)) -> defined.references) fragment.environments
       ));
  number "@anchor_" (List.map fst fragment.anchors);
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
          (fun (key, (defined : defined)) ->
            key_name key
            ^
            match defined.definition with
            | Struct { body; _ } -> body
            | Typedef text | Code_typedef text -> text)
          fragment.environments
      @ List.map snd fragment.prototypes @ fragment.statics @ fragment.helpers)
  in
  let buffer = Buffer.create (String.length whole) in
  let is_start character =
    character = '_'
    || (character >= 'a' && character <= 'z')
    || (character >= 'A' && character <= 'Z')
  in
  let is_part character = is_start character || (character >= '0' && character <= '9') in
  let length = String.length whole in
  let rec scan position =
    if position < length then
      if is_start whole.[position] then begin
        let stop = ref position in
        while !stop < length && is_part whole.[!stop] do
          incr stop
        done;
        Buffer.add_string buffer (rename (String.sub whole position (!stop - position)));
        scan !stop
      end
      else begin
        Buffer.add_char buffer whole.[position];
        scan (position + 1)
      end
  in
  scan 0;
  Buffer.contents buffer

module Builder = Builder

let contains text part =
  let length = String.length part and total = String.length text in
  let rec matches position offset =
    offset = length || (text.[position + offset] = part.[offset] && matches position (offset + 1))
  in
  let rec from position =
    position + length <= total
    &&
    match String.index_from_opt text position part.[0] with
    | Some found -> (found + length <= total && matches found 0) || from (found + 1)
    | None -> false
  in
  length = 0 || from 0

let bytes_definition (text, name) =
  let bytes =
    List.init (String.length text) (fun index -> string_of_int (Char.code text.[index]))
  in
  Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
    (max 1 (String.length text))
    (if bytes = [] then "0" else String.concat ", " bytes)

type compiled = Code of Builder.instance | Data of Lowered.data | Table of Lowered.table

let fragment env (compiled : compiled) =
  let key, context =
    match compiled with
    | Code code -> (code.C_instance.key, code.context)
    | Data data -> (data.data_key, new_context env (Instance.symbol data.data_key))
    | Table table -> (table.table_key, new_context env (Instance.symbol table.table_key))
  in
  let functions, definition, kind =
    match compiled with
    | Code code ->
        let nested =
          List.sort compare
            (List.filter_map
               (fun (nested, text) -> Option.map (fun nested -> (nested, text)) nested)
               code.C_instance.functions)
        in
        let main =
          match List.assoc_opt None code.C_instance.functions with
          | Some text -> text
          | None -> Compiler_bug.bug ~stage:"Emit_c" "%s is not built" (Instance.to_string key)
        in
        ( List.map snd nested @ [ main ],
          "",
          Functions { nested = List.length nested; weight = code.C_instance.weight } )
    | Data data -> ([], data_c context data, Static_data)
    | Table table -> ([], table_c context table, Table_entries table.capability)
  in
  let types = List.rev context.order in
  let environments =
    List.filter_map
      (fun key -> match key with Environment _ -> Some (key, define context key) | _ -> None)
      types
  in
  {
    key;
    kind;
    functions;
    definition;
    types = List.filter (function Environment _ -> false | _ -> true) types;
    environments;
    prototypes = List.rev context.prototypes;
    statics =
      List.rev_map bytes_definition
        (List.filter
           (fun (_, name) ->
             List.exists (fun (_, body) -> contains body name) functions || contains definition name)
           context.bytes)
      @ List.rev context.statics;
    anchors = List.rev context.anchors;
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

let anchors fragment = List.map snd fragment.anchors

let file env build (fragments : (fragment * linkage) list) =
  let context = new_context env "" in
  let local_types = Hashtbl.create 16 in
  List.iter
    (fun ((fragment : fragment), _) ->
      List.iter (register context) fragment.types;
      List.iter
        (fun (key, (defined : defined)) ->
          Hashtbl.replace local_types key defined;
          register context key;
          List.iter (register context) defined.references)
        fragment.environments)
    fragments;
  (* Every function of the file is declared before any body, so that a call
     of a copy sees the copy's declaration, not one made for the call. *)
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
    (* The symbol a header declares: the name before its parameters. *)
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
  (* Define every type the code names, and every type those definitions
     name, until nothing new is named. *)
  let definitions = ref Keys.empty in
  let define_key key =
    match Hashtbl.find_opt local_types key with
    | Some defined -> defined
    | None -> define context key
  in
  let rec close () =
    let pending =
      List.filter (fun key -> not (Keys.mem key !definitions)) (List.rev context.order)
    in
    if pending <> [] then begin
      List.iter (fun key -> definitions := Keys.add key (define_key key) !definitions) pending;
      close ()
    end
  in
  close ();
  let keys = List.rev context.order in
  let defined key = Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (runtime_declarations (Memory_layout.target env));
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
    helpers;
  List.iter
    (fun key ->
      match (defined key).definition with
      | Struct _ ->
          Buffer.add_string buffer
            (Printf.sprintf "typedef struct %s %s;\n" (key_name key) (key_name key))
      | Typedef _ | Code_typedef _ -> ())
    keys;
  (* Typedefs, each after the typedefs it names; then structs, each after
     the structs it holds by value. Every struct is declared above, so
     naming one needs nothing more. *)
  let emitted = ref Keys.empty in
  let rec emit_typedef key =
    if not (Keys.mem key !emitted) then
      match (defined key).definition with
      | Struct _ -> ()
      | (Typedef _ | Code_typedef _) as definition ->
          emitted := Keys.add key () !emitted;
          List.iter emit_typedef (defined key).references;
          Buffer.add_string buffer
            (match definition with
            | Typedef c_type -> Printf.sprintf "typedef %s %s;\n" c_type (key_name key)
            | Code_typedef text -> text
            | Struct _ -> "")
  in
  List.iter emit_typedef keys;
  let rec emit key =
    if not (Keys.mem key !emitted) then begin
      emitted := Keys.add key () !emitted;
      match (defined key).definition with
      | Struct { body; holds } ->
          List.iter emit holds;
          Buffer.add_string buffer (Printf.sprintf "struct %s {\n%s};\n" (key_name key) body)
      | Typedef _ | Code_typedef _ -> ()
    end
  in
  List.iter emit keys;
  List.iter
    (fun key ->
      let layout =
        match key with
        | Type ty -> Some (Memory_layout.of_type env ty)
        | Block (ty, variant) -> Some (Memory_layout.block env ty variant)
        | Code _ | Environment _ | Evidence _ -> None
      in
      Option.iter
        (fun (layout : Memory_layout.t) ->
          Buffer.add_string buffer
            (Printf.sprintf "_Static_assert(sizeof(%s) == %d && _Alignof(%s) == %d, \"layout\");\n"
               (key_name key) layout.size (key_name key) layout.alignment))
        layout)
    keys;
  let anchors =
    List.sort_uniq String.compare
      (List.concat_map (fun ((fragment : fragment), _) -> List.map fst fragment.anchors) fragments)
  in
  List.iter
    (fun symbol ->
      Buffer.add_string buffer (Printf.sprintf "extern const struct t_anchor %s;\n" symbol))
    anchors;
  Buffer.add_buffer buffer declarations;
  List.iter
    (fun ((fragment : fragment), _) -> List.iter (Buffer.add_string buffer) fragment.statics)
    fragments;
  List.iter
    (fun ((fragment : fragment), _) -> Buffer.add_string buffer fragment.definition)
    fragments;
  List.iter (fun (header, body) -> Buffer.add_string buffer (header ^ body)) own;
  Buffer.contents buffer

module For_testing = struct
  let c fragment =
    String.concat ""
      (List.map (fun (header, body) -> header ^ body) fragment.functions @ [ fragment.definition ])
end
