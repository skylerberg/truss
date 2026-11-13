open C_runtime
open C_types
open C_code
open C_data

type build = C_runtime.build = Development | Release
type linkage = C_runtime.linkage = External | Internal

let anchor_struct = C_runtime.anchor_struct
let runtime_declarations = C_runtime.runtime_declarations
let anchor_symbol = C_runtime.anchor_symbol
let version = 26

type site = { definition : Path.t; line : int; column : int }
type failure = Echo | Todo
type kind = Code of { nested : int; weight : int } | Data | Table of Path.t option

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
let table fragment = match fragment.kind with Table capability -> Some capability | _ -> None
let small = 24

let is_small fragment =
  match fragment.kind with Code { nested; weight } -> nested = 0 && weight <= small | _ -> false

(* A fragment's C with every name it holds written as a number: the
   instance's own symbol, which its nested functions' and statics' names
   start with, as a mark; each instance it refers to as that instance's
   place among its references; each type as its place among the types it
   names; and each anchor as its place among its anchors. *)
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

(* The instances that the LIR of an instance names. *)

let add key keys = if List.exists (Instance.equal key) keys then keys else key :: keys

let rec place_keys (place : Lir.place) keys =
  let keys = match place.root with Static { key; _ } -> add key keys | Local _ -> keys in
  List.fold_left
    (fun keys -> function Lir.Index operand -> operand_keys operand keys | _ -> keys)
    keys place.projections

and operand_keys (operand : Lir.operand) keys =
  match operand with
  | Copy place | Move place | Address { place; _ } | Moved_address place -> place_keys place keys
  | Constant (Symbol_address key) -> add key keys
  | Constant _ -> keys

let function_ref_keys (function_ref : Lir.function_ref) keys =
  match function_ref with Instance key -> add key keys | Nested _ -> keys

let rvalue_keys (rvalue : Lir.rvalue) keys =
  match rvalue with
  | Use operand | Unary (_, operand) | Convert (operand, _) -> operand_keys operand keys
  | Binary (_, left, right) -> operand_keys right (operand_keys left keys)
  | Build { fields; _ } ->
      List.fold_left (fun keys (_, operand) -> operand_keys operand keys) keys fields
  | Is_variant (place, _) -> place_keys place keys
  | Function_value { code; environment } ->
      Option.fold ~none:keys
        ~some:(fun environment_operand -> operand_keys environment_operand keys)
        environment
      |> function_ref_keys code

let instance_references env (instance : Lir.t) =
  let environment nested_index = instance.nested.(nested_index).environment in
  let in_function keys (function_ : Lir.function_) =
    Array.fold_left
      (fun keys (block : Lir.basic_block) ->
        let keys =
          List.fold_left
            (fun keys (statement : Lir.statement) ->
              match statement with
              | Assign (place, rvalue) -> rvalue_keys rvalue (place_keys place keys)
              | Call { target; arguments; result } -> (
                  let keys =
                    match target with
                    | Direct { function_ = called; _ } -> function_ref_keys called keys
                    | _ ->
                        List.fold_left
                          (fun keys operand -> operand_keys operand keys)
                          keys (Lir.target_operands target)
                  in
                  let keys =
                    List.fold_left (fun keys operand -> operand_keys operand keys) keys arguments
                  in
                  match result with
                  | Returned place | Written place -> place_keys place keys
                  | Discarded -> keys)
              | Drop place -> (
                  let keys = place_keys place keys in
                  match Lir.place_type env ~environment function_ place with
                  | Some (Value ty) -> add (Drop ty) keys
                  | _ -> keys)
              | Free_block { place; _ } -> place_keys place keys
              | Echo { text; length; _ } -> operand_keys length (operand_keys text keys)
              | Region _ | Regions_end _ -> keys
              | Fork { branches } ->
                  List.fold_left (fun keys (_, operand) -> operand_keys operand keys) keys branches
              | Fork_range { environment; first; last; _ } ->
                  operand_keys last (operand_keys first (operand_keys environment keys)))
            keys block.statements
        in
        match block.terminator with
        | Switch { value; _ } -> operand_keys value keys
        | Switch_variant { place; _ } -> place_keys place keys
        | Return value ->
            Option.fold ~none:keys ~some:(fun operand -> operand_keys operand keys) value
        | Fail { message; length; _ } -> operand_keys length (operand_keys message keys)
        | Yield { value; _ } -> operand_keys value keys
        | Goto _ | Unreachable -> keys)
      keys function_.blocks
  in
  let keys = Array.fold_left in_function (in_function [] instance.main) instance.nested in
  List.filter (fun key -> not (Instance.equal key instance.key)) (List.rev keys)

let functions_of (instance : Lir.t) = instance.main :: Array.to_list instance.nested

let statements_of instance =
  List.concat_map
    (fun (function_ : Lir.function_) ->
      List.concat_map
        (fun (block : Lir.basic_block) -> block.statements)
        (Array.to_list function_.blocks))
    (functions_of instance)

let terminators_of instance =
  List.concat_map
    (fun (function_ : Lir.function_) ->
      List.map (fun (block : Lir.basic_block) -> block.terminator) (Array.to_list function_.blocks))
    (functions_of instance)

let site_of (site : Lir.site) =
  { definition = site.definition; line = site.line; column = site.column }

(* A function's code size, for choosing the small ones: each statement,
   and each block twice. *)
let weight (function_ : Lir.function_) =
  Array.fold_left
    (fun total (block : Lir.basic_block) -> total + 2 + List.length block.statements)
    0 function_.blocks

(* Emitting *)

let new_context env prefix =
  {
    env;
    prefix;
    order = [];
    registered = Keys.empty;
    environments = Keys.empty;
    bytes = [];
    prototypes = [];
    anchors = [];
    references = None;
    helpers_used = [];
    statics = [];
  }

let nested_name symbol position = Printf.sprintf "%s_Nested_%d" symbol position

let bytes_definition (text, name) =
  let bytes =
    List.init (String.length text) (fun index -> string_of_int (Char.code text.[index]))
  in
  Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
    (max 1 (String.length text))
    (if bytes = [] then "0" else String.concat ", " bytes)

let fragment env (compiled : Lir.compiled) =
  let key =
    match compiled with
    | Code instance -> instance.key
    | Data data -> data.data_key
    | Table table -> table.table_key
  in
  let symbol = Instance.symbol key in
  let context = new_context env symbol in
  let functions, definition, kind =
    match compiled with
    | Code instance ->
        Array.iteri
          (fun position (function_ : Lir.function_) ->
            context.environments <-
              Keys.add (Environment (symbol, position)) function_.environment context.environments)
          instance.nested;
        let nested =
          List.mapi
            (fun position function_ ->
              function_c context instance.key (nested_name symbol position) function_)
            (Array.to_list instance.nested)
        in
        ( nested @ [ function_c context instance.key symbol instance.main ],
          "",
          Code { nested = Array.length instance.nested; weight = weight instance.main } )
    | Data data -> ([], data_c context data, Data)
    | Table table -> ([], table_c context table, Table table.capability)
  in
  let types = List.rev context.order in
  let environments =
    List.filter_map
      (fun key -> match key with Environment _ -> Some (key, define context key) | _ -> None)
      types
  in
  let references, calls, called, failures =
    match compiled with
    | Code instance ->
        ( instance_references env instance,
          List.filter_map
            (function
              | Lir.Call { target = Evidence_call { capability; slot; _ }; _ } ->
                  Some (capability, slot)
              | _ -> None)
            (statements_of instance),
          List.filter_map
            (function
              | Lir.Call { target = Direct { function_ = Instance key; _ }; _ } -> Some key
              | _ -> None)
            (statements_of instance),
          List.filter_map
            (function Lir.Echo { site; _ } -> Some (Echo, site_of site) | _ -> None)
            (statements_of instance)
          @ List.filter_map
              (function
                | Lir.Fail { failure = Todo; site; _ } -> Some (Todo, site_of site) | _ -> None)
              (terminators_of instance) )
    | Data _ -> ([], [], [], [])
    | Table table -> (List.map fst table.entries, [], [], [])
  in
  {
    key;
    kind;
    functions;
    definition;
    types = List.filter (function Environment _ -> false | _ -> true) (List.rev context.order);
    environments;
    prototypes = List.rev context.prototypes;
    statics = List.rev_map bytes_definition context.bytes @ List.rev context.statics;
    anchors = List.rev context.anchors;
    helpers = context.helpers_used;
    references;
    calls;
    called;
    failures;
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
  (* The C compiler lays each type out again from its definition, so it is
     made to check that it agrees with the layout the rest was built on. *)
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
