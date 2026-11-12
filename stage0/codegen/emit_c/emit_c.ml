open C_runtime
open C_types
open C_values
open C_code
open C_data

type build = C_runtime.build = Development | Release
type linkage = C_runtime.linkage = External | Internal

let anchor_struct = C_runtime.anchor_struct
let runtime_declarations = C_runtime.runtime_declarations
let anchor_symbol = C_runtime.anchor_symbol

let file env build ?(data = []) ?(tables = []) (instances : (Lir.t * linkage) list) =
  let context =
    {
      env;
      build;
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
  in
  List.iter
    (fun ((instance : Lir.t), _) ->
      let symbol = Instance.symbol instance.key in
      Array.iteri
        (fun n (f : Lir.function_) ->
          context.environments <-
            Keys.add (Environment (symbol, n)) f.environment context.environments)
        instance.nested)
    instances;
  let nested_name symbol n = Printf.sprintf "%s_Nested_%d" symbol n in
  (* Every function of the file is declared before any body, so that a call
     of a copy sees the copy's declaration, not one made for the call. *)
  List.iter
    (fun ((instance : Lir.t), linkage) ->
      let symbol = Instance.symbol instance.key in
      Array.iteri
        (fun n f ->
          let name = nested_name symbol n in
          declare_prototype context name
            (prototype context symbol name ~linkage:Internal (Lir.signature f) ^ ";\n"))
        instance.nested;
      declare_prototype context symbol
        (prototype context symbol symbol ~linkage (Lir.signature instance.main) ^ ";\n"))
    instances;
  let bodies =
    List.concat_map
      (fun ((instance : Lir.t), linkage) ->
        let symbol = Instance.symbol instance.key in
        List.mapi
          (fun n f -> function_c context instance.key (nested_name symbol n) ~linkage:Internal f)
          (Array.to_list instance.nested)
        @ [ function_c context instance.key symbol ~linkage instance.main ])
      instances
  in
  let data_definitions = List.map (data_c context) data @ List.map (table_c context) tables in
  (* Define every type the code names, and every type those definitions
     name, until nothing new is named. *)
  let definitions = ref Keys.empty in
  let rec close () =
    let pending =
      List.filter (fun key -> not (Keys.mem key !definitions)) (List.rev context.order)
    in
    if pending <> [] then begin
      List.iter (fun key -> definitions := Keys.add key (define context key) !definitions) pending;
      close ()
    end
  in
  close ();
  let keys = List.rev context.order in
  let defined key = Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (runtime_declarations (Memory_layout.target env));
  List.iter
    (fun (name, text) -> if List.mem name context.helpers_used then Buffer.add_string buffer text)
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
            | Typedef c -> Printf.sprintf "typedef %s %s;\n" c (key_name key)
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
  List.iter
    (fun (text, name) ->
      let bytes = List.init (String.length text) (fun i -> string_of_int (Char.code text.[i])) in
      Buffer.add_string buffer
        (Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
           (max 1 (String.length text))
           (if bytes = [] then "0" else String.concat ", " bytes)))
    (List.rev context.bytes);
  List.iter
    (fun (symbol, _) ->
      Buffer.add_string buffer (Printf.sprintf "extern const struct t_anchor %s;\n" symbol))
    (List.rev context.anchors);
  List.iter
    (fun (_, declaration) -> Buffer.add_string buffer declaration)
    (List.rev context.prototypes);
  List.iter (Buffer.add_string buffer) (List.rev context.statics);
  List.iter (Buffer.add_string buffer) data_definitions;
  List.iter (Buffer.add_string buffer) bodies;
  Buffer.contents buffer
