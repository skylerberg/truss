(* The C every file starts with, and the declarations of the runtime and the
   helpers that a file holds only where its code names them. *)

type build = Development | Release
type linkage = External | Internal

(* A position in a definition, relative to the line it starts on. *)
type site = { definition : Path.t; line : int; column : int }
type failure = Echo | Todo

let bug format = Compiler_bug.bug ~stage:"Emit_c" format
let anchor_symbol definition = "t_Anchor_" ^ Instance.path_symbol definition

let anchor_struct =
  "struct t_anchor {\n  const uint8_t *path;\n  t_usize path_length;\n  uint32_t line;\n};\n"

let integer_c : Memory_layout.integer -> string = function
  | Int8 -> "int8_t"
  | Int16 -> "int16_t"
  | Int32 -> "int32_t"
  | Int64 -> "int64_t"
  | UInt8 -> "uint8_t"
  | UInt16 -> "uint16_t"
  | UInt32 -> "uint32_t"
  | UInt64 -> "uint64_t"
  | USize -> "t_usize"
  | ISize -> "t_isize"

let unsigned_c : Memory_layout.integer -> string = function
  | Int8 | UInt8 -> "uint8_t"
  | Int16 | UInt16 -> "uint16_t"
  | Int32 | UInt32 -> "uint32_t"
  | Int64 | UInt64 -> "uint64_t"
  | USize | ISize -> "t_usize"

let signed : Memory_layout.integer -> bool = function
  | Int8 | Int16 | Int32 | Int64 | ISize -> true
  | UInt8 | UInt16 | UInt32 | UInt64 | USize -> false

(* The typedefs every file starts with: the fixed-width integers, from the
   compiler's own predefined macros, and the target's [USize] and
   [ISize]. *)
let integer_typedefs (target : Memory_layout.target) =
  let usize, isize =
    if target.usize_bytes = 8 then ("__UINT64_TYPE__", "__INT64_TYPE__")
    else ("__UINT32_TYPE__", "__INT32_TYPE__")
  in
  String.concat ""
    [
      "typedef __INT8_TYPE__ int8_t;\n";
      "typedef __INT16_TYPE__ int16_t;\n";
      "typedef __INT32_TYPE__ int32_t;\n";
      "typedef __INT64_TYPE__ int64_t;\n";
      "typedef __UINT8_TYPE__ uint8_t;\n";
      "typedef __UINT16_TYPE__ uint16_t;\n";
      "typedef __UINT32_TYPE__ uint32_t;\n";
      "typedef __UINT64_TYPE__ uint64_t;\n";
      Printf.sprintf "typedef %s t_usize;\n" usize;
      Printf.sprintf "typedef %s t_isize;\n" isize;
    ]

type declaration = { name : string; requires : string list; text : string }

let declaration ?(requires = []) name text = { name; requires; text }

(* A runtime function's prototype, named by its symbol. *)
let runtime_function ?requires symbol ~result ~parameters =
  declaration ?requires symbol (Printf.sprintf "%s%s(%s);\n" result symbol parameters)

let failing symbol ~result =
  runtime_function symbol ~result ~requires:[ "struct t_anchor" ]
    ~parameters:
      "const uint8_t *message, t_usize length, const struct t_anchor *anchor, uint32_t line, \
       uint32_t column"

(* The declarations a file holds only where its code names them, each after
   the declarations its text names. A file holds none of the others, so
   that adding one to the runtime leaves the C of every instance that does
   not name it unchanged. *)
let declarations build =
  [
    declaration "struct t_anchor" anchor_struct;
    declaration "struct t_evidence"
      "struct t_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct t_evidence *const *outer;\n\
       };\n";
    declaration "struct t_branch"
      "struct t_branch {\n  void (*run)(void *environment);\n  void *environment;\n};\n";
    failing "t_runtime_panic" ~result:"_Noreturn void ";
    failing "t_runtime_assertion_failed" ~result:"_Noreturn void ";
    failing "t_runtime_todo" ~result:"_Noreturn void ";
    failing "t_runtime_echo" ~result:"void ";
    runtime_function "t_runtime_compiler_bug" ~result:"_Noreturn void " ~parameters:"void";
    (match build with
    | Development ->
        declaration "T_UNREACHABLE" ~requires:[ "t_runtime_compiler_bug" ]
          "#define T_UNREACHABLE() t_runtime_compiler_bug()\n"
    | Release -> declaration "T_UNREACHABLE" "#define T_UNREACHABLE() __builtin_unreachable()\n");
    runtime_function "t_runtime_allocate" ~result:"void *"
      ~parameters:"t_usize size, t_usize alignment";
    runtime_function "t_runtime_reallocate" ~result:"void *"
      ~parameters:"void *pointer, t_usize old_size, t_usize size, t_usize alignment";
    runtime_function "t_runtime_free" ~result:"void " ~parameters:"void *pointer";
    runtime_function "t_runtime_parallel" ~result:"void " ~requires:[ "struct t_branch" ]
      ~parameters:"const struct t_branch *branches, t_usize count";
    runtime_function "t_runtime_parallel_range" ~result:"void "
      ~parameters:
        "void (*body)(void *environment, uint64_t first, uint64_t last), void *environment, \
         uint64_t first, uint64_t last";
    runtime_function "t_runtime_coroutine_start" ~result:"t_usize "
      ~parameters:"void (*code)(void *environment, uint64_t item), void *environment, uint64_t item";
    runtime_function "t_runtime_coroutine_resume" ~result:"uint8_t " ~parameters:"t_usize coroutine";
    runtime_function "t_runtime_coroutine_suspend" ~result:"void " ~parameters:"void";
    runtime_function "t_runtime_tasks_spawn" ~result:"uint8_t "
      ~parameters:
        "uint64_t group, void (*code)(void *environment, uint64_t item), void *environment, \
         uint64_t item";
    runtime_function "t_runtime_run_test" ~result:"void " ~parameters:"uint32_t index";
    runtime_function "t_runtime_report_tests_to" ~result:"void " ~parameters:"int32_t descriptor";
    runtime_function "t_runtime_live_blocks" ~result:"t_usize " ~parameters:"void";
    runtime_function "t_runtime_shared_allocate" ~result:"void *"
      ~parameters:"t_usize size, t_usize alignment";
    runtime_function "t_runtime_shared_retain" ~result:"void " ~parameters:"void *value";
    runtime_function "t_runtime_shared_release" ~result:"uint8_t " ~parameters:"void *value";
    runtime_function "t_runtime_shared_free" ~result:"void " ~parameters:"void *value";
    runtime_function "t_runtime_shared_lock" ~result:"void " ~parameters:"void *value";
    runtime_function "t_runtime_shared_unlock" ~result:"void " ~parameters:"void *value";
    runtime_function "t_runtime_blocking_begin" ~result:"void " ~parameters:"void";
    runtime_function "t_runtime_blocking_end" ~result:"void " ~parameters:"void";
    declaration "t_compare_bytes"
      {|static inline int32_t t_compare_bytes(const void *first, const void *second, t_usize count) {
  int order = __builtin_memcmp(first, second, count);
  return (order > 0) - (order < 0);
}
|};
    declaration "t_float64_bits"
      {|static inline uint64_t t_float64_bits(double value) {
  uint64_t bits;
  if (value != value) return 0x7ff8000000000000ULL;
  __builtin_memcpy(&bits, &value, 8);
  return bits;
}
|};
    declaration "t_float32_bits"
      {|static inline uint32_t t_float32_bits(float value) {
  uint32_t bits;
  if (value != value) return 0x7fc00000U;
  __builtin_memcpy(&bits, &value, 4);
  return bits;
}
|};
    declaration "t_float64_from_bits"
      {|static inline double t_float64_from_bits(uint64_t bits) {
  double value;
  __builtin_memcpy(&value, &bits, 8);
  return value;
}
|};
    declaration "t_float32_from_bits"
      {|static inline float t_float32_from_bits(uint32_t bits) {
  float value;
  __builtin_memcpy(&value, &bits, 4);
  return value;
}
|};
  ]

(* The text of the declarations named in [used] and of those their texts
   name, in the order of [declarations]. *)
let declarations_text build used =
  let all = declarations build in
  List.iter
    (fun name ->
      if not (List.exists (fun declaration -> declaration.name = name) all) then
        bug "no runtime declaration named %s" name)
    used;
  (* Each declaration comes after those it requires, so one pass from the
     last adds every declaration the used ones require. *)
  let required =
    List.fold_left
      (fun required declaration ->
        if List.mem declaration.name required then declaration.requires @ required else required)
      used (List.rev all)
  in
  String.concat ""
    (List.filter_map
       (fun declaration ->
         if List.mem declaration.name required then Some declaration.text else None)
       all)
