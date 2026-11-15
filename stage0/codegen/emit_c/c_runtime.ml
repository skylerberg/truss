(* The C every file starts with: the build and linkage kinds, the
   runtime's declarations, and the helpers a file includes when it uses
   them. *)

type build = Development | Release
type linkage = External | Internal

(* A position in a definition, relative to the line it starts on. *)
type site = { definition : Path.t; line : int; column : int }
type failure = Echo | Todo

let bug format = Compiler_bug.bug ~stage:"Emit_c" format
let anchor_symbol definition = "t_Anchor_" ^ Instance.path_symbol definition

let anchor_struct =
  "struct t_anchor {\n  const uint8_t *path;\n  uint64_t path_length;\n  uint32_t line;\n};\n"

let integer_c : Memory_layout.integer -> string = function
  | Int8 -> "int8_t"
  | Int16 -> "int16_t"
  | Int32 -> "int32_t"
  | Int64 -> "int64_t"
  | UInt8 -> "uint8_t"
  | UInt16 -> "uint16_t"
  | UInt32 -> "uint32_t"
  | UInt64 -> "uint64_t"

let unsigned_c : Memory_layout.integer -> string = function
  | Int8 | UInt8 -> "uint8_t"
  | Int16 | UInt16 -> "uint16_t"
  | Int32 | UInt32 -> "uint32_t"
  | Int64 | UInt64 -> "uint64_t"

let signed : Memory_layout.integer -> bool = function
  | Int8 | Int16 | Int32 | Int64 -> true
  | UInt8 | UInt16 | UInt32 | UInt64 -> false

let runtime_declarations =
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
      anchor_struct;
      "_Noreturn void t_runtime_panic(const uint8_t *message, uint64_t length, const struct \
       t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_assertion_failed(const uint8_t *message, uint64_t length, const \
       struct t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_todo(const uint8_t *message, uint64_t length, const struct \
       t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "void t_runtime_echo(const uint8_t *text, uint64_t length, const struct t_anchor *anchor, \
       uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_compiler_bug(void);\n";
      "struct t_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct t_evidence *const *outer;\n\
       };\n";
      "void *t_runtime_allocate(uint64_t size, uint64_t alignment);\n";
      "void *t_runtime_reallocate(void *pointer, uint64_t old_size, uint64_t size, uint64_t \
       alignment);\n";
      "void t_runtime_free(void *pointer);\n";
      "struct t_branch {\n  void (*run)(void *environment);\n  void *environment;\n};\n";
      "void t_runtime_parallel(const struct t_branch *branches, uint64_t count);\n";
      "void t_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t \
       last), void *environment, uint64_t first, uint64_t last);\n";
      "uint64_t t_runtime_coroutine_start(void (*code)(void *environment, uint64_t item), void \
       *environment, uint64_t item);\n";
      "uint8_t t_runtime_coroutine_resume(uint64_t coroutine);\n";
      "void t_runtime_coroutine_suspend(void);\n";
      "uint8_t t_runtime_tasks_spawn(uint64_t group, void (*code)(void *environment, uint64_t \
       item), void *environment, uint64_t item);\n";
      "void t_runtime_run_test(uint32_t index);\n";
      "void t_runtime_report_tests_to(int32_t descriptor);\n";
      "uint64_t t_runtime_live_blocks(void);\n";
    ]

(* Small functions that generated code calls, each emitted only into the
   files that use it. *)
let helpers =
  [
    ( "t_compare_bytes",
      {|static inline int32_t t_compare_bytes(const void *first, const void *second, uint64_t count) {
  int order = __builtin_memcmp(first, second, count);
  return (order > 0) - (order < 0);
}
|}
    );
    ( "t_float64_bits",
      {|static inline uint64_t t_float64_bits(double value) {
  uint64_t bits;
  if (value != value) return 0x7ff8000000000000ULL;
  __builtin_memcpy(&bits, &value, 8);
  return bits;
}
|}
    );
    ( "t_float32_bits",
      {|static inline uint32_t t_float32_bits(float value) {
  uint32_t bits;
  if (value != value) return 0x7fc00000U;
  __builtin_memcpy(&bits, &value, 4);
  return bits;
}
|}
    );
    ( "t_float64_from_bits",
      {|static inline double t_float64_from_bits(uint64_t bits) {
  double value;
  __builtin_memcpy(&value, &bits, 8);
  return value;
}
|}
    );
    ( "t_float32_from_bits",
      {|static inline float t_float32_from_bits(uint32_t bits) {
  float value;
  __builtin_memcpy(&value, &bits, 4);
  return value;
}
|}
    );
  ]
