(* The C every file starts with: the build and linkage kinds, the
   runtime's declarations, and the helpers a file includes when it uses
   them. *)

type build = Development | Release
type linkage = External | Internal

let bug format = Printf.ksprintf (fun message -> invalid_arg ("Emit_c: " ^ message)) format
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

(* What every file declares first: the fixed-width integers, from the
   compiler's own predefined macros, the target's [USize], and the runtime. *)
let runtime_declarations (target : Memory_layout.target) =
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
      anchor_struct;
      "_Noreturn void t_runtime_panic(const uint8_t *message, t_usize length, const struct \
       t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_assertion_failed(const uint8_t *message, t_usize length, const \
       struct t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_todo(const uint8_t *message, t_usize length, const struct t_anchor \
       *anchor, uint32_t line, uint32_t column);\n";
      "void t_runtime_echo(const uint8_t *text, t_usize length, const struct t_anchor *anchor, \
       uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_compiler_bug(void);\n";
      "uint8_t *t_runtime_program_argument(void *arguments, int32_t index, t_usize *length);\n";
      "struct t_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct t_evidence *const *outer;\n\
       };\n";
      "void *t_runtime_allocate(t_usize size, t_usize alignment);\n";
      "void *t_runtime_reallocate(void *pointer, t_usize old_size, t_usize size, t_usize alignment);\n";
      "void t_runtime_free(void *pointer);\n";
      "void t_runtime_storage_grow(void **buffer, t_usize length, t_usize *capacity, t_usize size, \
       t_usize alignment, t_usize minimum);\n";
      "t_isize t_runtime_write(int32_t descriptor, const uint8_t *bytes, t_usize count);\n";
      "t_isize t_runtime_read(int32_t descriptor, uint8_t *bytes, t_usize count);\n";
      "t_usize t_runtime_float32_text(float value, uint8_t *bytes);\n";
      "int32_t t_runtime_open(const uint8_t *path, t_usize length, int32_t flags, int32_t *error);\n";
      "void t_runtime_close(int32_t descriptor);\n";
      "int32_t t_runtime_run(const uint8_t *program, t_usize length, const uint8_t *arguments, \
       t_usize arguments_length, int32_t *error);\n";
      "uint8_t *t_runtime_environment(const uint8_t *name, t_usize length, t_usize *value_length);\n";
      "t_usize t_runtime_float64_text(double value, uint8_t *bytes);\n";
      "int64_t t_runtime_clock_now(void);\n";
      "void t_runtime_random_fill(uint8_t *bytes, t_usize count);\n";
      "void t_runtime_debug_begin(void);\n";
      "void t_runtime_debug_text(const void *bytes, t_usize count);\n";
      "void t_runtime_debug_signed(int64_t value);\n";
      "void t_runtime_debug_unsigned(uint64_t value);\n";
      "void t_runtime_debug_float32(float value);\n";
      "void t_runtime_debug_float64(double value);\n";
      "void t_runtime_debug_bool(uint8_t value);\n";
      "void t_runtime_debug_character(uint32_t value);\n";
      "void t_runtime_debug_string(const uint8_t *bytes, t_usize count);\n";
      "uint8_t *t_runtime_debug_bytes(void);\n";
      "t_usize t_runtime_debug_length(void);\n";
    ]

(* Small functions that generated code calls, each emitted only into the
   files that use it. *)
let helpers =
  [
    ( "t_compare_bytes",
      {|static inline int32_t t_compare_bytes(const void *first, const void *second, t_usize count) {
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
