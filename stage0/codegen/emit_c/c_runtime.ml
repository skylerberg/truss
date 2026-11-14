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

(* The declarations every file starts with: the fixed-width integers, from the
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
      "struct t_site {\n\
      \  const struct t_anchor *anchor;\n\
      \  uint32_t line;\n\
      \  uint32_t column;\n\
       };\n";
      "_Noreturn void t_runtime_panic(const uint8_t *message, t_usize length, const struct \
       t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_assertion_failed(const uint8_t *message, t_usize length, const \
       struct t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_todo(const uint8_t *message, t_usize length, const struct t_anchor \
       *anchor, uint32_t line, uint32_t column);\n";
      "void t_runtime_echo(const uint8_t *text, t_usize length, const struct t_anchor *anchor, \
       uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_compiler_bug(void);\n";
      "struct t_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct t_evidence *const *outer;\n\
       };\n";
      "void *t_runtime_allocate(t_usize size, t_usize alignment);\n";
      "void *t_runtime_reallocate(void *pointer, t_usize old_size, t_usize size, t_usize alignment);\n";
      "void t_runtime_free(void *pointer);\n";
      "struct t_branch {\n  void (*run)(void *environment);\n  void *environment;\n};\n";
      "void t_runtime_parallel(const struct t_branch *branches, t_usize count);\n";
      "void t_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t \
       last), void *environment, uint64_t first, uint64_t last);\n";
      "t_usize t_runtime_coroutine_start(void (*code)(void *environment, uint64_t item), void \
       *environment, uint64_t item);\n";
      "uint8_t t_runtime_coroutine_resume(t_usize coroutine);\n";
      "void t_runtime_coroutine_suspend(void);\n";
      "uint8_t t_runtime_tasks_spawn(uint64_t group, void (*code)(void *environment, uint64_t \
       item), void *environment, uint64_t item);\n";
      "void t_runtime_run_test(uint32_t index);\n";
      "void t_runtime_report_tests_to(int32_t descriptor);\n";
      "t_usize t_runtime_live_blocks(void);\n";
    ]

(* Small functions that generated code calls, each emitted only into the
   files that use it. *)
let helpers =
  [
    ( "t_lend",
      {|struct t_lend_deferred {
  struct t_lend_deferred *next;
  void (*drop)(void *);
  void *target;
  const void *source;
  t_usize size;
};
struct t_lend_block {
  struct t_lend_block *next;
};
struct t_lend {
  struct t_lend_deferred *deferred;
  struct t_lend_block *blocks;
  t_usize used;
  t_usize lends;
  _Alignas(16) uint8_t storage[128];
};
struct t_lend_mark {
  struct t_lend_deferred *deferred_before;
  struct t_lend_deferred *deferred_after;
  struct t_lend_block *blocks_before;
  struct t_lend_block *blocks_after;
  t_usize used_before;
  t_usize used_after;
  uint8_t is_lent;
};
__attribute__((unused)) static inline void *t_lend_allocate(struct t_lend *lend, t_usize size, t_usize alignment) {
  t_usize start = (lend->used + alignment - 1) & ~(alignment - 1);
  if (alignment <= 16 && start + size <= sizeof lend->storage) {
    lend->used = start + size;
    return lend->storage + start;
  }
  t_usize block_alignment =
    alignment < _Alignof(struct t_lend_block) ? _Alignof(struct t_lend_block) : alignment;
  t_usize header = (sizeof(struct t_lend_block) + block_alignment - 1) & ~(block_alignment - 1);
  struct t_lend_block *block = t_runtime_allocate(header + size, block_alignment);
  block->next = lend->blocks;
  lend->blocks = block;
  return (uint8_t *)block + header;
}
__attribute__((unused)) static inline struct t_lend_deferred *t_lend_defer(struct t_lend *lend) {
  struct t_lend_deferred *deferred =
    t_lend_allocate(lend, sizeof(struct t_lend_deferred), _Alignof(struct t_lend_deferred));
  deferred->next = lend->deferred;
  deferred->drop = 0;
  deferred->target = 0;
  deferred->source = 0;
  deferred->size = 0;
  lend->deferred = deferred;
  return deferred;
}
__attribute__((unused)) static inline void t_lend_defer_drop(struct t_lend *lend, void *drop, void *value) {
  struct t_lend_deferred *deferred = t_lend_defer(lend);
  deferred->drop = (void (*)(void *))drop;
  deferred->target = value;
}
__attribute__((unused)) static inline void t_lend_defer_write_back(struct t_lend *lend, void *destination,
                                           const void *source, t_usize size) {
  struct t_lend_deferred *deferred = t_lend_defer(lend);
  deferred->target = destination;
  deferred->source = source;
  deferred->size = size;
}
__attribute__((unused)) static inline void t_lend_defer_free(struct t_lend *lend, void *block) {
  t_lend_defer(lend)->target = block;
}
__attribute__((unused)) static inline void t_lend_begin(struct t_lend *lend, struct t_lend_mark *mark) {
  mark->deferred_before = lend->deferred;
  mark->blocks_before = lend->blocks;
  mark->used_before = lend->used;
  mark->deferred_after = lend->deferred;
  mark->blocks_after = lend->blocks;
  mark->used_after = lend->used;
  mark->is_lent = 1;
  lend->lends += 1;
}
__attribute__((unused)) static inline void t_lend_called(struct t_lend *lend, struct t_lend_mark *mark) {
  mark->deferred_after = lend->deferred;
  mark->blocks_after = lend->blocks;
  mark->used_after = lend->used;
}
__attribute__((unused)) static inline void t_lend_free_blocks(struct t_lend *lend, struct t_lend_block *until) {
  while (lend->blocks != until) {
    struct t_lend_block *block = lend->blocks;
    lend->blocks = block->next;
    t_runtime_free(block);
  }
}
__attribute__((unused)) static inline void t_lend_release(struct t_lend *lend, struct t_lend_mark *mark) {
  if (!mark->is_lent) return;
  mark->is_lent = 0;
  for (struct t_lend_deferred *deferred = mark->deferred_after; deferred != mark->deferred_before;
       deferred = deferred->next) {
    if (deferred->drop) deferred->drop(deferred->target);
    else if (deferred->source) __builtin_memcpy(deferred->target, deferred->source, deferred->size);
    else if (deferred->target) t_runtime_free(deferred->target);
    deferred->drop = 0;
    deferred->target = 0;
    deferred->source = 0;
  }
  if (lend->deferred == mark->deferred_after && lend->blocks == mark->blocks_after &&
      lend->used == mark->used_after) {
    lend->deferred = mark->deferred_before;
    t_lend_free_blocks(lend, mark->blocks_before);
    lend->used = mark->used_before;
  }
  lend->lends -= 1;
  if (lend->lends == 0) {
    t_lend_free_blocks(lend, 0);
    lend->deferred = 0;
    lend->used = 0;
  }
}
__attribute__((unused)) static inline void t_lend_transfer(struct t_lend *lend, struct t_lend_mark *mark) {
  if (mark->is_lent) {
    mark->is_lent = 0;
    lend->lends -= 1;
  }
}
|}
    );
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
