type linkage = External | Internal
type failure = Echo | Todo

type helper =
  | Lend
  | Compare_bytes
  | Float64_bits
  | Float32_bits
  | Float64_from_bits
  | Float32_from_bits

let raise_bug format = Compiler_bug.raise_bug ~stage:"Emit_c" format

let render_site_symbol (site : Lowered.site) =
  Printf.sprintf "truss_Site_%s_%d" (Mangling.mangle_path site.definition) site.offset

let render_capability_symbol capability = "truss_Capability_" ^ Mangling.mangle_path capability

let shared_structs =
  "struct truss_site {\n\
  \  const uint8_t *file;\n\
  \  uint64_t file_length;\n\
  \  uint32_t line;\n\
  \  uint32_t column;\n\
   };\n\
   struct truss_trace {\n\
  \  const struct truss_site *site;\n\
  \  const struct truss_trace *caller;\n\
   };\n\
   struct truss_capability {\n\
  \  const uint8_t *capability;\n\
  \  void *evidence;\n\
   };\n"

let render_integer_type : Memory_layout.integer -> string = function
  | Int8 -> "int8_t"
  | Int16 -> "int16_t"
  | Int32 -> "int32_t"
  | Int64 -> "int64_t"
  | UInt8 -> "uint8_t"
  | UInt16 -> "uint16_t"
  | UInt32 -> "uint32_t"
  | UInt64 -> "uint64_t"

let render_unsigned_type : Memory_layout.integer -> string = function
  | Int8 | UInt8 -> "uint8_t"
  | Int16 | UInt16 -> "uint16_t"
  | Int32 | UInt32 -> "uint32_t"
  | Int64 | UInt64 -> "uint64_t"

let is_signed : Memory_layout.integer -> bool = function
  | Int8 | Int16 | Int32 | Int64 -> true
  | UInt8 | UInt16 | UInt32 | UInt64 -> false

let lend_structs =
  {|struct truss_lend_deferred {
  struct truss_lend_deferred *next;
  void (*drop)(void *);
  void *target;
  const void *source;
  uint64_t size;
};
struct truss_lend_block {
  struct truss_lend_block *next;
};
struct truss_lend {
  struct truss_lend_deferred *deferred;
  struct truss_lend_block *blocks;
  uint64_t used;
  uint64_t lends;
  _Alignas(16) uint8_t storage[128];
};
struct truss_lend_mark {
  struct truss_lend_deferred *deferred_before;
  struct truss_lend_deferred *deferred_after;
  struct truss_lend_block *blocks_before;
  struct truss_lend_block *blocks_after;
  uint64_t used_before;
  uint64_t used_after;
  uint8_t is_lent;
};
|}

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
      shared_structs;
      "_Noreturn void truss_runtime_panic(const uint8_t *message, uint64_t length, const struct \
       truss_site *site, const struct truss_trace *trace);\n";
      "_Noreturn void truss_runtime_assertion_failed(const uint8_t *message, uint64_t length, \
       const struct truss_site *site);\n";
      "_Noreturn void truss_runtime_todo(const uint8_t *message, uint64_t length, const struct \
       truss_site *site);\n";
      "void truss_runtime_echo(const uint8_t *text, uint64_t length, const struct truss_site *site);\n";
      "_Noreturn void truss_runtime_compiler_bug(void);\n";
      "void *truss_runtime_find_capability(const struct truss_capability *capabilities, const \
       uint8_t *capability);\n";
      "struct truss_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct truss_evidence *const *outer;\n\
       };\n";
      "void *truss_runtime_allocate(uint64_t size, uint64_t alignment);\n";
      "void *truss_runtime_reallocate(void *pointer, uint64_t old_size, uint64_t size, uint64_t \
       alignment);\n";
      "void truss_runtime_free(void *pointer);\n";
      "struct truss_branch {\n  void (*run)(void *environment);\n  void *environment;\n};\n";
      "void truss_runtime_parallel(const struct truss_branch *branches, uint64_t count);\n";
      "void truss_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t \
       last), void *environment, uint64_t first, uint64_t last);\n";
      "uint64_t truss_runtime_coroutine_start(void (*code)(void *environment, uint64_t item, void \
       *capabilities), void *environment, uint64_t item);\n";
      "uint8_t truss_runtime_coroutine_resume(uint64_t coroutine);\n";
      "void truss_runtime_coroutine_suspend(void);\n";
      "uint8_t truss_runtime_tasks_spawn(uint64_t group, void (*code)(void *environment, uint64_t \
       item, void *capabilities), void *environment, uint64_t item);\n";
      "void truss_runtime_run_test(uint32_t index);\n";
      "void truss_runtime_report_tests_to(int32_t descriptor);\n";
      "uint64_t truss_runtime_live_blocks(void);\n";
      lend_structs;
    ]

let render_helper_name = function
  | Lend -> "truss_lend"
  | Compare_bytes -> "truss_compare_bytes"
  | Float64_bits -> "truss_float64_bits"
  | Float32_bits -> "truss_float32_bits"
  | Float64_from_bits -> "truss_float64_from_bits"
  | Float32_from_bits -> "truss_float32_from_bits"

let helpers =
  [
    ( Lend,
      {|__attribute__((unused)) static inline void *truss_lend_allocate(struct truss_lend *lend, uint64_t size, uint64_t alignment) {
  uint64_t start = (lend->used + alignment - 1) & ~(alignment - 1);
  if (alignment <= 16 && start + size <= sizeof lend->storage) {
    lend->used = start + size;
    return lend->storage + start;
  }
  uint64_t block_alignment =
    alignment < _Alignof(struct truss_lend_block) ? _Alignof(struct truss_lend_block) : alignment;
  uint64_t header = (sizeof(struct truss_lend_block) + block_alignment - 1) & ~(block_alignment - 1);
  struct truss_lend_block *block = truss_runtime_allocate(header + size, block_alignment);
  block->next = lend->blocks;
  lend->blocks = block;
  return (uint8_t *)block + header;
}
__attribute__((unused)) static inline struct truss_lend_deferred *truss_lend_defer(struct truss_lend *lend) {
  struct truss_lend_deferred *deferred =
    truss_lend_allocate(lend, sizeof(struct truss_lend_deferred), _Alignof(struct truss_lend_deferred));
  deferred->next = lend->deferred;
  deferred->drop = 0;
  deferred->target = 0;
  deferred->source = 0;
  deferred->size = 0;
  lend->deferred = deferred;
  return deferred;
}
__attribute__((unused)) static inline void truss_lend_defer_drop(struct truss_lend *lend, void *drop, void *value) {
  struct truss_lend_deferred *deferred = truss_lend_defer(lend);
  deferred->drop = (void (*)(void *))drop;
  deferred->target = value;
}
__attribute__((unused)) static inline void truss_lend_defer_write_back(struct truss_lend *lend, void *destination,
                                           const void *source, uint64_t size) {
  struct truss_lend_deferred *deferred = truss_lend_defer(lend);
  deferred->target = destination;
  deferred->source = source;
  deferred->size = size;
}
__attribute__((unused)) static inline void truss_lend_defer_free(struct truss_lend *lend, void *block) {
  truss_lend_defer(lend)->target = block;
}
__attribute__((unused)) static inline void truss_lend_begin(struct truss_lend *lend, struct truss_lend_mark *mark) {
  mark->deferred_before = lend->deferred;
  mark->blocks_before = lend->blocks;
  mark->used_before = lend->used;
  mark->deferred_after = lend->deferred;
  mark->blocks_after = lend->blocks;
  mark->used_after = lend->used;
  mark->is_lent = 1;
  lend->lends += 1;
}
__attribute__((unused)) static inline void truss_lend_called(struct truss_lend *lend, struct truss_lend_mark *mark) {
  mark->deferred_after = lend->deferred;
  mark->blocks_after = lend->blocks;
  mark->used_after = lend->used;
}
__attribute__((unused)) static inline void truss_lend_free_blocks(struct truss_lend *lend, struct truss_lend_block *until) {
  while (lend->blocks != until) {
    struct truss_lend_block *block = lend->blocks;
    lend->blocks = block->next;
    truss_runtime_free(block);
  }
}
__attribute__((unused)) static inline void truss_lend_release(struct truss_lend *lend, struct truss_lend_mark *mark) {
  if (!mark->is_lent) return;
  mark->is_lent = 0;
  for (struct truss_lend_deferred *deferred = mark->deferred_after; deferred != mark->deferred_before;
       deferred = deferred->next) {
    if (deferred->drop) deferred->drop(deferred->target);
    else if (deferred->source) __builtin_memcpy(deferred->target, deferred->source, deferred->size);
    else if (deferred->target) truss_runtime_free(deferred->target);
    deferred->drop = 0;
    deferred->target = 0;
    deferred->source = 0;
  }
  if (lend->deferred == mark->deferred_after && lend->blocks == mark->blocks_after &&
      lend->used == mark->used_after) {
    lend->deferred = mark->deferred_before;
    truss_lend_free_blocks(lend, mark->blocks_before);
    lend->used = mark->used_before;
  }
  lend->lends -= 1;
  if (lend->lends == 0) {
    truss_lend_free_blocks(lend, 0);
    lend->deferred = 0;
    lend->used = 0;
  }
}
__attribute__((unused)) static inline void truss_lend_transfer(struct truss_lend *lend, struct truss_lend_mark *mark) {
  if (mark->is_lent) {
    mark->is_lent = 0;
    lend->lends -= 1;
  }
}
|}
    );
    ( Compare_bytes,
      {|static inline int32_t truss_compare_bytes(const void *first, const void *second, uint64_t count) {
  int order = __builtin_memcmp(first, second, count);
  return (order > 0) - (order < 0);
}
|}
    );
    ( Float64_bits,
      {|static inline uint64_t truss_float64_bits(double value) {
  uint64_t bits;
  if (value != value) return 0x7ff8000000000000ULL;
  __builtin_memcpy(&bits, &value, 8);
  return bits;
}
|}
    );
    ( Float32_bits,
      {|static inline uint32_t truss_float32_bits(float value) {
  uint32_t bits;
  if (value != value) return 0x7fc00000U;
  __builtin_memcpy(&bits, &value, 4);
  return bits;
}
|}
    );
    ( Float64_from_bits,
      {|static inline double truss_float64_from_bits(uint64_t bits) {
  double value;
  __builtin_memcpy(&value, &bits, 8);
  return value;
}
|}
    );
    ( Float32_from_bits,
      {|static inline float truss_float32_from_bits(uint32_t bits) {
  float value;
  __builtin_memcpy(&value, &bits, 4);
  return value;
}
|}
    );
  ]
