type linkage = External | Internal
type failure = Echo | Todo

type helper =
  | Lend
  | Compare_bytes
  | Find_byte
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
  {|struct truss_lend {
  void (*release)(void *);
  void *context;
};
struct truss_lend_arena {
  uint64_t used;
  uint64_t top;
  _Alignas(16) uint8_t storage[256];
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
  | Find_byte -> "truss_find_byte"
  | Float64_bits -> "truss_float64_bits"
  | Float32_bits -> "truss_float32_bits"
  | Float64_from_bits -> "truss_float64_from_bits"
  | Float32_from_bits -> "truss_float32_from_bits"

let helpers =
  [
    ( Lend,
      {|struct truss_lend_held {
  struct truss_lend_arena *arena;
  uint32_t below;
  uint32_t is_free;
};
struct truss_lend_both {
  struct truss_lend first;
  struct truss_lend second;
};
struct truss_lend_write_back {
  void *destination;
  const void *source;
  uint64_t size;
  struct truss_lend next;
};
__attribute__((unused)) static inline void truss_lend_arena_init(struct truss_lend_arena *arena) {
  arena->used = 0;
  arena->top = 0;
}
__attribute__((unused, noinline)) static void *truss_lend_arena_allocate(struct truss_lend_arena *arena, uint64_t size, uint64_t alignment) {
  uint64_t end = arena->used + sizeof(struct truss_lend_held) + ((size + 15) & ~(uint64_t)15);
  if (alignment <= 16 && end <= sizeof arena->storage) {
    struct truss_lend_held *held = (struct truss_lend_held *)(arena->storage + arena->used);
    held->arena = arena;
    held->below = (uint32_t)arena->top;
    held->is_free = 0;
    arena->top = arena->used + 1;
    arena->used = end;
    return held + 1;
  }
  uint64_t block_alignment = alignment < 16 ? 16 : alignment;
  uint8_t *block = truss_runtime_allocate(block_alignment + size, block_alignment);
  struct truss_lend_held *held = (struct truss_lend_held *)(block + block_alignment) - 1;
  held->arena = 0;
  held->below = (uint32_t)block_alignment;
  return held + 1;
}
__attribute__((unused, noinline)) static void truss_lend_arena_free(void *allocation) {
  struct truss_lend_held *held = (struct truss_lend_held *)allocation - 1;
  struct truss_lend_arena *arena = held->arena;
  if (!arena) {
    truss_runtime_free((uint8_t *)allocation - held->below);
    return;
  }
  held->is_free = 1;
  while (arena->top) {
    struct truss_lend_held *top = (struct truss_lend_held *)(arena->storage + arena->top - 1);
    if (!top->is_free) break;
    arena->used = arena->top - 1;
    arena->top = top->below;
  }
}
__attribute__((unused)) static void truss_lend_release_both(void *context) {
  struct truss_lend_both both = *(struct truss_lend_both *)context;
  truss_lend_arena_free(context);
  both.first.release(both.first.context);
  both.second.release(both.second.context);
}
__attribute__((unused, noinline)) static void truss_lend_defer_before(struct truss_lend *lend, struct truss_lend_arena *arena,
                                                 struct truss_lend deferred) {
  struct truss_lend_both *both =
    truss_lend_arena_allocate(arena, sizeof(struct truss_lend_both), _Alignof(struct truss_lend_both));
  both->first = deferred;
  both->second = *lend;
  lend->release = truss_lend_release_both;
  lend->context = both;
}
__attribute__((unused)) static inline void truss_lend_defer(struct truss_lend *lend, struct truss_lend_arena *arena, void *release,
                                    void *context) {
  struct truss_lend deferred = { (void (*)(void *))release, context };
  if (lend->release) truss_lend_defer_before(lend, arena, deferred);
  else *lend = deferred;
}
__attribute__((unused)) static void truss_lend_write_back(void *context) {
  struct truss_lend_write_back write_back = *(struct truss_lend_write_back *)context;
  truss_lend_arena_free(context);
  __builtin_memcpy(write_back.destination, write_back.source, write_back.size);
  if (write_back.next.release) write_back.next.release(write_back.next.context);
}
__attribute__((unused, noinline)) static void truss_lend_defer_write_back(struct truss_lend *lend, struct truss_lend_arena *arena,
                                                     void *destination, const void *source, uint64_t size) {
  struct truss_lend_write_back *write_back = truss_lend_arena_allocate(
    arena, sizeof(struct truss_lend_write_back), _Alignof(struct truss_lend_write_back));
  write_back->destination = destination;
  write_back->source = source;
  write_back->size = size;
  write_back->next = *lend;
  lend->release = truss_lend_write_back;
  lend->context = write_back;
}
__attribute__((unused)) static inline void truss_lend_defer_free(struct truss_lend *lend, struct truss_lend_arena *arena, void *block) {
  truss_lend_defer(lend, arena, (void *)truss_runtime_free, block);
}
__attribute__((unused, noinline)) static void *truss_lend_allocate(struct truss_lend *lend, struct truss_lend_arena *arena, uint64_t size,
                                              uint64_t alignment) {
  void *slot = truss_lend_arena_allocate(arena, size, alignment);
  truss_lend_defer(lend, arena, (void *)truss_lend_arena_free, slot);
  return slot;
}
__attribute__((unused)) static inline void truss_lend_release(struct truss_lend *lend) {
  if (lend->release) {
    struct truss_lend released = *lend;
    lend->release = 0;
    released.release(released.context);
  }
}
__attribute__((unused)) static inline void truss_lend_transfer(struct truss_lend *caller, struct truss_lend_arena *arena,
                                       struct truss_lend *lend) {
  if (lend->release) {
    truss_lend_defer(caller, arena, (void *)lend->release, lend->context);
    lend->release = 0;
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
    ( Find_byte,
      {|static inline uint64_t truss_find_byte(const void *bytes, uint64_t count, uint8_t byte) {
  if (count == 0) {
    return 0;
  }
  const unsigned char *found = __builtin_memchr(bytes, byte, count);
  return found ? (uint64_t)(found - (const unsigned char *)bytes) : count;
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
