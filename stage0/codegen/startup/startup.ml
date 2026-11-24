let headers =
  {|#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <spawn.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <poll.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/socket.h>
#ifdef __linux__
#include <sys/epoll.h>
#include <sys/timerfd.h>
#else
#include <sys/event.h>
#endif
#include <netinet/in.h>
#include <netdb.h>
#if defined(__x86_64__)
#include <cpuid.h>
#endif
|}

let failing =
  {|
#if defined(__x86_64__)
#define TRUSS_BASELINE_CPU __attribute__((target("arch=x86-64")))
#else
#define TRUSS_BASELINE_CPU
#endif

TRUSS_BASELINE_CPU static void truss_write_all(int descriptor, const void *bytes, size_t length) {
  const char *next = bytes;
  while (length > 0) {
    ssize_t written = write(descriptor, next, length);
    if (written < 0) {
      if (errno == EINTR) continue;
      return;
    }
    next += written;
    length -= (size_t)written;
  }
}

__attribute__((noinline)) int *truss_runtime_errno_address_uncached(void) {
  __asm__ __volatile__("");
  return &errno;
}

void *truss_runtime_allocate(uint64_t size, uint64_t alignment);

static int truss_report = -1;

void truss_runtime_report_tests_to(int32_t descriptor) { truss_report = descriptor; }

enum { truss_passed, truss_failed, truss_panicked, truss_incomplete, truss_echoed, truss_timed_out };

static char truss_text[65536];
static size_t truss_text_length;
static pthread_mutex_t truss_text_lock = PTHREAD_MUTEX_INITIALIZER;

static void truss_text_add(const void *bytes, size_t length) {
  size_t room = sizeof truss_text - truss_text_length;
  if (length > room) length = room;
  memcpy(truss_text + truss_text_length, bytes, length);
  truss_text_length += length;
}

static void truss_text_string(const char *text) { truss_text_add(text, strlen(text)); }

static void truss_text_number(uint64_t number) {
  char digits[20];
  size_t count = 0;
  do {
    digits[sizeof digits - 1 - count] = (char)('0' + number % 10);
    number /= 10;
    count += 1;
  } while (number > 0);
  truss_text_add(digits + sizeof digits - count, count);
}

static void truss_text_position(const struct truss_site *site) {
  truss_text_add(site->file, site->file_length);
  truss_text_string(":");
  truss_text_number(site->line);
  truss_text_string(":");
  truss_text_number(site->column);
}

static void truss_record(uint8_t kind) {
  uint8_t header[5];
  uint32_t length = (uint32_t)truss_text_length;
  header[0] = kind;
  for (int byte = 0; byte < 4; byte++) header[1 + byte] = (uint8_t)(length >> (8 * byte));
  truss_write_all(truss_report, header, sizeof header);
  truss_write_all(truss_report, truss_text, truss_text_length);
}

static _Noreturn void truss_end(uint8_t kind, const char *heading, int status) {
  if (truss_report >= 0) {
    truss_record(kind);
    _exit(status);
  }
  truss_write_all(2, heading, strlen(heading));
  truss_write_all(2, truss_text, truss_text_length);
  truss_write_all(2, "\n", 1);
  _exit(status);
}

static void truss_describe(const uint8_t *message, uint64_t length, const struct truss_site *site) {
  pthread_mutex_lock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_add(message, length);
  truss_text_string("\n  at ");
  truss_text_position(site);
}

_Noreturn void truss_runtime_panic(const uint8_t *message, uint64_t length, const struct truss_site *site, const struct truss_trace *trace) {
  truss_describe(message, length, site);
  for (const struct truss_trace *link = trace; link != 0; link = link->caller) {
    truss_text_string("\n  called at ");
    truss_text_position(link->site);
  }
  truss_end(truss_panicked, "panic: ", 101);
}

_Noreturn void truss_runtime_assertion_failed(const uint8_t *message, uint64_t length, const struct truss_site *site) {
  truss_describe(message, length, site);
  truss_end(truss_failed, "assertion failed: ", 1);
}

_Noreturn void truss_runtime_todo(const uint8_t *message, uint64_t length, const struct truss_site *site) {
  truss_describe(message, length, site);
  truss_end(truss_incomplete, "", 101);
}

void truss_runtime_echo(const uint8_t *text, uint64_t length, const struct truss_site *site) {
  pthread_mutex_lock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_position(site);
  truss_text_string(": ");
  truss_text_add(text, length);
  if (truss_report >= 0) {
    truss_record(truss_echoed);
  } else {
    truss_write_all(2, "echo ", 5);
    truss_write_all(2, truss_text, truss_text_length);
    truss_write_all(2, "\n", 1);
  }
  pthread_mutex_unlock(&truss_text_lock);
}

_Noreturn void truss_runtime_compiler_bug(void) {
  pthread_mutex_lock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_string("reached code the prover showed unreachable");
  truss_end(truss_panicked, "compiler bug: ", 101);
}

void *truss_runtime_find_capability(const struct truss_capability *capabilities,
                                const uint8_t *capability) {
  for (const struct truss_capability *entry = capabilities; entry != 0 && entry->capability != 0;
       entry++) {
    if (entry->capability == capability) return entry->evidence;
  }
  truss_runtime_compiler_bug();
}

static _Noreturn void truss_out_of_memory(void) {
  pthread_mutex_lock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_string("out of memory");
  if (truss_report >= 0) truss_end(truss_panicked, "", 101);
  truss_write_all(2, "out of memory\n", 14);
  abort();
}

static char truss_signal_stack[65536];

static void truss_stack_overflow(int signal) {
  (void)signal;
  (void)pthread_mutex_trylock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_string("stack overflow");
  truss_end(truss_panicked, "", 101);
}

static void truss_install_signal_dispositions(void) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  stack.ss_sp = truss_signal_stack;
  stack.ss_size = sizeof truss_signal_stack;
  sigaltstack(&stack, NULL);
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = truss_stack_overflow;
  action.sa_flags = SA_ONSTACK;
  sigemptyset(&action.sa_mask);
  sigaction(SIGSEGV, &action, NULL);
  sigaction(SIGBUS, &action, NULL);
  signal(SIGPIPE, SIG_IGN);
  sigset_t runtime;
  sigemptyset(&runtime);
  sigaddset(&runtime, SIGSEGV);
  sigaddset(&runtime, SIGBUS);
  sigaddset(&runtime, SIGURG);
  pthread_sigmask(SIG_UNBLOCK, &runtime, NULL);
}
|}

let assumed_cpu_features =
  {|
#if defined(__x86_64__)
enum { truss_cpuid_1_ecx, truss_cpuid_7_ebx, truss_cpuid_80000001_ecx, truss_cpuid_registers };
enum { truss_osxsave_bit = 27, truss_xcr0_sse_and_avx_state = 6 };

struct truss_cpu_feature {
  const char *name;
  uint8_t cpuid_register;
  uint8_t bit;
  uint8_t needs_avx_state;
};

static const struct truss_cpu_feature truss_assumed_cpu_features[] = {
#ifdef __SSE3__
    {"SSE3", truss_cpuid_1_ecx, 0, 0},
#endif
#ifdef __SSSE3__
    {"SSSE3", truss_cpuid_1_ecx, 9, 0},
#endif
#ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_16
    {"CMPXCHG16B", truss_cpuid_1_ecx, 13, 0},
#endif
#ifdef __SSE4_1__
    {"SSE4.1", truss_cpuid_1_ecx, 19, 0},
#endif
#ifdef __SSE4_2__
    {"SSE4.2", truss_cpuid_1_ecx, 20, 0},
#endif
#ifdef __POPCNT__
    {"POPCNT", truss_cpuid_1_ecx, 23, 0},
#endif
#ifdef __LAHF_SAHF__
    {"LAHF-SAHF", truss_cpuid_80000001_ecx, 0, 0},
#endif
#ifdef __AVX__
    {"AVX", truss_cpuid_1_ecx, 28, 1},
#endif
#ifdef __AVX2__
    {"AVX2", truss_cpuid_7_ebx, 5, 1},
#endif
#ifdef __FMA__
    {"FMA", truss_cpuid_1_ecx, 12, 1},
#endif
#ifdef __F16C__
    {"F16C", truss_cpuid_1_ecx, 29, 1},
#endif
#ifdef __BMI__
    {"BMI1", truss_cpuid_7_ebx, 3, 0},
#endif
#ifdef __BMI2__
    {"BMI2", truss_cpuid_7_ebx, 8, 0},
#endif
#ifdef __LZCNT__
    {"LZCNT", truss_cpuid_80000001_ecx, 5, 0},
#endif
#ifdef __MOVBE__
    {"MOVBE", truss_cpuid_1_ecx, 22, 0},
#endif
#ifdef __XSAVE__
    {"OSXSAVE", truss_cpuid_1_ecx, truss_osxsave_bit, 0},
#endif
    {NULL, 0, 0, 0},
};

__attribute__((constructor)) TRUSS_BASELINE_CPU static void truss_require_assumed_cpu_features(void) {
  unsigned int eax, ebx, ecx, edx;
  unsigned int registers[truss_cpuid_registers] = {0};
  __cpuid(0, eax, ebx, ecx, edx);
  unsigned int highest_leaf = eax;
  if (highest_leaf >= 1) {
    __cpuid(1, eax, ebx, ecx, edx);
    registers[truss_cpuid_1_ecx] = ecx;
  }
  if (highest_leaf >= 7) {
    __cpuid_count(7, 0, eax, ebx, ecx, edx);
    registers[truss_cpuid_7_ebx] = ebx;
  }
  __cpuid(0x80000000, eax, ebx, ecx, edx);
  if (eax >= 0x80000001) {
    __cpuid(0x80000001, eax, ebx, ecx, edx);
    registers[truss_cpuid_80000001_ecx] = ecx;
  }
  int has_avx_state = 0;
  if (registers[truss_cpuid_1_ecx] >> truss_osxsave_bit & 1) {
    unsigned int low, high;
    __asm__ __volatile__("xgetbv" : "=a"(low), "=d"(high) : "c"(0));
    has_avx_state = (low & truss_xcr0_sse_and_avx_state) == truss_xcr0_sse_and_avx_state;
  }
  for (const struct truss_cpu_feature *feature = truss_assumed_cpu_features; feature->name != NULL; feature++) {
    if ((registers[feature->cpuid_register] >> feature->bit & 1) && (has_avx_state || !feature->needs_avx_state))
      continue;
    static const char needs[] = "This program needs a CPU with ";
    static const char lacks[] =
        ", which this machine lacks. Build the program with TRUSS_CFLAGS=-march=x86-64 to run it on every "
        "x86-64 CPU.\n";
    size_t name_length = 0;
    while (feature->name[name_length] != 0) name_length += 1;
    truss_write_all(2, needs, sizeof needs - 1);
    truss_write_all(2, feature->name, name_length);
    truss_write_all(2, lacks, sizeof lacks - 1);
    _exit(126);
  }
}
#endif
|}

let allocation =
  {|
#ifdef TRUSS_TESTS
static _Atomic uint64_t truss_live_blocks;
#define TRUSS_BLOCK_ALLOCATED() \
  ((void)atomic_fetch_add_explicit(&truss_live_blocks, 1, memory_order_relaxed))
#define TRUSS_BLOCK_FREED() ((void)atomic_fetch_sub_explicit(&truss_live_blocks, 1, memory_order_relaxed))
uint64_t truss_runtime_live_blocks(void) {
  return atomic_load_explicit(&truss_live_blocks, memory_order_relaxed);
}
#else
#define TRUSS_BLOCK_ALLOCATED() ((void)0)
#define TRUSS_BLOCK_FREED() ((void)0)
#endif

void *truss_runtime_allocate(uint64_t size, uint64_t alignment) {
  void *pointer = NULL;
  if (size == 0) size = 1;
  if (alignment <= 16) {
    pointer = malloc(size);
  } else if (posix_memalign(&pointer, alignment, size) != 0) {
    pointer = NULL;
  }
  if (pointer == NULL) truss_out_of_memory();
  TRUSS_BLOCK_ALLOCATED();
  return pointer;
}

void truss_runtime_free(void *pointer) {
  TRUSS_BLOCK_FREED();
  free(pointer);
}

void *truss_runtime_reallocate(void *pointer, uint64_t old_size, uint64_t size, uint64_t alignment) {
  if (size == 0) size = 1;
  if (alignment <= 16) {
    void *moved = realloc(pointer, size);
    if (moved == NULL) truss_out_of_memory();
    return moved;
  }
  void *moved = truss_runtime_allocate(size, alignment);
  memcpy(moved, pointer, old_size < size ? old_size : size);
  truss_runtime_free(pointer);
  return moved;
}

|}

let threads =
  {|
static size_t truss_stack_size(void) {
  struct rlimit limit;
  size_t stack = (size_t)8 << 20;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY &&
      limit.rlim_cur >= ((rlim_t)1 << 16) && limit.rlim_cur <= ((rlim_t)1 << 30))
    stack = (size_t)limit.rlim_cur;
  return stack;
}

static void truss_thread_signal_stack_install(void) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  stack.ss_sp = malloc(65536);
  if (stack.ss_sp == NULL) return;
  stack.ss_size = 65536;
  if (sigaltstack(&stack, NULL) != 0) free(stack.ss_sp);
}

static void truss_thread_attributes(pthread_attr_t *attributes) {
  pthread_attr_init(attributes);
  pthread_attr_setstacksize(attributes, truss_stack_size());
}

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define TRUSS_ADDRESS_SANITIZER 1
#endif
#if __has_feature(thread_sanitizer)
#define TRUSS_THREAD_SANITIZER 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__) && !defined(TRUSS_ADDRESS_SANITIZER)
#define TRUSS_ADDRESS_SANITIZER 1
#endif
#if defined(__SANITIZE_THREAD__) && !defined(TRUSS_THREAD_SANITIZER)
#define TRUSS_THREAD_SANITIZER 1
#endif

#ifdef TRUSS_ADDRESS_SANITIZER
void __sanitizer_start_switch_fiber(void **fake_stack_save, const void *bottom, size_t size);
void __sanitizer_finish_switch_fiber(void *fake_stack_save, const void **bottom_old,
                                     size_t *size_old);
void __asan_unpoison_memory_region(void const volatile *address, size_t size);
#endif
#ifdef TRUSS_THREAD_SANITIZER
void *__tsan_get_current_fiber(void);
void *__tsan_create_fiber(unsigned flags);
void __tsan_destroy_fiber(void *fiber);
void __tsan_switch_to_fiber(void *fiber, unsigned flags);
const char *__tsan_default_options(void);
__attribute__((visibility("default"), used)) const char *__tsan_default_options(void) {
  return "halt_on_error=1";
}
#endif

#define TRUSS_STACK_CACHE 64

static pthread_mutex_t truss_stack_lock = PTHREAD_MUTEX_INITIALIZER;
static void *truss_stack_cache[TRUSS_STACK_CACHE];
static size_t truss_stack_cached;
static size_t truss_stack_bytes;
static size_t truss_stack_guard;

static void *truss_stack_acquire(void) {
  pthread_mutex_lock(&truss_stack_lock);
  if (truss_stack_bytes == 0) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    truss_stack_guard = page;
    truss_stack_bytes = (truss_stack_size() + page - 1) / page * page;
  }
  void *low = truss_stack_cached > 0 ? truss_stack_cache[--truss_stack_cached] : NULL;
  pthread_mutex_unlock(&truss_stack_lock);
  if (low != NULL) return low;
  int flags = MAP_PRIVATE | MAP_ANON;
#ifdef MAP_NORESERVE
  flags |= MAP_NORESERVE;
#endif
#ifdef MAP_STACK
  flags |= MAP_STACK;
#endif
  char *mapping = mmap(NULL, truss_stack_guard + truss_stack_bytes, PROT_READ | PROT_WRITE, flags, -1, 0);
  if (mapping == MAP_FAILED) truss_out_of_memory();
  if (mprotect(mapping, truss_stack_guard, PROT_NONE) != 0) truss_out_of_memory();
  return mapping + truss_stack_guard;
}

static void truss_stack_release(void *low) {
#ifdef TRUSS_ADDRESS_SANITIZER
  __asan_unpoison_memory_region(low, truss_stack_bytes);
#endif
  pthread_mutex_lock(&truss_stack_lock);
  if (truss_stack_cached < TRUSS_STACK_CACHE) {
    truss_stack_cache[truss_stack_cached++] = low;
    low = NULL;
  }
  pthread_mutex_unlock(&truss_stack_lock);
  if (low != NULL) munmap((char *)low - truss_stack_guard, truss_stack_guard + truss_stack_bytes);
}

struct truss_context {
  void *stack_pointer;
};

void truss_context_switch(struct truss_context *from, const struct truss_context *to);

#ifdef __APPLE__
#define TRUSS_ASSEMBLY_NAME(name) "_" name
#else
#define TRUSS_ASSEMBLY_NAME(name) name
#endif

#if defined(__x86_64__)
__asm__(".text\n"
        ".globl " TRUSS_ASSEMBLY_NAME("truss_context_switch") "\n"
        ".p2align 4\n"
        TRUSS_ASSEMBLY_NAME("truss_context_switch") ":\n"
        "  pushq %rbp\n"
        "  pushq %rbx\n"
        "  pushq %r12\n"
        "  pushq %r13\n"
        "  pushq %r14\n"
        "  pushq %r15\n"
        "  movq %rsp, (%rdi)\n"
        "  movq (%rsi), %rsp\n"
        "  popq %r15\n"
        "  popq %r14\n"
        "  popq %r13\n"
        "  popq %r12\n"
        "  popq %rbx\n"
        "  popq %rbp\n"
        "  retq\n");

static void truss_context_start(struct truss_context *context, void *low, size_t size, void (*entry)(void)) {
  uint64_t *top = (uint64_t *)(((uintptr_t)low + size) & ~(uintptr_t)15);
  *--top = 0;
  *--top = (uint64_t)(uintptr_t)entry;
  for (int saved = 0; saved < 6; saved++) *--top = 0;
  context->stack_pointer = top;
}
#elif defined(__aarch64__)
__asm__(".text\n"
        ".globl " TRUSS_ASSEMBLY_NAME("truss_context_switch") "\n"
        ".p2align 2\n"
        TRUSS_ASSEMBLY_NAME("truss_context_switch") ":\n"
        "  sub sp, sp, #160\n"
        "  stp x19, x20, [sp, #0]\n"
        "  stp x21, x22, [sp, #16]\n"
        "  stp x23, x24, [sp, #32]\n"
        "  stp x25, x26, [sp, #48]\n"
        "  stp x27, x28, [sp, #64]\n"
        "  stp x29, x30, [sp, #80]\n"
        "  stp d8, d9, [sp, #96]\n"
        "  stp d10, d11, [sp, #112]\n"
        "  stp d12, d13, [sp, #128]\n"
        "  stp d14, d15, [sp, #144]\n"
        "  mov x9, sp\n"
        "  str x9, [x0]\n"
        "  ldr x9, [x1]\n"
        "  mov sp, x9\n"
        "  ldp x19, x20, [sp, #0]\n"
        "  ldp x21, x22, [sp, #16]\n"
        "  ldp x23, x24, [sp, #32]\n"
        "  ldp x25, x26, [sp, #48]\n"
        "  ldp x27, x28, [sp, #64]\n"
        "  ldp x29, x30, [sp, #80]\n"
        "  ldp d8, d9, [sp, #96]\n"
        "  ldp d10, d11, [sp, #112]\n"
        "  ldp d12, d13, [sp, #128]\n"
        "  ldp d14, d15, [sp, #144]\n"
        "  add sp, sp, #160\n"
        "  ret\n");

static void truss_context_start(struct truss_context *context, void *low, size_t size, void (*entry)(void)) {
  uint64_t *top = (uint64_t *)(((uintptr_t)low + size) & ~(uintptr_t)15);
  uint64_t *saved = top - 20;
  memset(saved, 0, 160);
  saved[11] = (uint64_t)(uintptr_t)entry;
  context->stack_pointer = saved;
}
#else
#error "the runtime has no context switch for this processor"
#endif

struct truss_coroutine {
  struct truss_context context;
  struct truss_context resumer;
  void *stack;
  int finished;
  void (*code)(void *environment, uint64_t item, void *capabilities);
  void *environment;
  uint64_t item;
#ifdef TRUSS_ADDRESS_SANITIZER
  const void *resumer_stack;
  size_t resumer_stack_size;
#endif
#ifdef TRUSS_THREAD_SANITIZER
  void *fiber;
  void *resumer_fiber;
#endif
};

static _Thread_local struct truss_coroutine *truss_coroutine_self;

__attribute__((noinline)) static struct truss_coroutine *truss_coroutine_current(void) {
  __asm__ __volatile__("");
  return truss_coroutine_self;
}

__attribute__((noinline)) static void truss_coroutine_current_set(struct truss_coroutine *coroutine) {
  __asm__ __volatile__("");
  truss_coroutine_self = coroutine;
}

static void truss_coroutine_leave(struct truss_coroutine *coroutine) {
#ifdef TRUSS_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(coroutine->finished ? NULL : &fake, coroutine->resumer_stack,
                                 coroutine->resumer_stack_size);
#endif
#ifdef TRUSS_THREAD_SANITIZER
  __tsan_switch_to_fiber(coroutine->resumer_fiber, 0);
#endif
  truss_context_switch(&coroutine->context, &coroutine->resumer);
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &coroutine->resumer_stack,
                                  &coroutine->resumer_stack_size);
#endif
}

static void truss_coroutine_entry(void) {
  struct truss_coroutine *coroutine = truss_coroutine_current();
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(NULL, &coroutine->resumer_stack,
                                  &coroutine->resumer_stack_size);
#endif
  coroutine->code(coroutine->environment, coroutine->item, 0);
  coroutine->finished = 1;
  truss_coroutine_leave(coroutine);
  truss_runtime_compiler_bug();
}

uint64_t truss_runtime_coroutine_start(void (*code)(void *environment, uint64_t item, void *capabilities), void *environment,
                                  uint64_t item) {
  struct truss_coroutine *coroutine = malloc(sizeof *coroutine);
  if (coroutine == NULL) truss_out_of_memory();
  coroutine->stack = truss_stack_acquire();
  coroutine->finished = 0;
  coroutine->code = code;
  coroutine->environment = environment;
  coroutine->item = item;
  truss_context_start(&coroutine->context, coroutine->stack, truss_stack_bytes, truss_coroutine_entry);
#ifdef TRUSS_THREAD_SANITIZER
  coroutine->fiber = __tsan_create_fiber(0);
#endif
  return (uint64_t)coroutine;
}

uint8_t truss_runtime_coroutine_resume(uint64_t handle) {
  struct truss_coroutine *coroutine = (struct truss_coroutine *)handle;
  struct truss_coroutine *resumer = truss_coroutine_current();
  truss_coroutine_current_set(coroutine);
#ifdef TRUSS_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(&fake, coroutine->stack, truss_stack_bytes);
#endif
#ifdef TRUSS_THREAD_SANITIZER
  coroutine->resumer_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(coroutine->fiber, 0);
#endif
  truss_context_switch(&coroutine->resumer, &coroutine->context);
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, NULL, NULL);
#endif
  truss_coroutine_current_set(resumer);
  if (!coroutine->finished) return 1;
#ifdef TRUSS_THREAD_SANITIZER
  __tsan_destroy_fiber(coroutine->fiber);
#endif
  truss_stack_release(coroutine->stack);
  free(coroutine);
  return 0;
}

void truss_runtime_coroutine_suspend(void) {
  struct truss_coroutine *coroutine = truss_coroutine_current();
  if (coroutine == NULL) truss_runtime_compiler_bug();
  truss_coroutine_leave(coroutine);
}

struct truss_shared {
  void *block;
  atomic_size_t count;
  pthread_mutex_t mutex;
};

static struct truss_shared *truss_shared_header(void *value) { return (struct truss_shared *)value - 1; }

void *truss_runtime_shared_allocate(uint64_t size, uint64_t alignment) {
  if (alignment < _Alignof(struct truss_shared)) alignment = _Alignof(struct truss_shared);
  uint64_t offset = (sizeof(struct truss_shared) + alignment - 1) / alignment * alignment;
  char *block = truss_runtime_allocate(offset + size, alignment);
  struct truss_shared *shared = truss_shared_header(block + offset);
  shared->block = block;
  atomic_init(&shared->count, 1);
  pthread_mutex_init(&shared->mutex, NULL);
  return block + offset;
}

void truss_runtime_shared_retain(void *value) {
  atomic_fetch_add_explicit(&truss_shared_header(value)->count, 1, memory_order_relaxed);
}

uint8_t truss_runtime_shared_release(void *value) {
  if (atomic_fetch_sub_explicit(&truss_shared_header(value)->count, 1, memory_order_release) != 1)
    return 0;
  atomic_thread_fence(memory_order_acquire);
  return 1;
}

void truss_runtime_shared_free(void *value) {
  struct truss_shared *shared = truss_shared_header(value);
  pthread_mutex_destroy(&shared->mutex);
  truss_runtime_free(shared->block);
}

void truss_runtime_shared_lock(void *value) { pthread_mutex_lock(&truss_shared_header(value)->mutex); }

void truss_runtime_shared_unlock(void *value) { pthread_mutex_unlock(&truss_shared_header(value)->mutex); }

static uint64_t truss_descriptor_limit(int32_t descriptor, int32_t writing) {
  struct timeval limit;
  socklen_t size = sizeof limit;
  if (getsockopt(descriptor, SOL_SOCKET, writing ? SO_SNDTIMEO : SO_RCVTIMEO, &limit, &size) != 0)
    return 0;
  return (uint64_t)limit.tv_sec * 1000000000u + (uint64_t)limit.tv_usec * 1000u;
}

static int32_t truss_descriptor_poll(int32_t descriptor, int32_t writing) {
  uint64_t limit = truss_descriptor_limit(descriptor, writing);
  uint64_t milliseconds = (limit + 999999u) / 1000000u;
  struct pollfd one = {descriptor, writing ? POLLOUT : POLLIN, 0};
  int timeout = limit == 0 ? -1 : milliseconds > INT32_MAX ? INT32_MAX : (int)milliseconds;
  return poll(&one, 1, timeout) != 0;
}

static void truss_descriptors_poll(const int32_t *descriptors, size_t count) {
  if (count == 0) return;
  struct pollfd *waited = malloc(count * sizeof *waited);
  if (waited == NULL) truss_out_of_memory();
  for (size_t index = 0; index < count; index++) {
    waited[index].fd = descriptors[index];
    waited[index].events = POLLIN;
    waited[index].revents = 0;
  }
  poll(waited, (nfds_t)count, -1);
  free(waited);
}

struct truss_branch {
  void (*run)(void *environment);
  void *environment;
};

struct truss_worker;

struct truss_job {
  void (*run)(void *environment);
  void *environment;
  _Atomic(struct truss_worker *) thief;
  atomic_int done;
};

#define TRUSS_QUEUE 256
#define TRUSS_MAXIMUM_WORKERS 256
#define TRUSS_MAXIMUM_SPARES 256
#define TRUSS_GRAINS_PER_WORKER 8

struct truss_worker {
  _Alignas(64) _Atomic(int64_t) top;
  _Alignas(64) _Atomic(int64_t) bottom;
  uint64_t random;
  _Alignas(64) _Atomic(struct truss_job *) jobs[TRUSS_QUEUE];
  _Alignas(64) atomic_size_t joiners;
  pthread_mutex_t join_lock;
  pthread_cond_t join_wake;
};

static struct truss_worker truss_workers[TRUSS_MAXIMUM_WORKERS + TRUSS_MAXIMUM_SPARES];
static atomic_size_t truss_worker_count;
static _Thread_local struct truss_worker *truss_self;

__attribute__((noinline)) static struct truss_worker *truss_worker_self(void) {
  __asm__ __volatile__("");
  return truss_self;
}
static uint32_t truss_requested_workers;
static size_t truss_pool_workers = 1;
static pthread_once_t truss_pool_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t truss_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t truss_pool_wake = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t truss_spare_lock = PTHREAD_MUTEX_INITIALIZER;
static atomic_size_t truss_idle_runners;

static atomic_size_t truss_run_count;
struct truss_task;
static struct truss_task *truss_run_pop(void);
static void truss_task_run(struct truss_task *task);
static atomic_int truss_blocked;
static void truss_spare_ensure(void);

static int truss_offer(struct truss_worker *worker, struct truss_job *job) {
  int64_t bottom = atomic_load_explicit(&worker->bottom, memory_order_relaxed);
  int64_t top = atomic_load_explicit(&worker->top, memory_order_acquire);
  if (bottom - top >= TRUSS_QUEUE) return 0;
  atomic_store_explicit(&worker->jobs[bottom % TRUSS_QUEUE], job, memory_order_relaxed);
  atomic_store(&worker->bottom, bottom + 1);
  return 1;
}

static struct truss_job *truss_take_back(struct truss_worker *worker) {
  int64_t bottom = atomic_load_explicit(&worker->bottom, memory_order_relaxed) - 1;
  atomic_store_explicit(&worker->bottom, bottom, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  int64_t top = atomic_load_explicit(&worker->top, memory_order_relaxed);
  struct truss_job *job = NULL;
  if (top <= bottom) {
    job = atomic_load_explicit(&worker->jobs[bottom % TRUSS_QUEUE], memory_order_relaxed);
    if (top == bottom) {
      if (!atomic_compare_exchange_strong_explicit(&worker->top, &top, top + 1, memory_order_seq_cst,
                                                   memory_order_relaxed))
        job = NULL;
      atomic_store_explicit(&worker->bottom, bottom + 1, memory_order_relaxed);
    }
  } else {
    atomic_store_explicit(&worker->bottom, bottom + 1, memory_order_relaxed);
  }
  return job;
}

static struct truss_job *truss_steal(struct truss_worker *victim) {
  int64_t top = atomic_load_explicit(&victim->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  int64_t bottom = atomic_load_explicit(&victim->bottom, memory_order_acquire);
  if (top >= bottom) return NULL;
  struct truss_job *job = atomic_load_explicit(&victim->jobs[top % TRUSS_QUEUE], memory_order_relaxed);
  if (!atomic_compare_exchange_strong_explicit(&victim->top, &top, top + 1, memory_order_seq_cst,
                                               memory_order_relaxed))
    return NULL;
  return job;
}

static struct truss_job *truss_find(struct truss_worker *self) {
  size_t count = atomic_load(&truss_worker_count);
  self->random = self->random * 6364136223846793005ULL + 1442695040888963407ULL;
  size_t start = (size_t)(self->random >> 33) % count;
  for (size_t offset = 0; offset < count; offset++) {
    struct truss_worker *victim = &truss_workers[(start + offset) % count];
    if (victim == self) continue;
    struct truss_job *job = truss_steal(victim);
    if (job != NULL) return job;
  }
  return NULL;
}

static int truss_has_job(struct truss_worker *worker) {
  return atomic_load(&worker->top) < atomic_load(&worker->bottom);
}

static int truss_any_job(void) {
  size_t count = atomic_load(&truss_worker_count);
  for (size_t index = 0; index < count; index++)
    if (truss_has_job(&truss_workers[index])) return 1;
  return 0;
}

static void truss_wake(int everyone) {
  if (atomic_load(&truss_idle_runners) == 0) return;
  pthread_mutex_lock(&truss_pool_lock);
  if (everyone) pthread_cond_broadcast(&truss_pool_wake);
  else pthread_cond_signal(&truss_pool_wake);
  pthread_mutex_unlock(&truss_pool_lock);
}

static void truss_wake_joiners(struct truss_worker *worker) {
  if (atomic_load(&worker->joiners) == 0) return;
  pthread_mutex_lock(&worker->join_lock);
  pthread_cond_broadcast(&worker->join_wake);
  pthread_mutex_unlock(&worker->join_lock);
}

static void truss_run_stolen(struct truss_worker *self, struct truss_job *job) {
  atomic_store_explicit(&job->thief, self, memory_order_release);
  job->run(job->environment);
  atomic_store(&job->done, 1);
  truss_wake_joiners(self);
}

static void truss_rest(unsigned idle) {
  if (idle < 32) {
#if defined(__x86_64__)
    __builtin_ia32_pause();
#elif defined(__aarch64__)
    __asm__ __volatile__("yield");
#endif
  } else {
    sched_yield();
  }
}

static void truss_sleep(atomic_int *done) {
  pthread_mutex_lock(&truss_pool_lock);
  atomic_fetch_add(&truss_idle_runners, 1);
  if (!(done != NULL && atomic_load(done)) && !truss_any_job() && atomic_load(&truss_run_count) == 0)
    pthread_cond_wait(&truss_pool_wake, &truss_pool_lock);
  atomic_fetch_sub(&truss_idle_runners, 1);
  pthread_mutex_unlock(&truss_pool_lock);
}

static pthread_once_t truss_join_locks_once = PTHREAD_ONCE_INIT;

static void truss_join_locks_start(void) {
  for (size_t index = 0; index < TRUSS_MAXIMUM_WORKERS + TRUSS_MAXIMUM_SPARES; index++) {
    pthread_mutex_init(&truss_workers[index].join_lock, NULL);
    pthread_cond_init(&truss_workers[index].join_wake, NULL);
  }
}

static void truss_sleep_on_thief(struct truss_worker *thief, atomic_int *done) {
  pthread_once(&truss_join_locks_once, truss_join_locks_start);
  atomic_fetch_add(&truss_blocked, 1);
  truss_spare_ensure();
  pthread_mutex_lock(&thief->join_lock);
  atomic_fetch_add(&thief->joiners, 1);
  if (!atomic_load(done) && !truss_has_job(thief)) pthread_cond_wait(&thief->join_wake, &thief->join_lock);
  atomic_fetch_sub(&thief->joiners, 1);
  pthread_mutex_unlock(&thief->join_lock);
  atomic_fetch_sub(&truss_blocked, 1);
}

static void truss_join(struct truss_worker *self, struct truss_job *job) {
  unsigned idle = 0;
  while (!atomic_load_explicit(&job->done, memory_order_acquire)) {
    struct truss_worker *thief = atomic_load_explicit(&job->thief, memory_order_acquire);
    struct truss_job *descendant = thief == NULL ? NULL : truss_steal(thief);
    if (descendant != NULL) {
      truss_run_stolen(self, descendant);
      idle = 0;
    } else if (++idle < 40 || thief == NULL) {
      truss_rest(idle);
    } else {
      truss_sleep_on_thief(thief, &job->done);
      idle = 0;
    }
  }
}

static void truss_runner_signals(void) {
  sigset_t all;
  sigfillset(&all);
  sigdelset(&all, SIGSEGV);
  sigdelset(&all, SIGBUS);
  sigdelset(&all, SIGFPE);
  sigdelset(&all, SIGILL);
  sigdelset(&all, SIGURG);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
}

static void truss_run_until(struct truss_worker *self, atomic_int *done) {
  unsigned idle = 0;
  while (done == NULL || !atomic_load(done)) {
    struct truss_task *task = truss_run_pop();
    struct truss_job *job = task == NULL ? truss_find(self) : NULL;
    if (task != NULL) {
      truss_task_run(task);
      idle = 0;
    } else if (job != NULL) {
      truss_run_stolen(self, job);
      idle = 0;
    } else if (++idle < 40) {
      truss_rest(idle);
    } else {
      truss_sleep(done);
      idle = 0;
    }
  }
}

static void *truss_worker_main(void *argument) {
  struct truss_worker *self = argument;
  truss_self = self;
  truss_runner_signals();
  truss_thread_signal_stack_install();
  truss_run_until(self, NULL);
  return NULL;
}

static long truss_count_processors(void) {
#ifdef __linux__
  cpu_set_t allowed;
  if (sched_getaffinity(0, sizeof allowed, &allowed) == 0) return CPU_COUNT(&allowed);
#endif
  return sysconf(_SC_NPROCESSORS_ONLN);
}

static void truss_pool_start(void) {
  long count = truss_requested_workers;
  if (count == 0) {
    count = truss_count_processors();
    const char *requested = getenv("TRUSS_WORKERS");
    if (requested != NULL && requested[0] != 0) count = strtol(requested, NULL, 10);
  }
  if (count > TRUSS_MAXIMUM_WORKERS) count = TRUSS_MAXIMUM_WORKERS;
  pthread_attr_t attributes;
  truss_thread_attributes(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  pthread_mutex_lock(&truss_spare_lock);
  while ((long)truss_pool_workers < count) {
    size_t index = atomic_load(&truss_worker_count);
    truss_workers[index].random = (uint64_t)index + 1;
    pthread_t thread;
    if (pthread_create(&thread, &attributes, truss_worker_main, &truss_workers[index]) != 0) break;
    atomic_store(&truss_worker_count, index + 1);
    truss_pool_workers += 1;
  }
  pthread_mutex_unlock(&truss_spare_lock);
  pthread_attr_destroy(&attributes);
}

static void truss_fork(struct truss_worker *self, struct truss_branch first, struct truss_branch second) {
  struct truss_job job;
  job.run = second.run;
  job.environment = second.environment;
  atomic_init(&job.thief, NULL);
  atomic_init(&job.done, 0);
  if (!truss_offer(self, &job)) {
    first.run(first.environment);
    second.run(second.environment);
    return;
  }
  truss_wake(0);
  truss_wake_joiners(self);
  first.run(first.environment);
  struct truss_job *back = truss_take_back(self);
  if (back == &job) second.run(second.environment);
  else if (back == NULL) truss_join(self, &job);
  else truss_runtime_compiler_bug();
}

struct truss_branches {
  const struct truss_branch *branches;
  uint64_t count;
};

static void truss_branches_run(void *argument) {
  const struct truss_branches *all = argument;
  if (all->count == 1) {
    all->branches[0].run(all->branches[0].environment);
    return;
  }
  struct truss_branches low = {all->branches, all->count / 2};
  struct truss_branches high = {all->branches + low.count, all->count - low.count};
  truss_fork(truss_worker_self(), (struct truss_branch){truss_branches_run, &low},
             (struct truss_branch){truss_branches_run, &high});
}

void truss_runtime_parallel(const struct truss_branch *branches, uint64_t count) {
  if (count == 0) truss_runtime_compiler_bug();
  pthread_once(&truss_pool_once, truss_pool_start);
  if (truss_pool_workers == 1) {
    for (uint64_t index = 0; index < count; index++) branches[index].run(branches[index].environment);
    return;
  }
  struct truss_branches all = {branches, count};
  truss_branches_run(&all);
}

struct truss_range {
  void (*body)(void *environment, uint64_t first, uint64_t last);
  void *environment;
  uint64_t first;
  uint64_t last;
  uint64_t grain;
};

static void truss_range_run(void *argument) {
  struct truss_range range = *(const struct truss_range *)argument;
  struct truss_worker *self = truss_worker_self();
  for (;;) {
    if (range.last - range.first >= range.grain && !truss_has_job(self)) {
      struct truss_range low = range;
      struct truss_range high = range;
      low.last = range.first + (range.last - range.first) / 2;
      high.first = low.last + 1;
      truss_fork(self, (struct truss_branch){truss_range_run, &low},
                 (struct truss_branch){truss_range_run, &high});
      return;
    }
    uint64_t last = range.last - range.first < range.grain ? range.last : range.first + range.grain - 1;
    range.body(range.environment, range.first, last);
    if (last == range.last) return;
    range.first = last + 1;
  }
}

void truss_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t last),
                              void *environment, uint64_t first, uint64_t last) {
  if (first > last) truss_runtime_compiler_bug();
  pthread_once(&truss_pool_once, truss_pool_start);
  if (truss_pool_workers == 1) {
    body(environment, first, last);
    return;
  }
  struct truss_range whole = {body, environment, first, last,
                              (last - first) / (TRUSS_GRAINS_PER_WORKER * truss_pool_workers) + 1};
  truss_range_run(&whole);
}

struct truss_wait_slot;

struct truss_task {
  struct truss_context context;
  void *stack;
  struct truss_group *group;
  void (*code)(void *environment, uint64_t item, void *capabilities);
  void *environment;
  uint64_t item;
  struct truss_task *next;
  uint64_t wait_key;
  _Atomic(struct truss_wait_slot *) cancellable;
  struct truss_task *sibling;
  _Atomic(pthread_t) thread;
  atomic_int blocking;
  atomic_int state;
  int finished;
  struct truss_coroutine *coroutine;
#ifdef TRUSS_ADDRESS_SANITIZER
  const void *suspended_stack;
  size_t suspended_stack_size;
  const void *thread_stack;
  size_t thread_stack_size;
#endif
#ifdef TRUSS_THREAD_SANITIZER
  void *fiber;
  void *suspended_fiber;
  void *thread_fiber;
#endif
};

struct truss_group {
  pthread_mutex_t lock;
  size_t running;
  atomic_int cancelled;
  struct truss_group *parent;
  struct truss_task *tasks;
  struct truss_group *children;
  struct truss_group *next;
  struct truss_task *joiner;
  struct truss_group *interrupted;
};

enum { TRUSS_TASK_RUNNING, TRUSS_TASK_PARKING, TRUSS_TASK_PARKED };

static _Thread_local struct truss_task *truss_task_running;
static _Thread_local struct truss_context truss_thread_context;

__attribute__((noinline)) static struct truss_task *truss_task_self(void) {
  __asm__ __volatile__("");
  return truss_task_running;
}

__attribute__((noinline)) static struct truss_context *truss_thread_context_self(void) {
  __asm__ __volatile__("");
  return &truss_thread_context;
}

static pthread_mutex_t truss_run_lock = PTHREAD_MUTEX_INITIALIZER;
static struct truss_task *truss_run_first;
static struct truss_task *truss_run_last;

static void truss_run_push(struct truss_task *task) {
  task->next = NULL;
  pthread_mutex_lock(&truss_run_lock);
  if (truss_run_last != NULL) truss_run_last->next = task;
  else truss_run_first = task;
  truss_run_last = task;
  atomic_fetch_add(&truss_run_count, 1);
  pthread_mutex_unlock(&truss_run_lock);
  truss_wake(1);
  truss_spare_ensure();
}

static struct truss_task *truss_run_pop(void) {
  if (atomic_load(&truss_run_count) == 0) return NULL;
  size_t left = 0;
  pthread_mutex_lock(&truss_run_lock);
  struct truss_task *task = truss_run_first;
  if (task != NULL) {
    truss_run_first = task->next;
    if (truss_run_first == NULL) truss_run_last = NULL;
    left = atomic_fetch_sub(&truss_run_count, 1) - 1;
  }
  pthread_mutex_unlock(&truss_run_lock);
  if (left > 0) truss_spare_ensure();
  return task;
}

static void truss_task_run(struct truss_task *task) {
  truss_task_running = task;
  truss_coroutine_self = task->coroutine;
  atomic_store(&task->thread, pthread_self());
#ifdef TRUSS_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(&fake, task->suspended_stack, task->suspended_stack_size);
#endif
#ifdef TRUSS_THREAD_SANITIZER
  task->thread_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(task->suspended_fiber, 0);
#endif
  truss_context_switch(&truss_thread_context, &task->context);
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &task->suspended_stack, &task->suspended_stack_size);
#endif
  truss_task_running = NULL;
  task->coroutine = truss_coroutine_self;
  truss_coroutine_self = NULL;
  if (task->finished) {
#ifdef TRUSS_THREAD_SANITIZER
    __tsan_destroy_fiber(task->fiber);
#endif
    truss_stack_release(task->stack);
    free(task);
    return;
  }
  int state = TRUSS_TASK_PARKING;
  if (!atomic_compare_exchange_strong(&task->state, &state, TRUSS_TASK_PARKED)) truss_run_push(task);
}

static void truss_task_switch(struct truss_task *task) {
#ifdef TRUSS_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(task->finished ? NULL : &fake, task->thread_stack,
                                 task->thread_stack_size);
#endif
#ifdef TRUSS_THREAD_SANITIZER
  task->suspended_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(task->thread_fiber, 0);
#endif
  truss_context_switch(&task->context, truss_thread_context_self());
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &task->thread_stack, &task->thread_stack_size);
#endif
}

static void truss_task_park(struct truss_task *task, pthread_mutex_t *lock) {
  atomic_store(&task->state, TRUSS_TASK_PARKING);
  pthread_mutex_unlock(lock);
  truss_task_switch(task);
}

static void truss_task_ready(struct truss_task *task) {
  int state = TRUSS_TASK_PARKING;
  if (atomic_compare_exchange_strong(&task->state, &state, TRUSS_TASK_RUNNING)) return;
  atomic_store(&task->state, TRUSS_TASK_RUNNING);
  truss_run_push(task);
}

static pthread_cond_t truss_spare_wake = PTHREAD_COND_INITIALIZER;
static int truss_spares;
static int truss_spares_idle;
static int truss_spares_busy;
static int truss_spares_called;

static void *truss_spare_main(void *argument) {
  truss_self = argument;
  truss_runner_signals();
  truss_thread_signal_stack_install();
  for (;;) {
    struct truss_task *task = truss_run_pop();
    if (task != NULL) truss_task_run(task);
    pthread_mutex_lock(&truss_spare_lock);
    if (truss_spares_busy > atomic_load(&truss_blocked) || atomic_load(&truss_run_count) == 0) {
      truss_spares_busy -= 1;
      truss_spares_idle += 1;
      while (truss_spares_called == 0) pthread_cond_wait(&truss_spare_wake, &truss_spare_lock);
      truss_spares_called -= 1;
    }
    pthread_mutex_unlock(&truss_spare_lock);
  }
  return NULL;
}

static atomic_int truss_monitor_asleep = 1;
static void truss_monitor_rouse(void);

static void truss_spare_ensure(void) {
  if (atomic_load(&truss_run_count) == 0) return;
  if (atomic_load(&truss_monitor_asleep)) truss_monitor_rouse();
  if (atomic_load(&truss_blocked) == 0 || atomic_load(&truss_idle_runners) > 0) return;
  pthread_mutex_lock(&truss_spare_lock);
  if (truss_spares_busy < atomic_load(&truss_blocked)) {
    if (truss_spares_idle > 0) {
      truss_spares_idle -= 1;
      truss_spares_busy += 1;
      truss_spares_called += 1;
      pthread_cond_signal(&truss_spare_wake);
    } else if (truss_spares < TRUSS_MAXIMUM_SPARES) {
      size_t index = atomic_load(&truss_worker_count);
      pthread_t thread;
      pthread_attr_t attributes;
      truss_thread_attributes(&attributes);
      pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
      if (pthread_create(&thread, &attributes, truss_spare_main, &truss_workers[index]) == 0) {
        atomic_store(&truss_worker_count, index + 1);
        truss_spares += 1;
        truss_spares_busy += 1;
      } else if (index == 1) {
        truss_out_of_memory();
      }
      pthread_attr_destroy(&attributes);
    }
  }
  pthread_mutex_unlock(&truss_spare_lock);
}

#define TRUSS_COUNTED UINT_FAST64_MAX

struct truss_caller {
  atomic_uint_fast64_t since;
  struct truss_caller *next;
};

static _Thread_local struct truss_caller truss_thread_caller;
static _Thread_local int truss_caller_listed;
static pthread_mutex_t truss_monitor_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t truss_monitor_wake = PTHREAD_COND_INITIALIZER;
static pthread_once_t truss_monitor_once = PTHREAD_ONCE_INIT;
static struct truss_caller *truss_callers;
static atomic_uint_fast64_t truss_tick = 1;

__attribute__((noinline)) static struct truss_caller *truss_caller_self(void) {
  __asm__ __volatile__("");
  if (!truss_caller_listed) {
    truss_caller_listed = 1;
    pthread_mutex_lock(&truss_monitor_lock);
    truss_thread_caller.next = truss_callers;
    truss_callers = &truss_thread_caller;
    pthread_mutex_unlock(&truss_monitor_lock);
  }
  return &truss_thread_caller;
}

static void *truss_monitor_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  pthread_mutex_lock(&truss_monitor_lock);
  for (;;) {
    if (atomic_load(&truss_run_count) == 0) {
      atomic_store(&truss_monitor_asleep, 1);
      if (atomic_load(&truss_run_count) == 0) pthread_cond_wait(&truss_monitor_wake, &truss_monitor_lock);
      continue;
    }
    atomic_store(&truss_monitor_asleep, 0);
    uint_fast64_t tick = atomic_fetch_add(&truss_tick, 1) + 1;
    int counted = 0;
    for (struct truss_caller *caller = truss_callers; caller != NULL; caller = caller->next) {
      uint_fast64_t since = atomic_load(&caller->since);
      if (since == 0 || since == TRUSS_COUNTED || tick - since < 2) continue;
      if (atomic_compare_exchange_strong(&caller->since, &since, TRUSS_COUNTED)) {
        atomic_fetch_add(&truss_blocked, 1);
        counted = 1;
      }
    }
    pthread_mutex_unlock(&truss_monitor_lock);
    if (counted) truss_spare_ensure();
    struct timespec tick_length = {0, 1000000};
    nanosleep(&tick_length, NULL);
    pthread_mutex_lock(&truss_monitor_lock);
  }
  return NULL;
}

static void truss_monitor_start(void) {
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, truss_monitor_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) truss_out_of_memory();
}

static void truss_monitor_rouse(void) {
  pthread_once(&truss_monitor_once, truss_monitor_start);
  pthread_mutex_lock(&truss_monitor_lock);
  pthread_cond_signal(&truss_monitor_wake);
  pthread_mutex_unlock(&truss_monitor_lock);
}

void truss_runtime_blocking_begin(void) {
  struct truss_task *task = truss_task_self();
  atomic_store(&task->thread, pthread_self());
  atomic_store(&task->blocking, 1);
  atomic_store(&truss_caller_self()->since, atomic_load(&truss_tick));
  truss_spare_ensure();
}

void truss_runtime_blocking_end(void) {
  if (atomic_exchange(&truss_caller_self()->since, 0) == TRUSS_COUNTED) atomic_fetch_sub(&truss_blocked, 1);
  atomic_store(&truss_task_self()->blocking, 0);
}

static void truss_interrupt_handler(int signal) { (void)signal; }

static pthread_mutex_t truss_interrupter_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t truss_interrupter_wake = PTHREAD_COND_INITIALIZER;
static struct truss_group *truss_interrupter_groups;
static pthread_once_t truss_interrupt_once = PTHREAD_ONCE_INIT;

static void truss_group_interrupt(struct truss_group *group) {
  for (struct truss_task *task = group->tasks; task != NULL; task = task->sibling)
    if (atomic_load(&task->blocking)) pthread_kill(atomic_load(&task->thread), SIGURG);
  for (struct truss_group *child = group->children; child != NULL; child = child->next) {
    pthread_mutex_lock(&child->lock);
    truss_group_interrupt(child);
    pthread_mutex_unlock(&child->lock);
  }
}

static void *truss_interrupter_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  for (;;) {
    pthread_mutex_lock(&truss_interrupter_lock);
    while (truss_interrupter_groups == NULL)
      pthread_cond_wait(&truss_interrupter_wake, &truss_interrupter_lock);
    for (struct truss_group *group = truss_interrupter_groups; group != NULL; group = group->interrupted) {
      pthread_mutex_lock(&group->lock);
      truss_group_interrupt(group);
      pthread_mutex_unlock(&group->lock);
    }
    pthread_mutex_unlock(&truss_interrupter_lock);
    struct timespec pause = {0, 5000000};
    nanosleep(&pause, NULL);
  }
  return NULL;
}

static void truss_interrupt_start(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = truss_interrupt_handler;
  sigemptyset(&action.sa_mask);
  sigaction(SIGURG, &action, NULL);
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, truss_interrupter_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) truss_out_of_memory();
}

#define TRUSS_WAIT_SLOTS 1024

struct truss_wait_slot {
  pthread_mutex_t lock;
  atomic_uint_fast64_t wakes;
  struct truss_task *parked;
};

static struct truss_wait_slot truss_wait_slots[TRUSS_WAIT_SLOTS];
static pthread_once_t truss_wait_slots_once = PTHREAD_ONCE_INIT;

static void truss_wait_slots_start(void) {
  for (int index = 0; index < TRUSS_WAIT_SLOTS; index++) pthread_mutex_init(&truss_wait_slots[index].lock, NULL);
}

static struct truss_wait_slot *truss_wait_slot(uint64_t key) {
  pthread_once(&truss_wait_slots_once, truss_wait_slots_start);
  return &truss_wait_slots[(key * 0x9E3779B97F4A7C15ULL) >> 54];
}

int32_t truss_runtime_tasks_cancelled(void) {
  for (struct truss_group *group = truss_task_self()->group; group != NULL; group = group->parent)
    if (atomic_load(&group->cancelled)) return 1;
  return 0;
}

uint64_t truss_runtime_tasks_watch(uint64_t key) { return atomic_load(&truss_wait_slot(key)->wakes); }

static void truss_wait(uint64_t key, uint64_t ticket, int cancellable) {
  struct truss_wait_slot *slot = truss_wait_slot(key);
  struct truss_task *task = truss_task_self();
  pthread_mutex_lock(&slot->lock);
  if (cancellable) atomic_store(&task->cancellable, slot);
  if (atomic_load(&slot->wakes) != ticket || (cancellable && truss_runtime_tasks_cancelled())) {
    pthread_mutex_unlock(&slot->lock);
  } else {
    task->wait_key = key;
    task->next = slot->parked;
    slot->parked = task;
    truss_task_park(task, &slot->lock);
  }
  if (cancellable) atomic_store(&task->cancellable, NULL);
}

int32_t truss_runtime_tasks_wait(uint64_t key, uint64_t ticket) {
  truss_wait(key, ticket, 1);
  return 0;
}

int32_t truss_runtime_tasks_wake(uint64_t key) {
  struct truss_wait_slot *slot = truss_wait_slot(key);
  struct truss_task *tasks = NULL;
  pthread_mutex_lock(&slot->lock);
  atomic_fetch_add(&slot->wakes, 1);
  for (struct truss_task **link = &slot->parked; *link != NULL;) {
    struct truss_task *task = *link;
    if (task->wait_key != key) {
      link = &task->next;
      continue;
    }
    *link = task->next;
    task->next = tasks;
    tasks = task;
  }
  pthread_mutex_unlock(&slot->lock);
  while (tasks != NULL) {
    struct truss_task *task = tasks;
    tasks = task->next;
    truss_task_ready(task);
  }
  return 0;
}

static void truss_group_wake(struct truss_group *group) {
  for (struct truss_task *task = group->tasks; task != NULL; task = task->sibling) {
    struct truss_wait_slot *slot = atomic_load(&task->cancellable);
    if (slot == NULL) continue;
    pthread_mutex_lock(&slot->lock);
    struct truss_task **link = &slot->parked;
    while (*link != NULL && *link != task) link = &(*link)->next;
    int parked = *link == task;
    if (parked) *link = task->next;
    pthread_mutex_unlock(&slot->lock);
    if (parked) truss_task_ready(task);
  }
  for (struct truss_group *child = group->children; child != NULL; child = child->next) {
    pthread_mutex_lock(&child->lock);
    truss_group_wake(child);
    pthread_mutex_unlock(&child->lock);
  }
}

struct truss_timer {
  uint64_t deadline;
  uint64_t key;
  size_t index;
  int fired;
};

static pthread_mutex_t truss_timer_lock = PTHREAD_MUTEX_INITIALIZER;
static struct truss_timer **truss_timers;
static size_t truss_timer_count;
static size_t truss_timer_room;

#define TRUSS_TIMERS_EVENT 1
#define TRUSS_SIGNALS_EVENT 2

static int truss_poller = -1;
static pthread_once_t truss_poller_once = PTHREAD_ONCE_INIT;
static void truss_poller_start(void);
static void truss_signals_arrived(void);

#ifdef __linux__
static int truss_timer_descriptor = -1;
#endif

static uint64_t truss_monotonic(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000000u + (uint64_t)now.tv_nsec;
}

static void truss_timer_place(struct truss_timer *timer, size_t index) {
  truss_timers[index] = timer;
  timer->index = index;
}

static void truss_timer_settle(size_t index) {
  struct truss_timer *timer = truss_timers[index];
  while (index > 0) {
    size_t parent = (index - 1) / 2;
    if (truss_timers[parent]->deadline <= timer->deadline) break;
    truss_timer_place(truss_timers[parent], index);
    index = parent;
  }
  for (;;) {
    size_t child = 2 * index + 1;
    if (child >= truss_timer_count) break;
    if (child + 1 < truss_timer_count && truss_timers[child + 1]->deadline < truss_timers[child]->deadline)
      child += 1;
    if (timer->deadline <= truss_timers[child]->deadline) break;
    truss_timer_place(truss_timers[child], index);
    index = child;
  }
  truss_timer_place(timer, index);
}

static void truss_timer_remove(struct truss_timer *timer) {
  size_t index = timer->index;
  truss_timer_count -= 1;
  if (index == truss_timer_count) return;
  truss_timer_place(truss_timers[truss_timer_count], index);
  truss_timer_settle(index);
}

static void truss_timer_arm(void) {
  uint64_t deadline = truss_timers[0]->deadline;
#ifdef __linux__
  struct itimerspec setting;
  memset(&setting, 0, sizeof setting);
  setting.it_value.tv_sec = (time_t)(deadline / 1000000000u);
  setting.it_value.tv_nsec = (long)(deadline % 1000000000u);
  timerfd_settime(truss_timer_descriptor, TFD_TIMER_ABSTIME, &setting, NULL);
#else
  uint64_t now = truss_monotonic();
  struct kevent change;
  EV_SET(&change, TRUSS_TIMERS_EVENT, EVFILT_TIMER, EV_ADD | EV_ONESHOT, NOTE_NSECONDS,
         deadline > now ? (intptr_t)(deadline - now) : 1, NULL);
  kevent(truss_poller, &change, 1, NULL, 0, NULL);
#endif
}

static void truss_timers_fire(void) {
  uint64_t now = truss_monotonic();
  pthread_mutex_lock(&truss_timer_lock);
  while (truss_timer_count > 0 && truss_timers[0]->deadline <= now) {
    struct truss_timer *first = truss_timers[0];
    truss_timer_remove(first);
    first->fired = 1;
    uint64_t key = first->key;
    pthread_mutex_unlock(&truss_timer_lock);
    truss_runtime_tasks_wake(key);
    pthread_mutex_lock(&truss_timer_lock);
  }
  if (truss_timer_count > 0) truss_timer_arm();
  pthread_mutex_unlock(&truss_timer_lock);
}

static void truss_timer_begin(struct truss_timer *timer, uint64_t nanoseconds, uint64_t key) {
  pthread_once(&truss_poller_once, truss_poller_start);
  uint64_t now = truss_monotonic();
  uint64_t latest = (uint64_t)INT64_MAX;
  timer->deadline = nanoseconds > latest - now ? latest : now + nanoseconds;
  timer->key = key;
  timer->fired = 0;
  pthread_mutex_lock(&truss_timer_lock);
  if (truss_timer_count == truss_timer_room) {
    truss_timer_room = truss_timer_room == 0 ? 64 : truss_timer_room * 2;
    truss_timers = realloc(truss_timers, truss_timer_room * sizeof *truss_timers);
    if (truss_timers == NULL) truss_out_of_memory();
  }
  truss_timer_count += 1;
  truss_timer_place(timer, truss_timer_count - 1);
  truss_timer_settle(truss_timer_count - 1);
  if (timer->index == 0) truss_timer_arm();
  pthread_mutex_unlock(&truss_timer_lock);
}

static int truss_timer_fired(struct truss_timer *timer) {
  pthread_mutex_lock(&truss_timer_lock);
  int fired = timer->fired;
  pthread_mutex_unlock(&truss_timer_lock);
  return fired;
}

static int truss_timer_end(struct truss_timer *timer) {
  pthread_mutex_lock(&truss_timer_lock);
  int fired = timer->fired;
  if (!fired) truss_timer_remove(timer);
  pthread_mutex_unlock(&truss_timer_lock);
  return fired;
}

int32_t truss_runtime_sleep(int64_t seconds, int64_t nanoseconds) {
  uint64_t duration = seconds <= 0 ? 0 : (uint64_t)seconds;
  duration = duration > UINT64_MAX / 1000000000u ? UINT64_MAX : duration * 1000000000u;
  uint64_t rest = nanoseconds <= 0 ? 0 : (uint64_t)nanoseconds;
  duration = duration > UINT64_MAX - rest ? UINT64_MAX : duration + rest;
  if (duration == 0) return 0;
  struct truss_timer timer;
  uint64_t key = (uint64_t)(uintptr_t)&timer;
  truss_timer_begin(&timer, duration, key);
  for (;;) {
    uint64_t ticket = truss_runtime_tasks_watch(key);
    if (truss_timer_fired(&timer)) return 0;
    if (truss_runtime_tasks_cancelled()) return !truss_timer_end(&timer);
    truss_wait(key, ticket, 1);
  }
}

#define TRUSS_DESCRIPTORS 65536

#define TRUSS_OWN_KEY 1
#define TRUSS_CALLERS_KEY 2

static atomic_uchar truss_descriptor_registered[TRUSS_DESCRIPTORS];

static uint64_t truss_descriptor_key(int32_t descriptor, int32_t writing) {
  return (uint64_t)1 << 63 | (uint64_t)(uint32_t)descriptor << 1 | (uint64_t)(writing != 0);
}

static void *truss_poller_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  for (;;) {
#ifdef __linux__
    struct epoll_event events[64];
    int count = epoll_wait(truss_poller, events, 64, -1);
    for (int index = 0; index < count; index++) {
      uint64_t key = events[index].data.u64;
      uint32_t ready = events[index].events;
      if (key == TRUSS_TIMERS_EVENT) {
        uint64_t expirations;
        ssize_t received = read(truss_timer_descriptor, &expirations, sizeof expirations);
        (void)received;
        truss_timers_fire();
      } else if (key == TRUSS_SIGNALS_EVENT) {
        truss_signals_arrived();
      } else {
        if (ready & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) truss_runtime_tasks_wake(key);
        if ((key >> 63) && (ready & (EPOLLOUT | EPOLLHUP | EPOLLERR))) truss_runtime_tasks_wake(key | 1);
      }
    }
#else
    struct kevent events[64];
    int count = kevent(truss_poller, NULL, 0, events, 64, NULL);
    for (int index = 0; index < count; index++) {
      uint64_t key = (uint64_t)(uintptr_t)events[index].udata;
      int writing = events[index].filter == EVFILT_WRITE;
      if (events[index].filter == EVFILT_TIMER)
        truss_timers_fire();
      else if (key == TRUSS_SIGNALS_EVENT)
        truss_signals_arrived();
      else if (key == 0)
        truss_runtime_tasks_wake(truss_descriptor_key((int32_t)events[index].ident, writing));
      else if (!writing)
        truss_runtime_tasks_wake(key);
    }
#endif
  }
  return NULL;
}

static void truss_poller_start(void) {
#ifdef __linux__
  truss_poller = epoll_create1(EPOLL_CLOEXEC);
  if (truss_poller < 0) truss_out_of_memory();
  truss_timer_descriptor = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC | TFD_NONBLOCK);
  if (truss_timer_descriptor < 0) truss_out_of_memory();
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN;
  event.data.u64 = TRUSS_TIMERS_EVENT;
  if (epoll_ctl(truss_poller, EPOLL_CTL_ADD, truss_timer_descriptor, &event) != 0) truss_out_of_memory();
#else
  truss_poller = kqueue();
  if (truss_poller < 0) truss_out_of_memory();
  fcntl(truss_poller, F_SETFD, FD_CLOEXEC);
#endif
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, truss_poller_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) truss_out_of_memory();
}

static int truss_descriptor_register(int32_t descriptor, uint64_t key) {
  int known = descriptor >= 0 && descriptor < TRUSS_DESCRIPTORS;
  if (key == 0 && known && atomic_load(&truss_descriptor_registered[descriptor]) == TRUSS_OWN_KEY) return 1;
  pthread_once(&truss_poller_once, truss_poller_start);
#ifdef __linux__
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN | EPOLLOUT | EPOLLRDHUP | EPOLLET;
  event.data.u64 = key == 0 ? truss_descriptor_key(descriptor, 0) : key;
  if (epoll_ctl(truss_poller, EPOLL_CTL_ADD, descriptor, &event) != 0
      && (*truss_runtime_errno_address_uncached() != EEXIST || epoll_ctl(truss_poller, EPOLL_CTL_MOD, descriptor, &event) != 0))
    return 0;
#else
  struct kevent changes[2];
  void *reported = (void *)(uintptr_t)key;
  EV_SET(&changes[0], descriptor, EVFILT_READ, EV_ADD | EV_CLEAR, 0, 0, reported);
  EV_SET(&changes[1], descriptor, EVFILT_WRITE, EV_ADD | EV_CLEAR, 0, 0, reported);
  if (kevent(truss_poller, changes, 2, NULL, 0, NULL) != 0) return 0;
#endif
  if (known) atomic_store(&truss_descriptor_registered[descriptor], key == 0 ? TRUSS_OWN_KEY : TRUSS_CALLERS_KEY);
  return 1;
}

uint64_t truss_runtime_descriptor_watch(int32_t descriptor, int32_t writing) {
  return truss_runtime_tasks_watch(truss_descriptor_key(descriptor, writing));
}

int32_t truss_runtime_descriptor_wait(int32_t descriptor, int32_t writing, uint64_t ticket) {
  int32_t ready = 1;
  if (!truss_descriptor_register(descriptor, 0)) {
    truss_runtime_blocking_begin();
    ready = truss_descriptor_poll(descriptor, writing);
    truss_runtime_blocking_end();
  } else {
    uint64_t key = truss_descriptor_key(descriptor, writing);
    uint64_t limit = truss_descriptor_limit(descriptor, writing);
    if (limit == 0) {
      truss_wait(key, ticket, 1);
    } else {
      struct truss_timer timer;
      truss_timer_begin(&timer, limit, key);
      truss_wait(key, ticket, 1);
      ready = !truss_timer_end(&timer);
    }
  }
  if (truss_runtime_tasks_cancelled()) {
    *truss_runtime_errno_address_uncached() = EINTR;
    return 0;
  }
  if (!ready) *truss_runtime_errno_address_uncached() = EAGAIN;
  return ready;
}

static uint64_t truss_descriptors_key(void) { return (uint64_t)(uintptr_t)&truss_task_self()->wait_key; }

uint64_t truss_runtime_descriptors_watch(void) { return truss_runtime_tasks_watch(truss_descriptors_key()); }

int32_t truss_runtime_descriptors_wait(const int32_t *descriptors, size_t count, uint64_t ticket) {
  uint64_t key = truss_descriptors_key();
  int registered = 1;
  for (size_t index = 0; index < count && registered; index++)
    if (descriptors[index] >= 0) registered = truss_descriptor_register(descriptors[index], key);
  if (registered) {
    truss_wait(key, ticket, 1);
  } else {
    truss_runtime_blocking_begin();
    truss_descriptors_poll(descriptors, count);
    truss_runtime_blocking_end();
  }
  if (truss_runtime_tasks_cancelled()) {
    *truss_runtime_errno_address_uncached() = EINTR;
    return 0;
  }
  return 1;
}

int32_t truss_runtime_close(int32_t descriptor) {
  if (descriptor >= 0 && descriptor < TRUSS_DESCRIPTORS)
    atomic_store(&truss_descriptor_registered[descriptor], 0);
  return close(descriptor);
}

int32_t truss_runtime_dup2(int32_t descriptor, int32_t target) {
  if (target >= 0 && target < TRUSS_DESCRIPTORS)
    atomic_store(&truss_descriptor_registered[target], 0);
  return dup2(descriptor, target);
}

int truss_runtime_posix_spawnp(int *process, const char *program, const void *file_actions,
                           char *const *arguments, char *const *environment) {
  posix_spawnattr_t attributes;
  int failed = posix_spawnattr_init(&attributes);
  if (failed) return failed;
  sigset_t signals;
  sigemptyset(&signals);
  posix_spawnattr_setsigmask(&attributes, &signals);
  sigaddset(&signals, SIGPIPE);
  posix_spawnattr_setsigdefault(&attributes, &signals);
  posix_spawnattr_setflags(&attributes, (short)(POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF));
  failed = posix_spawnp(process, program, file_actions, &attributes, arguments, environment);
  posix_spawnattr_destroy(&attributes);
  return failed;
}

static struct truss_group *truss_group_new(struct truss_group *parent) {
  struct truss_group *group = malloc(sizeof *group);
  if (group == NULL) truss_out_of_memory();
  pthread_mutex_init(&group->lock, NULL);
  group->running = 0;
  atomic_init(&group->cancelled, 0);
  group->parent = parent;
  group->tasks = NULL;
  group->children = NULL;
  group->next = NULL;
  group->joiner = NULL;
  group->interrupted = NULL;
  if (parent != NULL) {
    pthread_mutex_lock(&parent->lock);
    group->next = parent->children;
    parent->children = group;
    pthread_mutex_unlock(&parent->lock);
  }
  return group;
}

uint64_t truss_runtime_tasks_open(void) { return (uint64_t)(uintptr_t)truss_group_new(truss_task_self()->group); }

static void truss_task_entry(void) {
  struct truss_task *task = truss_task_self();
#ifdef TRUSS_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(NULL, &task->thread_stack, &task->thread_stack_size);
#endif
  task->code(task->environment, task->item, 0);
  struct truss_group *group = task->group;
  struct truss_task *joiner = NULL;
  pthread_mutex_lock(&group->lock);
  for (struct truss_task **link = &group->tasks; *link != NULL; link = &(*link)->sibling)
    if (*link == task) {
      *link = task->sibling;
      break;
    }
  group->running -= 1;
  if (group->running == 0) {
    joiner = group->joiner;
    group->joiner = NULL;
  }
  pthread_mutex_unlock(&group->lock);
  if (joiner != NULL) truss_task_ready(joiner);
  task->finished = 1;
  truss_task_switch(task);
  truss_runtime_compiler_bug();
}

static struct truss_task *truss_task_new(struct truss_group *group, void (*code)(void *environment, uint64_t item, void *capabilities),
                                 void *environment, uint64_t item) {
  struct truss_task *task = malloc(sizeof *task);
  if (task == NULL) truss_out_of_memory();
  task->stack = truss_stack_acquire();
  truss_context_start(&task->context, task->stack, truss_stack_bytes, truss_task_entry);
  task->group = group;
  task->code = code;
  task->environment = environment;
  task->item = item;
  task->next = NULL;
  atomic_init(&task->blocking, 0);
  atomic_init(&task->state, TRUSS_TASK_RUNNING);
  atomic_init(&task->cancellable, NULL);
  task->finished = 0;
  task->coroutine = NULL;
#ifdef TRUSS_ADDRESS_SANITIZER
  task->suspended_stack = task->stack;
  task->suspended_stack_size = truss_stack_bytes;
#endif
#ifdef TRUSS_THREAD_SANITIZER
  task->fiber = __tsan_create_fiber(0);
  task->suspended_fiber = task->fiber;
#endif
  pthread_mutex_lock(&group->lock);
  group->running += 1;
  task->sibling = group->tasks;
  group->tasks = task;
  pthread_mutex_unlock(&group->lock);
  return task;
}

uint8_t truss_runtime_tasks_spawn(uint64_t handle, void (*code)(void *environment, uint64_t item, void *capabilities),
                              void *environment, uint64_t item) {
  struct truss_group *group = (struct truss_group *)(uintptr_t)handle;
  if (atomic_load_explicit(&group->cancelled, memory_order_acquire)) return 0;
  pthread_once(&truss_pool_once, truss_pool_start);
  pthread_once(&truss_interrupt_once, truss_interrupt_start);
  truss_run_push(truss_task_new(group, code, environment, item));
  return 1;
}

int32_t truss_runtime_tasks_join(uint64_t handle) {
  struct truss_group *group = (struct truss_group *)(uintptr_t)handle;
  pthread_mutex_lock(&group->lock);
  while (group->running > 0) {
    struct truss_task *task = truss_task_self();
    group->joiner = task;
    truss_task_park(task, &group->lock);
    pthread_mutex_lock(&group->lock);
  }
  pthread_mutex_unlock(&group->lock);
  if (atomic_load(&group->cancelled)) {
    pthread_mutex_lock(&truss_interrupter_lock);
    for (struct truss_group **link = &truss_interrupter_groups; *link != NULL; link = &(*link)->interrupted)
      if (*link == group) {
        *link = group->interrupted;
        break;
      }
    pthread_mutex_unlock(&truss_interrupter_lock);
  }
  if (group->parent != NULL) {
    pthread_mutex_lock(&group->parent->lock);
    for (struct truss_group **link = &group->parent->children; *link != NULL; link = &(*link)->next)
      if (*link == group) {
        *link = group->next;
        break;
      }
    pthread_mutex_unlock(&group->parent->lock);
  }
  pthread_mutex_destroy(&group->lock);
  free(group);
  return 0;
}

int32_t truss_runtime_tasks_cancel(uint64_t handle) {
  struct truss_group *group = (struct truss_group *)(uintptr_t)handle;
  int cancelled = 0;
  if (!atomic_compare_exchange_strong(&group->cancelled, &cancelled, 1)) return 0;
  pthread_mutex_lock(&group->lock);
  truss_group_wake(group);
  pthread_mutex_unlock(&group->lock);
  pthread_once(&truss_interrupt_once, truss_interrupt_start);
  pthread_mutex_lock(&truss_interrupter_lock);
  group->interrupted = truss_interrupter_groups;
  truss_interrupter_groups = group;
  pthread_cond_signal(&truss_interrupter_wake);
  pthread_mutex_unlock(&truss_interrupter_lock);
  return 1;
}

struct truss_root {
  void (*code)(void *environment, uint64_t item, void *capabilities);
  void *environment;
  atomic_int ended;
};

static void truss_root_run(void *argument, uint64_t item, void *capabilities) {
  struct truss_root *root = argument;
  (void)capabilities;
  root->code(root->environment, item, 0);
  atomic_store(&root->ended, 1);
  truss_wake(1);
}

void truss_runtime_main(void (*code)(void *environment, uint64_t item, void *capabilities), void *environment,
                    uint32_t requested_workers) {
  truss_install_signal_dispositions();
  truss_requested_workers = requested_workers;
  truss_self = &truss_workers[0];
  atomic_store(&truss_worker_count, 1);
  struct truss_root root = {code, environment, 0};
  truss_task_run(truss_task_new(truss_group_new(NULL), truss_root_run, &root, 0));
  truss_run_until(&truss_workers[0], &root.ended);
}

static void truss_wake_one(uint64_t key) {
  struct truss_wait_slot *slot = truss_wait_slot(key);
  struct truss_task **link = NULL;
  pthread_mutex_lock(&slot->lock);
  atomic_fetch_add(&slot->wakes, 1);
  for (struct truss_task **parked = &slot->parked; *parked != NULL; parked = &(*parked)->next)
    if ((*parked)->wait_key == key) link = parked;
  struct truss_task *woken = NULL;
  if (link != NULL) {
    woken = *link;
    *link = woken->next;
  }
  pthread_mutex_unlock(&slot->lock);
  if (woken != NULL) truss_task_ready(woken);
}

int32_t truss_runtime_tasks_lock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  uint64_t unlocked = 0;
  if (__atomic_compare_exchange_n(word, &unlocked, 1, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
    return 0;
  for (;;) {
    uint64_t ticket = truss_runtime_tasks_watch(mutex);
    if (__atomic_exchange_n(word, 2, __ATOMIC_SEQ_CST) == 0) return 0;
    truss_wait(mutex, ticket, 0);
  }
}

int32_t truss_runtime_tasks_unlock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  if (__atomic_exchange_n(word, 0, __ATOMIC_SEQ_CST) == 2) truss_wake_one(mutex);
  return 0;
}

int32_t truss_runtime_tasks_yield(void) {
  truss_task_switch(truss_task_self());
  return 0;
}

static atomic_uint_fast64_t truss_signals_pending;
static uint64_t truss_signals_handled;
static pthread_mutex_t truss_signals_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t truss_signals_once = PTHREAD_ONCE_INIT;
static int truss_signals_pipe[2];

static void truss_signals_handler(int signal) {
  int saved = errno;
  atomic_fetch_or(&truss_signals_pending, (uint_fast64_t)1 << signal);
  ssize_t written = write(truss_signals_pipe[1], "", 1);
  (void)written;
  errno = saved;
}

static void truss_signals_arrived(void) {
  char bytes[64];
  while (read(truss_signals_pipe[0], bytes, sizeof bytes) > 0) {
  }
  sigset_t handled;
  sigemptyset(&handled);
  pthread_mutex_lock(&truss_signals_lock);
  for (int signal = 1; signal < 64; signal++)
    if (truss_signals_handled & ((uint64_t)1 << signal)) sigaddset(&handled, signal);
  pthread_mutex_unlock(&truss_signals_lock);
  pthread_sigmask(SIG_UNBLOCK, &handled, NULL);
  truss_runtime_tasks_wake((uint64_t)(uintptr_t)&truss_signals_pending);
}

static void truss_signals_start(void) {
  if (pipe(truss_signals_pipe) != 0) truss_out_of_memory();
  for (int end = 0; end < 2; end++) {
    fcntl(truss_signals_pipe[end], F_SETFD, FD_CLOEXEC);
    fcntl(truss_signals_pipe[end], F_SETFL, fcntl(truss_signals_pipe[end], F_GETFL) | O_NONBLOCK);
  }
  pthread_once(&truss_poller_once, truss_poller_start);
#ifdef __linux__
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN;
  event.data.u64 = TRUSS_SIGNALS_EVENT;
  if (epoll_ctl(truss_poller, EPOLL_CTL_ADD, truss_signals_pipe[0], &event) != 0) truss_out_of_memory();
#else
  struct kevent change;
  EV_SET(&change, truss_signals_pipe[0], EVFILT_READ, EV_ADD, 0, 0, (void *)(uintptr_t)TRUSS_SIGNALS_EVENT);
  if (kevent(truss_poller, &change, 1, NULL, 0, NULL) != 0) truss_out_of_memory();
#endif
}

int32_t truss_runtime_signals_wait(const int32_t *signals, size_t count) {
  pthread_once(&truss_signals_once, truss_signals_start);
  uint_fast64_t wanted = 0;
  int installed = 0;
  pthread_mutex_lock(&truss_signals_lock);
  for (size_t index = 0; index < count; index++) {
    int32_t signal = signals[index];
    if (signal <= 0 || signal >= 64) continue;
    uint64_t bit = (uint64_t)1 << signal;
    wanted |= bit;
    if (!(truss_signals_handled & bit)) {
      struct sigaction action;
      memset(&action, 0, sizeof action);
      action.sa_handler = truss_signals_handler;
      sigfillset(&action.sa_mask);
      action.sa_flags = SA_RESTART;
      if (sigaction(signal, &action, NULL) == 0) {
        truss_signals_handled |= bit;
        installed = 1;
      }
    }
  }
  pthread_mutex_unlock(&truss_signals_lock);
  if (installed) {
    ssize_t written = write(truss_signals_pipe[1], "", 1);
    (void)written;
  }
  uint64_t key = (uint64_t)(uintptr_t)&truss_signals_pending;
  for (;;) {
    uint64_t ticket = truss_runtime_tasks_watch(key);
    sigset_t pending_signals;
    if (sigpending(&pending_signals) == 0)
      for (size_t index = 0; index < count; index++) {
        int32_t signal = signals[index];
        if (signal <= 0 || signal >= 64 || sigismember(&pending_signals, signal) != 1) continue;
        sigset_t single;
        sigemptyset(&single);
        sigaddset(&single, signal);
#ifdef __linux__
        struct timespec immediately = {0, 0};
        if (sigtimedwait(&single, NULL, &immediately) == signal) return signal;
#else
        int arrived = 0;
        if (sigwait(&single, &arrived) == 0) return arrived;
#endif
      }
    uint_fast64_t pending = atomic_load(&truss_signals_pending);
    while (pending & wanted) {
      uint_fast64_t arrived = pending & wanted;
      uint_fast64_t lowest = arrived & (~arrived + 1);
      if (atomic_compare_exchange_weak(&truss_signals_pending, &pending, pending & ~lowest))
        return (int32_t)__builtin_ctzll(lowest);
    }
    if (truss_runtime_tasks_cancelled()) return 0;
    truss_wait(key, ticket, 1);
  }
}
|}

let resolving =
  {|
long truss_runtime_addresses_of_host(const char *host, void *room, size_t size) {
  struct addrinfo wanted;
  memset(&wanted, 0, sizeof wanted);
  wanted.ai_socktype = SOCK_STREAM;
  struct addrinfo *found = NULL;
  int failed = getaddrinfo(host, NULL, &wanted, &found);
  if (failed != 0) {
#ifdef EAI_NODATA
    if (failed == EAI_NODATA) return -1;
#endif
    return failed == EAI_NONAME ? -1 : -2;
  }
  uint8_t *bytes = room;
  size_t used = 0;
  for (const struct addrinfo *each = found; each != NULL; each = each->ai_next) {
    if (each->ai_family == AF_INET && size - used >= 5) {
      bytes[used] = 4;
      memcpy(bytes + used + 1, &((const struct sockaddr_in *)(const void *)each->ai_addr)->sin_addr, 4);
      used += 5;
    } else if (each->ai_family == AF_INET6 && size - used >= 17) {
      bytes[used] = 6;
      memcpy(bytes + used + 1, &((const struct sockaddr_in6 *)(const void *)each->ai_addr)->sin6_addr, 16);
      used += 17;
    }
  }
  freeaddrinfo(found);
  return (long)used;
}
|}

let tests_table =
  {|
typedef void (*truss_test)(void);
const truss_test *truss_runtime_tests;
uint64_t truss_runtime_cpu_limit_milliseconds;

static void truss_cpu_limit_reached(int signal) {
  (void)signal;
  (void)pthread_mutex_trylock(&truss_text_lock);
  truss_text_length = 0;
  truss_text_string("it used more than ");
  truss_text_number(truss_runtime_cpu_limit_milliseconds);
  truss_text_string(" ms of CPU time");
  truss_end(truss_timed_out, "", 101);
}

static void truss_limit_cpu_time(uint64_t milliseconds) {
  struct itimerval limit;
  memset(&limit, 0, sizeof limit);
  limit.it_value.tv_sec = (time_t)(milliseconds / 1000u);
  limit.it_value.tv_usec = (suseconds_t)(milliseconds % 1000u * 1000u);
  setitimer(ITIMER_PROF, &limit, NULL);
}

void truss_runtime_run_test(uint32_t index) {
  if (truss_runtime_cpu_limit_milliseconds == 0) {
    truss_runtime_tests[index]();
    return;
  }
  signal(SIGPROF, truss_cpu_limit_reached);
  sigset_t timer;
  sigemptyset(&timer);
  sigaddset(&timer, SIGPROF);
  pthread_sigmask(SIG_UNBLOCK, &timer, NULL);
  truss_limit_cpu_time(truss_runtime_cpu_limit_milliseconds);
  truss_runtime_tests[index]();
  truss_limit_cpu_time(0);
}
|}

let runtime_line_control = "#line 1 \"<runtime>\"\n"

let render_runtime ~tests =
  String.concat ""
    [
      runtime_line_control;
      (if tests then "#define TRUSS_TESTS 1\n" else "");
      headers;
      Emit_c.shared_structs;
      failing;
      assumed_cpu_features;
      allocation;
      threads;
      resolving;
      (if tests then tests_table else "");
    ]

let render_start ?(before_start = "") ~declarations ~requested_workers root_call =
  Printf.sprintf
    "%stypedef __INT32_TYPE__ int32_t;\n\
     typedef __UINT32_TYPE__ uint32_t;\n\
     typedef __UINT64_TYPE__ uint64_t;\n\
     void truss_runtime_main(void (*code)(void *environment, uint64_t item, void *capabilities), \
     void *environment,\n\
    \                    uint32_t requested_workers);\n\
     %sstruct truss_program {\n\
    \  int32_t count;\n\
    \  void *arguments;\n\
    \  int32_t status;\n\
     };\n\
     static void truss_program_run(void *environment, uint64_t item, void *capabilities) {\n\
    \  struct truss_program *program = environment;\n\
    \  (void)item;\n\
    \  (void)capabilities;\n\
    \  %s;\n\
     }\n\
     int main(int count, char **arguments) {\n\
    \  struct truss_program program = {(int32_t)count, (void *)arguments, 0};\n\
     %s  truss_runtime_main(truss_program_run, &program, %d);\n\
    \  return (int)program.status;\n\
     }\n"
    runtime_line_control declarations root_call before_start requested_workers

let render_main_start entry =
  render_start
    ~declarations:(Printf.sprintf "int32_t %s(void);\n" entry)
    ~requested_workers:0
    (Printf.sprintf "program->status = %s()" entry)

let render_tests_start ~time_limit_ms ~cpu_time_limit_ms ~runner tests =
  let test_declarations =
    String.concat "" (List.map (fun symbol -> Printf.sprintf "void %s(void);\n" symbol) tests)
  in
  render_start
    ~declarations:
      (Printf.sprintf
         "typedef void (*truss_test)(void);\n\
          extern const truss_test *truss_runtime_tests;\n\
          extern uint64_t truss_runtime_cpu_limit_milliseconds;\n\
          int32_t %s(uint32_t count, uint32_t time_limit_milliseconds);\n\
          %sstatic const truss_test truss_tests[] = { %s };\n"
         runner test_declarations
         (if tests = [] then "0" else String.concat ", " tests))
    ~before_start:
      (Printf.sprintf
         "  truss_runtime_tests = truss_tests;\n  truss_runtime_cpu_limit_milliseconds = %d;\n"
         cpu_time_limit_ms)
    ~requested_workers:1
    (Printf.sprintf "program->status = %s(%d, %d)" runner (List.length tests) time_limit_ms)

let render_program_start entry =
  render_start
    ~declarations:(Printf.sprintf "int32_t %s(int32_t count, void *arguments);\n" entry)
    ~requested_workers:0
    (Printf.sprintf "program->status = %s(program->count, program->arguments)" entry)

module For_testing = struct
  let render_main_start = render_main_start
end
