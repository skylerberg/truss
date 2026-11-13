(* The runtime is C, kept here as text. Its parts: writing and failing,
   which every program uses; allocation; the threads that run branches at
   once; and a test program's output to the runner, which is Truss in the
   standard library. *)

let headers =
  (* Strict C11 hides POSIX functions such as [posix_memalign] and
     [sigaltstack] in glibc unless they are asked for. *)
  {|#define _DEFAULT_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
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
#else
#include <sys/event.h>
#endif
#include <netinet/in.h>
#include <netdb.h>
|}

let failing =
  {|
static void t_write_all(int descriptor, const void *bytes, size_t length) {
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

/* The address of [errno] on the calling thread. Generated code reads
   [errno] through this function. glibc declares its own function for the
   address as one that returns the same address on every call, so a
   compiler may reuse the address after a task has parked and resumed on
   another thread, and the task would read that thread's [errno]. The
   empty assembly keeps the compiler from concluding the same of this
   function. A release build optimizes across the runtime and the
   generated code, so a function of the runtime that generated code calls
   reads [errno] through this function too. */
__attribute__((noinline)) int *t_runtime_errno(void) {
  __asm__ __volatile__("");
  return &errno;
}

void *t_runtime_allocate(t_usize size, t_usize alignment);

/* A test worker reports to the runner through this pipe; anywhere else it
   is -1, and reports go to standard error. */
static int t_report = -1;

void t_runtime_report_tests_to(int32_t descriptor) { t_report = descriptor; }

/* The kinds of record a worker writes. The runner, in the standard library,
   numbers them the same way, and writes the first itself. */
enum { t_passed, t_failed, t_panicked, t_incomplete, t_echoed };

/* Text is built in a fixed buffer, so that failing never allocates, even
   when it fails because memory ran out. Longer text is cut short. One
   thread at a time builds text, and a thread that is ending the run never
   gives the buffer up, so one failure is reported. */
static char t_text[65536];
static size_t t_text_length;
static pthread_mutex_t t_text_lock = PTHREAD_MUTEX_INITIALIZER;

static void t_text_add(const void *bytes, size_t length) {
  size_t room = sizeof t_text - t_text_length;
  if (length > room) length = room;
  memcpy(t_text + t_text_length, bytes, length);
  t_text_length += length;
}

static void t_text_string(const char *text) { t_text_add(text, strlen(text)); }

static void t_text_number(uint64_t number) {
  char digits[20];
  size_t count = 0;
  do {
    digits[sizeof digits - 1 - count] = (char)('0' + number % 10);
    number /= 10;
    count += 1;
  } while (number > 0);
  t_text_add(digits + sizeof digits - count, count);
}

static void t_text_position(const struct t_anchor *anchor, uint32_t line, uint32_t column) {
  if (anchor) {
    t_text_add(anchor->path, anchor->path_length);
    t_text_string(":");
    t_text_number((uint64_t)anchor->line + line);
  } else {
    t_text_string("generated code:");
    t_text_number(line);
  }
  t_text_string(":");
  t_text_number(column);
}

/* A record is its kind, the length of its text in four bytes, the low one
   first, and the text. */
static void t_record(uint8_t kind) {
  uint8_t header[5];
  uint32_t length = (uint32_t)t_text_length;
  header[0] = kind;
  for (int byte = 0; byte < 4; byte++) header[1 + byte] = (uint8_t)(length >> (8 * byte));
  t_write_all(t_report, header, sizeof header);
  t_write_all(t_report, t_text, t_text_length);
}

/* Ends the run with a report of [kind] and the text built so far: in a test
   worker, as a record for the runner, and anywhere else on standard error
   after [heading]. */
static _Noreturn void t_end(uint8_t kind, const char *heading, int status) {
  if (t_report >= 0) {
    t_record(kind);
    _exit(status);
  }
  t_write_all(2, heading, strlen(heading));
  t_write_all(2, t_text, t_text_length);
  t_write_all(2, "\n", 1);
  _exit(status);
}

static void t_describe(const uint8_t *message, t_usize length, const struct t_anchor *anchor, uint32_t line,
                       uint32_t column) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_add(message, length);
  t_text_string("\n  at ");
  t_text_position(anchor, line, column);
}

_Noreturn void t_runtime_panic(const uint8_t *message, t_usize length, const struct t_anchor *anchor,
                               uint32_t line, uint32_t column) {
  t_describe(message, length, anchor, line, column);
  t_end(t_panicked, "panic: ", 101);
}

_Noreturn void t_runtime_assertion_failed(const uint8_t *message, t_usize length,
                                          const struct t_anchor *anchor, uint32_t line, uint32_t column) {
  t_describe(message, length, anchor, line, column);
  t_end(t_failed, "assertion failed: ", 1);
}

_Noreturn void t_runtime_todo(const uint8_t *message, t_usize length, const struct t_anchor *anchor,
                              uint32_t line, uint32_t column) {
  t_describe(message, length, anchor, line, column);
  t_end(t_incomplete, "todo reached: ", 101);
}

void t_runtime_echo(const uint8_t *text, t_usize length, const struct t_anchor *anchor, uint32_t line,
                    uint32_t column) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_position(anchor, line, column);
  t_text_string(": ");
  t_text_add(text, length);
  if (t_report >= 0) {
    t_record(t_echoed);
  } else {
    t_write_all(2, "echo ", 5);
    t_write_all(2, t_text, t_text_length);
    t_write_all(2, "\n", 1);
  }
  pthread_mutex_unlock(&t_text_lock);
}

_Noreturn void t_runtime_compiler_bug(void) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_string("reached code the prover showed unreachable");
  t_end(t_panicked, "compiler bug: ", 101);
}

static _Noreturn void t_out_of_memory(void) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_string("out of memory");
  if (t_report >= 0) t_end(t_panicked, "", 101);
  t_write_all(2, "out of memory\n", 14);
  abort();
}

static char t_signal_stack[65536];

static void t_stack_overflow(int signal) {
  (void)signal;
  /* The thread may hold the lock already, so it is taken only if free. */
  (void)pthread_mutex_trylock(&t_text_lock);
  t_text_length = 0;
  t_text_string("stack overflow");
  t_end(t_panicked, "", 101);
}

void t_runtime_install(void) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  stack.ss_sp = t_signal_stack;
  stack.ss_size = sizeof t_signal_stack;
  sigaltstack(&stack, NULL);
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = t_stack_overflow;
  action.sa_flags = SA_ONSTACK;
  sigemptyset(&action.sa_mask);
  sigaction(SIGSEGV, &action, NULL);
  sigaction(SIGBUS, &action, NULL);
  /* A write to a socket or a pipe whose reader has gone is an error the
     program sees, SystemError.BrokenPipe, not a signal that ends it: a
     server must outlive a client that hangs up. */
  signal(SIGPIPE, SIG_IGN);
}
|}

let allocation =
  {|
/* In a test program, how many blocks are allocated and not yet freed. A
   test must end with as many as it started with: Truss frees every block
   it allocates, so a test that leaves one is a compiler bug. A program
   that is not a test program counts nothing. */
#ifdef T_TESTS
static t_usize t_live_blocks = 0;
#define t_block_allocated() (t_live_blocks += 1)
#define t_block_freed() (t_live_blocks -= 1)
t_usize t_runtime_live_blocks(void) { return t_live_blocks; }
#else
#define t_block_allocated() ((void)0)
#define t_block_freed() ((void)0)
#endif

void *t_runtime_allocate(t_usize size, t_usize alignment) {
  void *pointer = NULL;
  if (size == 0) size = 1;
  if (alignment <= 16) {
    pointer = malloc(size);
  } else if (posix_memalign(&pointer, alignment, size) != 0) {
    pointer = NULL;
  }
  if (pointer == NULL) t_out_of_memory();
  t_block_allocated();
  return pointer;
}

void t_runtime_free(void *pointer) {
  t_block_freed();
  free(pointer);
}

void *t_runtime_reallocate(void *pointer, t_usize old_size, t_usize size, t_usize alignment) {
  if (size == 0) size = 1;
  if (alignment <= 16) {
    void *moved = realloc(pointer, size);
    if (moved == NULL) t_out_of_memory();
    return moved;
  }
  void *moved = t_runtime_allocate(size, alignment);
  memcpy(moved, pointer, old_size < size ? old_size : size);
  t_runtime_free(pointer);
  return moved;
}

|}

let threads =
  {|
/* The size of the main thread's stack. Every other stack has the same
   size, so that the recursion depth limit is the same on each. */
static size_t t_stack_size(void) {
  struct rlimit limit;
  size_t stack = (size_t)8 << 20;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY &&
      limit.rlim_cur >= ((rlim_t)1 << 16) && limit.rlim_cur <= ((rlim_t)1 << 30))
    stack = (size_t)limit.rlim_cur;
  return stack;
}

#ifndef T_IN_ORDER

/* Installs an alternate signal stack on the calling thread, so that the
   handler of a stack overflow can run. A thread of the runtime never
   exits, so the stack is never removed. */
static void t_thread_signal_stack_install(void) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  stack.ss_sp = malloc(65536);
  if (stack.ss_sp == NULL) return;
  stack.ss_size = 65536;
  if (sigaltstack(&stack, NULL) != 0) free(stack.ss_sp);
}

/* The attributes of a thread that the runtime creates. */
static void t_thread_attributes(pthread_attr_t *attributes) {
  pthread_attr_init(attributes);
  pthread_attr_setstacksize(attributes, t_stack_size());
}

#endif

/* Sanitizer hooks for switching stacks. */
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define T_ADDRESS_SANITIZER 1
#endif
#if __has_feature(thread_sanitizer)
#define T_THREAD_SANITIZER 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__) && !defined(T_ADDRESS_SANITIZER)
#define T_ADDRESS_SANITIZER 1
#endif
#if defined(__SANITIZE_THREAD__) && !defined(T_THREAD_SANITIZER)
#define T_THREAD_SANITIZER 1
#endif

#ifdef T_ADDRESS_SANITIZER
void __sanitizer_start_switch_fiber(void **fake_stack_save, const void *bottom, size_t size);
void __sanitizer_finish_switch_fiber(void *fake_stack_save, const void **bottom_old,
                                     size_t *size_old);
void __asan_unpoison_memory_region(void const volatile *address, size_t size);
#endif
#ifdef T_THREAD_SANITIZER
void *__tsan_get_current_fiber(void);
void *__tsan_create_fiber(unsigned flags);
void __tsan_destroy_fiber(void *fiber);
void __tsan_switch_to_fiber(void *fiber, unsigned flags);
#endif

/* Stacks.

   A coroutine runs on a stack of its own: memory from [mmap] with a guard
   page below it, so that an overflow faults and is reported as any stack
   overflow is. A stack is as large as the main thread's. Its pages take
   memory only once they are touched. A few stacks that are no longer used
   are kept for the next coroutine. */
#define T_STACK_CACHE 64

static pthread_mutex_t t_stack_lock = PTHREAD_MUTEX_INITIALIZER;
static void *t_stack_cache[T_STACK_CACHE];
static size_t t_stack_cached;
static size_t t_stack_bytes;
static size_t t_stack_guard;

/* The lowest address of a stack's usable memory. */
static void *t_stack_acquire(void) {
  pthread_mutex_lock(&t_stack_lock);
  if (t_stack_bytes == 0) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    t_stack_guard = page;
    t_stack_bytes = (t_stack_size() + page - 1) / page * page;
  }
  void *low = t_stack_cached > 0 ? t_stack_cache[--t_stack_cached] : NULL;
  pthread_mutex_unlock(&t_stack_lock);
  if (low != NULL) return low;
  int flags = MAP_PRIVATE | MAP_ANON;
#ifdef MAP_NORESERVE
  flags |= MAP_NORESERVE;
#endif
#ifdef MAP_STACK
  flags |= MAP_STACK;
#endif
  char *mapping = mmap(NULL, t_stack_guard + t_stack_bytes, PROT_READ | PROT_WRITE, flags, -1, 0);
  if (mapping == MAP_FAILED) t_out_of_memory();
  if (mprotect(mapping, t_stack_guard, PROT_NONE) != 0) t_out_of_memory();
  return mapping + t_stack_guard;
}

static void t_stack_release(void *low) {
#ifdef T_ADDRESS_SANITIZER
  /* The last coroutine's poisoned frames must not be reported against
     the next one. */
  __asan_unpoison_memory_region(low, t_stack_bytes);
#endif
  pthread_mutex_lock(&t_stack_lock);
  if (t_stack_cached < T_STACK_CACHE) {
    t_stack_cache[t_stack_cached++] = low;
    low = NULL;
  }
  pthread_mutex_unlock(&t_stack_lock);
  if (low != NULL) munmap((char *)low - t_stack_guard, t_stack_guard + t_stack_bytes);
}

/* Switching stacks.

   A context is the stack pointer of code that is not running. Its
   callee-saved registers are on its stack, below that pointer, and the
   address it resumes at is the return address of its call of
   [t_context_switch]. The function saves the caller's registers and stack
   pointer in [from] and loads those of [to]. */
struct t_context {
  void *stack_pointer;
};

void t_context_switch(struct t_context *from, const struct t_context *to);

#ifdef __APPLE__
#define T_ASSEMBLY_NAME(name) "_" name
#else
#define T_ASSEMBLY_NAME(name) name
#endif

#if defined(__x86_64__)
__asm__(".text\n"
        ".globl " T_ASSEMBLY_NAME("t_context_switch") "\n"
        ".p2align 4\n"
        T_ASSEMBLY_NAME("t_context_switch") ":\n"
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

/* A context that starts [entry] on an empty stack: the registers that the
   switch pops, the address it returns to, and a word that leaves the
   stack pointer where a call would. */
static void t_context_start(struct t_context *context, void *low, size_t size, void (*entry)(void)) {
  uint64_t *top = (uint64_t *)(((uintptr_t)low + size) & ~(uintptr_t)15);
  *--top = 0;
  *--top = (uint64_t)(uintptr_t)entry;
  for (int saved = 0; saved < 6; saved++) *--top = 0;
  context->stack_pointer = top;
}
#elif defined(__aarch64__)
__asm__(".text\n"
        ".globl " T_ASSEMBLY_NAME("t_context_switch") "\n"
        ".p2align 2\n"
        T_ASSEMBLY_NAME("t_context_switch") ":\n"
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

/* A context that starts [entry] on an empty stack: the registers that the
   switch loads, with [entry] as the address it returns to. */
static void t_context_start(struct t_context *context, void *low, size_t size, void (*entry)(void)) {
  uint64_t *top = (uint64_t *)(((uintptr_t)low + size) & ~(uintptr_t)15);
  uint64_t *saved = top - 20;
  memset(saved, 0, 160);
  saved[11] = (uint64_t)(uintptr_t)entry;
  context->stack_pointer = saved;
}
#else
#error "the runtime has no context switch for this processor"
#endif

/* Coroutines.

   A coroutine is a function call with its own stack. It runs only between
   a resume and its next suspend. A scheduler that runs one task at a
   time, such as a test's, runs each task as a coroutine: it resumes the
   task it chose, and a task that must block suspends.

   A resume switches to the coroutine's stack on the calling thread, and a
   suspend switches back, so the two never run at the same time and no
   thread is created. */
struct t_coroutine {
  struct t_context context; /* The coroutine, while it is suspended */
  struct t_context resumer; /* The code that resumed it, while it runs */
  void *stack;
  int finished;
  void (*code)(void *environment, uint64_t item);
  void *environment;
  uint64_t item;
#ifdef T_ADDRESS_SANITIZER
  const void *resumer_stack;
  size_t resumer_stack_size;
#endif
#ifdef T_THREAD_SANITIZER
  void *fiber;
  void *resumer_fiber;
#endif
};

static _Thread_local struct t_coroutine *t_coroutine_self;

/* The coroutine that the calling thread runs, or NULL. A coroutine in a
   task resumes on another thread after the task has parked, so code that
   runs after a switch reads and writes the variable through these
   two. They are not inlined, and the empty assembly keeps the compiler
   from concluding that two calls do the same. */
__attribute__((noinline)) static struct t_coroutine *t_coroutine_current(void) {
  __asm__ __volatile__("");
  return t_coroutine_self;
}

__attribute__((noinline)) static void t_coroutine_current_set(struct t_coroutine *coroutine) {
  __asm__ __volatile__("");
  t_coroutine_self = coroutine;
}

/* Switches from the coroutine to the code that resumed it. A coroutine
   that has finished never runs again. */
static void t_coroutine_leave(struct t_coroutine *coroutine) {
#ifdef T_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(coroutine->finished ? NULL : &fake, coroutine->resumer_stack,
                                 coroutine->resumer_stack_size);
#endif
#ifdef T_THREAD_SANITIZER
  __tsan_switch_to_fiber(coroutine->resumer_fiber, 0);
#endif
  t_context_switch(&coroutine->context, &coroutine->resumer);
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &coroutine->resumer_stack,
                                  &coroutine->resumer_stack_size);
#endif
}

/* Where a coroutine starts, on its own stack. It never returns: its
   function's return switches to the resumer for the last time. */
static void t_coroutine_entry(void) {
  struct t_coroutine *coroutine = t_coroutine_current();
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(NULL, &coroutine->resumer_stack,
                                  &coroutine->resumer_stack_size);
#endif
  coroutine->code(coroutine->environment, coroutine->item);
  coroutine->finished = 1;
  t_coroutine_leave(coroutine);
  t_runtime_compiler_bug();
}

t_usize t_runtime_coroutine_start(void (*code)(void *environment, uint64_t item), void *environment,
                                  uint64_t item) {
  struct t_coroutine *coroutine = malloc(sizeof *coroutine);
  if (coroutine == NULL) t_out_of_memory();
  coroutine->stack = t_stack_acquire();
  coroutine->finished = 0;
  coroutine->code = code;
  coroutine->environment = environment;
  coroutine->item = item;
  t_context_start(&coroutine->context, coroutine->stack, t_stack_bytes, t_coroutine_entry);
#ifdef T_THREAD_SANITIZER
  coroutine->fiber = __tsan_create_fiber(0);
#endif
  return (t_usize)coroutine;
}

/* Runs a coroutine until it suspends or its function returns. Returns 1 if
   it suspended. Returns 0 if its function returned, and frees the
   coroutine. */
uint8_t t_runtime_coroutine_resume(t_usize handle) {
  struct t_coroutine *coroutine = (struct t_coroutine *)handle;
  struct t_coroutine *resumer = t_coroutine_current();
  t_coroutine_current_set(coroutine);
#ifdef T_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(&fake, coroutine->stack, t_stack_bytes);
#endif
#ifdef T_THREAD_SANITIZER
  coroutine->resumer_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(coroutine->fiber, 0);
#endif
  t_context_switch(&coroutine->resumer, &coroutine->context);
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, NULL, NULL);
#endif
  t_coroutine_current_set(resumer);
  if (!coroutine->finished) return 1;
#ifdef T_THREAD_SANITIZER
  __tsan_destroy_fiber(coroutine->fiber);
#endif
  t_stack_release(coroutine->stack);
  free(coroutine);
  return 0;
}

/* Called in a coroutine. Switches to the code that resumed the coroutine,
   and returns when the coroutine is resumed again. */
void t_runtime_coroutine_suspend(void) {
  struct t_coroutine *coroutine = t_coroutine_current();
  if (coroutine == NULL) t_runtime_compiler_bug();
  t_coroutine_leave(coroutine);
}

/* Shared values.

   The heap block of a shared value is this header followed by the value.
   A [Shared] holds the address of the value, and the header ends where
   the value starts. Every reference to the block counts in [count], and
   [mutex] is held while the value is read or changed. */
struct t_shared {
  void *block;
  atomic_size_t count;
  pthread_mutex_t mutex;
};

static struct t_shared *t_shared_header(void *value) { return (struct t_shared *)value - 1; }

void *t_runtime_shared_allocate(t_usize size, t_usize alignment) {
  if (alignment < _Alignof(struct t_shared)) alignment = _Alignof(struct t_shared);
  t_usize offset = (sizeof(struct t_shared) + alignment - 1) / alignment * alignment;
  char *block = t_runtime_allocate(offset + size, alignment);
  struct t_shared *shared = t_shared_header(block + offset);
  shared->block = block;
  atomic_init(&shared->count, 1);
  pthread_mutex_init(&shared->mutex, NULL);
  return block + offset;
}

void t_runtime_shared_retain(void *value) {
  atomic_fetch_add_explicit(&t_shared_header(value)->count, 1, memory_order_relaxed);
}

/* Returns 1 to the caller that released the last reference. The acquire
   fence orders every earlier use of the value, on any thread, before the
   drop that follows. */
uint8_t t_runtime_shared_release(void *value) {
  if (atomic_fetch_sub_explicit(&t_shared_header(value)->count, 1, memory_order_release) != 1)
    return 0;
  atomic_thread_fence(memory_order_acquire);
  return 1;
}

void t_runtime_shared_free(void *value) {
  struct t_shared *shared = t_shared_header(value);
  pthread_mutex_destroy(&shared->mutex);
  t_runtime_free(shared->block);
}

void t_runtime_shared_lock(void *value) { pthread_mutex_lock(&t_shared_header(value)->mutex); }

void t_runtime_shared_unlock(void *value) { pthread_mutex_unlock(&t_shared_header(value)->mutex); }

/* The time limit that the program set on the socket for receiving or for
   sending, in nanoseconds, or 0 if it set none or the descriptor is not a
   socket. The system applies the limit only to a call that blocks, and a
   socket that tasks wait for does not block, so the runtime's wait
   applies it. */
static uint64_t t_descriptor_limit(int32_t descriptor, int32_t writing) {
  struct timeval limit;
  socklen_t size = sizeof limit;
  if (getsockopt(descriptor, SOL_SOCKET, writing ? SO_SNDTIMEO : SO_RCVTIMEO, &limit, &size) != 0)
    return 0;
  return (uint64_t)limit.tv_sec * 1000000000u + (uint64_t)limit.tv_usec * 1000u;
}

/* Waits in [poll] until the descriptor can be read, or written, or the
   time limit passes. Returns 0 if the limit passed. */
static int32_t t_descriptor_poll(int32_t descriptor, int32_t writing) {
  uint64_t limit = t_descriptor_limit(descriptor, writing);
  uint64_t milliseconds = (limit + 999999u) / 1000000u;
  struct pollfd one = {descriptor, writing ? POLLOUT : POLLIN, 0};
  int timeout = limit == 0 ? -1 : milliseconds > INT32_MAX ? INT32_MAX : (int)milliseconds;
  return poll(&one, 1, timeout) != 0;
}

/* Waits in [poll] until one of the descriptors can be read. [poll] skips
   a negative descriptor. */
static void t_descriptors_poll(const int32_t *descriptors, size_t count) {
  if (count == 0) return;
  struct pollfd *waited = malloc(count * sizeof *waited);
  if (waited == NULL) t_out_of_memory();
  for (size_t index = 0; index < count; index++) {
    waited[index].fd = descriptors[index];
    waited[index].events = POLLIN;
    waited[index].revents = 0;
  }
  poll(waited, (nfds_t)count, -1);
  free(waited);
}

/* Tasks, in a runtime that starts no thread. */

#ifdef T_IN_ORDER

/* A test program, and code run while compiling, have one thread.
   [t_runtime_tasks_spawn] calls the task's function and returns when it
   returns, so the tasks of a group run sequentially, in the order they
   are spawned. That is correct for tasks that never block on one another.
   A task that waits on a key would deadlock, because the task that would
   wake it cannot run, so [t_runtime_tasks_wait] panics. */
struct t_group {
  int cancelled;
};

uint64_t t_runtime_tasks_open(void) {
  struct t_group *group = malloc(sizeof *group);
  if (group == NULL) t_out_of_memory();
  group->cancelled = 0;
  return (uint64_t)(uintptr_t)group;
}

uint8_t t_runtime_tasks_spawn(uint64_t handle, void (*code)(void *environment, uint64_t item),
                              void *environment, uint64_t item) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  if (group->cancelled) return 0;
  code(environment, item);
  return 1;
}

int32_t t_runtime_tasks_join(uint64_t handle) {
  free((struct t_group *)(uintptr_t)handle);
  return 0;
}

int32_t t_runtime_tasks_cancel(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  if (group->cancelled) return 0;
  group->cancelled = 1;
  return 1;
}

int32_t t_runtime_tasks_cancelled(void) { return 0; }

uint64_t t_runtime_tasks_watch(uint64_t key) {
  (void)key;
  return 0;
}

int32_t t_runtime_tasks_wait(uint64_t key, uint64_t ticket) {
  (void)key;
  (void)ticket;
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_string("deadlock: a task waited for another task, which cannot run until this one ends");
  t_end(t_panicked, "panic: ", 101);
}

int32_t t_runtime_tasks_wake(uint64_t key) {
  (void)key;
  return 0;
}

int32_t t_runtime_tasks_lock(uint64_t mutex) {
  (void)mutex;
  return 0;
}

int32_t t_runtime_tasks_unlock(uint64_t mutex) {
  (void)mutex;
  return 0;
}

int32_t t_runtime_tasks_yield(void) { return 0; }

void t_runtime_blocking_begin(void) {}

void t_runtime_blocking_end(void) {}

/* A wait for a descriptor, and a sleep, block the one thread. */
uint64_t t_runtime_descriptor_watch(int32_t descriptor, int32_t writing) {
  (void)descriptor;
  (void)writing;
  return 0;
}

int32_t t_runtime_descriptor_wait(int32_t descriptor, int32_t writing, uint64_t ticket) {
  (void)ticket;
  if (t_descriptor_poll(descriptor, writing)) return 1;
  errno = EAGAIN;
  return 0;
}

uint64_t t_runtime_descriptors_watch(void) { return 0; }

int32_t t_runtime_descriptors_wait(const int32_t *descriptors, size_t count, uint64_t ticket) {
  (void)ticket;
  t_descriptors_poll(descriptors, count);
  return 1;
}

int32_t t_runtime_sleep(int64_t seconds, int64_t nanoseconds) {
  if (seconds < 0) return 0;
  struct timespec left = {(time_t)seconds, (long)nanoseconds};
  while (nanosleep(&left, &left) != 0 && errno == EINTR) {
  }
  return 0;
}

int32_t t_runtime_close(int32_t descriptor) { return close(descriptor); }

/* Blocks until one of the signals arrives, and returns its number. The
   signals stay blocked afterwards, so one that arrives between two calls
   is pending for the second. */
int32_t t_runtime_signals_wait(const int32_t *signals, size_t count) {
  sigset_t set;
  sigemptyset(&set);
  size_t added = 0;
  for (size_t index = 0; index < count; index++)
    if (signals[index] > 0 && sigaddset(&set, signals[index]) == 0) added += 1;
  sigprocmask(SIG_BLOCK, &set, NULL);
  for (;;) {
    int arrived = 0;
    if (added == 0)
      sleep(3600);
    else if (sigwait(&set, &arrived) == 0)
      return arrived;
  }
}

#endif

struct t_branch {
  void (*run)(void *environment);
  void *environment;
};

#ifdef T_IN_ORDER

/* A test program, and code run while compiling, run a fork's branches in
   order, which gives the same result as running them at once. A test already has
   one core of the machine, and in order a check that fails is the same
   check on every run. */
void t_runtime_parallel(const struct t_branch *branches, t_usize count) {
  for (t_usize index = 0; index < count; index++) branches[index].run(branches[index].environment);
}

void t_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t last),
                              void *environment, uint64_t first, uint64_t last) {
  body(environment, first, last);
}

#else

/* Running branches at once.

   A fork gives a thread several branches. It runs the first itself and
   offers the rest as jobs on its own queue, where a thread with nothing to
   do takes one from the far end. When its first branch returns, the thread
   takes back each job that is still there and runs it, and for a job that
   was taken it waits, running other threads' jobs meanwhile. A job lives in
   the frame of the fork that offered it, which does not return until every
   one of its jobs is done.

   The queue is Chase and Lev's, with the memory orderings of Le, Pop,
   Cohen, and Zappa Nardelli ("Correct and Efficient Work-Stealing for Weak
   Memory Models"), and a fixed size: a thread whose queue is full runs the
   branch itself, which is always right. */

struct t_job {
  void (*run)(void *environment);
  void *environment;
  atomic_int done;
  int offered;
};

#define T_QUEUE 256
#define T_WORKERS 256
#define T_SPARES 256
#define T_FORK 32

struct t_worker {
  _Alignas(64) _Atomic(int64_t) top;
  _Alignas(64) _Atomic(int64_t) bottom;
  uint64_t random;
  _Alignas(64) _Atomic(struct t_job *) jobs[T_QUEUE];
};

/* The pool's threads, and after them the spare threads, which are started
   while the program runs. */
static struct t_worker t_workers[T_WORKERS + T_SPARES];
static atomic_size_t t_worker_count;
static _Thread_local struct t_worker *t_self;

/* The calling thread's queue of branches, or NULL. A task that has parked
   resumes on another thread, and a release build optimizes across the
   runtime and the generated code. So code that generated code calls reads
   the variable through this function, which is not inlined, and whose
   empty assembly keeps the compiler from concluding that two calls
   return the same. */
__attribute__((noinline)) static struct t_worker *t_worker_self(void) {
  __asm__ __volatile__("");
  return t_self;
}
static pthread_once_t t_pool_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t t_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_pool_wake = PTHREAD_COND_INITIALIZER;
static atomic_size_t t_sleepers;
/* The sleepers that run tasks when they wake. */
static atomic_size_t t_idle_runners;

/* How many tasks are ready to run. The tasks are defined after the pool. */
static atomic_size_t t_run_count;
struct t_task;
static struct t_task *t_run_pop(void);
static void t_task_run(struct t_task *task);
static atomic_int t_blocked;
static void t_spare_ensure(void);

static int t_offer(struct t_worker *worker, struct t_job *job) {
  int64_t bottom = atomic_load_explicit(&worker->bottom, memory_order_relaxed);
  int64_t top = atomic_load_explicit(&worker->top, memory_order_acquire);
  if (bottom - top >= T_QUEUE) return 0;
  atomic_store_explicit(&worker->jobs[bottom % T_QUEUE], job, memory_order_relaxed);
  /* Sequentially consistent, so that of this store and a thread that is
     about to sleep, one sees the other. */
  atomic_store(&worker->bottom, bottom + 1);
  return 1;
}

static struct t_job *t_take_back(struct t_worker *worker) {
  int64_t bottom = atomic_load_explicit(&worker->bottom, memory_order_relaxed) - 1;
  atomic_store_explicit(&worker->bottom, bottom, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  int64_t top = atomic_load_explicit(&worker->top, memory_order_relaxed);
  struct t_job *job = NULL;
  if (top <= bottom) {
    job = atomic_load_explicit(&worker->jobs[bottom % T_QUEUE], memory_order_relaxed);
    if (top == bottom) {
      /* The last job, which a thief may be taking. */
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

static struct t_job *t_steal(struct t_worker *victim) {
  int64_t top = atomic_load_explicit(&victim->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  int64_t bottom = atomic_load_explicit(&victim->bottom, memory_order_acquire);
  if (top >= bottom) return NULL;
  struct t_job *job = atomic_load_explicit(&victim->jobs[top % T_QUEUE], memory_order_relaxed);
  if (!atomic_compare_exchange_strong_explicit(&victim->top, &top, top + 1, memory_order_seq_cst,
                                               memory_order_relaxed))
    return NULL;
  return job;
}

/* A job of another thread's, or none. */
static struct t_job *t_find(struct t_worker *self) {
  size_t count = atomic_load(&t_worker_count);
  self->random = self->random * 6364136223846793005ULL + 1442695040888963407ULL;
  size_t start = (size_t)(self->random >> 33) % count;
  for (size_t offset = 0; offset < count; offset++) {
    struct t_worker *victim = &t_workers[(start + offset) % count];
    if (victim == self) continue;
    struct t_job *job = t_steal(victim);
    if (job != NULL) return job;
  }
  return NULL;
}

static int t_any_job(void) {
  size_t count = atomic_load(&t_worker_count);
  for (size_t index = 0; index < count; index++)
    if (atomic_load(&t_workers[index].top) < atomic_load(&t_workers[index].bottom)) return 1;
  return 0;
}

static void t_wake(int everyone) {
  if (atomic_load(&t_sleepers) == 0) return;
  pthread_mutex_lock(&t_pool_lock);
  if (everyone) pthread_cond_broadcast(&t_pool_wake);
  else pthread_cond_signal(&t_pool_wake);
  pthread_mutex_unlock(&t_pool_lock);
}

/* Runs a job that was taken from another thread. Its frame may be gone as
   soon as it is marked done. */
static void t_run_taken(struct t_job *job) {
  job->run(job->environment);
  atomic_store(&job->done, 1);
  t_wake(1);
}

static void t_rest(unsigned idle) {
  if (idle < 32) {
#if defined(__x86_64__) || defined(__i386__)
    __builtin_ia32_pause();
#elif defined(__aarch64__)
    __asm__ __volatile__("yield");
#endif
  } else {
    sched_yield();
  }
}

/* Sleeps until a job is offered or a taken one is done, unless [job] is
   done or some thread has a job already. A thread that runs tasks
   ([runner]) does not sleep while a task is ready. */
static void t_sleep(struct t_job *job, int runner) {
  pthread_mutex_lock(&t_pool_lock);
  atomic_fetch_add(&t_sleepers, 1);
  if (runner) atomic_fetch_add(&t_idle_runners, 1);
  if (!(job != NULL && atomic_load(&job->done)) && !t_any_job() &&
      !(runner && atomic_load(&t_run_count) > 0))
    pthread_cond_wait(&t_pool_wake, &t_pool_lock);
  if (runner) atomic_fetch_sub(&t_idle_runners, 1);
  atomic_fetch_sub(&t_sleepers, 1);
  pthread_mutex_unlock(&t_pool_lock);
}

static void t_wait_for(struct t_worker *self, struct t_job *job) {
  unsigned idle = 0;
  while (!atomic_load_explicit(&job->done, memory_order_acquire)) {
    struct t_job *other = t_find(self);
    if (other != NULL) {
      t_run_taken(other);
      idle = 0;
    } else if (++idle < 40) {
      t_rest(idle);
    } else {
      /* The thread runs no task while it sleeps, so it counts as blocked. */
      atomic_fetch_add(&t_blocked, 1);
      t_spare_ensure();
      t_sleep(job, 0);
      atomic_fetch_sub(&t_blocked, 1);
      idle = 0;
    }
  }
}

/* A thread of the runtime that runs tasks blocks every signal but the
   faults and SIGURG. Signals sent to the process then go to the thread
   that started it, as they do in a program with one thread. SIGURG is
   the runtime's interrupt of a cancelled task. */
static void t_runner_signals(void) {
  sigset_t all;
  sigfillset(&all);
  sigdelset(&all, SIGSEGV);
  sigdelset(&all, SIGBUS);
  sigdelset(&all, SIGFPE);
  sigdelset(&all, SIGILL);
  sigdelset(&all, SIGURG);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
}

static void *t_worker_main(void *argument) {
  struct t_worker *self = argument;
  t_self = self;
  t_runner_signals();
  t_thread_signal_stack_install();
  unsigned idle = 0;
  for (;;) {
    struct t_task *task = t_run_pop();
    struct t_job *job = task == NULL ? t_find(self) : NULL;
    if (task != NULL) {
      t_task_run(task);
      idle = 0;
    } else if (job != NULL) {
      t_run_taken(job);
      idle = 0;
    } else if (++idle < 40) {
      t_rest(idle);
    } else {
      t_sleep(NULL, 1);
      idle = 0;
    }
  }
  return NULL;
}

/* Starts the pool: a thread for each core but one, since the thread that
   forks first is the pool's too. [TRUSS_WORKERS] gives another number of
   threads, which changes how long a program takes and nothing it does. */
static void t_pool_start(void) {
  long count = sysconf(_SC_NPROCESSORS_ONLN);
  const char *asked = getenv("TRUSS_WORKERS");
  if (asked != NULL && asked[0] != 0) count = strtol(asked, NULL, 10);
  if (count < 1) count = 1;
  if (count > T_WORKERS) count = T_WORKERS;
  for (long index = 0; index < count; index++) t_workers[index].random = (uint64_t)index + 1;
  atomic_store(&t_worker_count, (size_t)count);
  if (count == 1) return;
  t_self = &t_workers[0];
  pthread_attr_t attributes;
  t_thread_attributes(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  for (long index = 1; index < count; index++) {
    pthread_t thread;
    if (pthread_create(&thread, &attributes, t_worker_main, &t_workers[index]) != 0) {
      /* Fewer threads than cores is slower and still right. */
      atomic_store(&t_worker_count, (size_t)index);
      break;
    }
  }
  pthread_attr_destroy(&attributes);
  if (atomic_load(&t_worker_count) == 1) t_self = NULL;
}

/* Runs up to [T_FORK] + 1 branches at once. */
static void t_fork(struct t_worker *self, const struct t_branch *branches, size_t count) {
  struct t_job jobs[T_FORK];
  int offered = 0;
  /* The last branch is offered first, so that thieves take the last ones
     and this thread takes the others back in order. */
  for (size_t index = count - 1; index >= 1; index--) {
    struct t_job *job = &jobs[index - 1];
    job->run = branches[index].run;
    job->environment = branches[index].environment;
    atomic_init(&job->done, 0);
    job->offered = t_offer(self, job);
    offered |= job->offered;
  }
  if (offered) t_wake(0);
  branches[0].run(branches[0].environment);
  for (size_t index = 1; index < count; index++) {
    struct t_job *job = &jobs[index - 1];
    if (!job->offered) {
      job->run(job->environment);
      continue;
    }
    /* Each earlier branch's job was taken back or waited for, so the
       newest job on the queue is this one, unless a thief has
       it, and then a thief has every job offered before it too. */
    struct t_job *back = t_take_back(self);
    if (back == job) job->run(job->environment);
    else if (back == NULL) t_wait_for(self, job);
    else t_runtime_compiler_bug();
  }
}

void t_runtime_parallel(const struct t_branch *branches, t_usize count) {
  pthread_once(&t_pool_once, t_pool_start);
  /* A branch may use no capability but [Panic], so a task neither parks
     nor yields in one, and it leaves the block on the thread it entered
     it on. */
  struct t_worker *self = t_worker_self();
  if (self == NULL) {
    /* The first thread of a machine with one core: in order. */
    for (t_usize index = 0; index < count; index++) branches[index].run(branches[index].environment);
    return;
  }
  while (count > 0) {
    size_t some = count > T_FORK + 1 ? T_FORK + 1 : (size_t)count;
    t_fork(self, branches, some);
    branches += some;
    count -= some;
  }
}

struct t_range {
  void (*body)(void *environment, uint64_t first, uint64_t last);
  void *environment;
  uint64_t first;
  uint64_t last;
  uint64_t size;
};

/* Runs a range by halves, down to parts of at most [size] indexes. */
static void t_range_run(void *argument) {
  const struct t_range *range = argument;
  if (range->last - range->first < range->size) {
    range->body(range->environment, range->first, range->last);
    return;
  }
  uint64_t middle = range->first + (range->last - range->first) / 2;
  struct t_range low = *range;
  struct t_range high = *range;
  low.last = middle;
  high.first = middle + 1;
  const struct t_branch halves[2] = {{t_range_run, &low}, {t_range_run, &high}};
  t_runtime_parallel(halves, 2);
}

/* The size of a part depends on the range alone, never on the machine. */
void t_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t last),
                              void *environment, uint64_t first, uint64_t last) {
  struct t_range whole = {body, environment, first, last, ((last - first) >> 8) + 1};
  t_range_run(&whole);
}

/* Tasks.

   A task is a call of a function on a stack of its own. The pool's
   threads run the tasks that are ready, from one queue. A task that has
   to wait, for a key, a mutex, or the tasks of a group, parks: it leaves
   its stack, and the thread that ran it takes the next ready task. So a
   waiting task holds no thread, and it resumes on whichever thread takes
   it next.

   A thread that waits and is not a task blocks, and so does a thread in
   a call of the operating system that does not return at once. The C
   library's rows that can block are bracketed by
   [t_runtime_blocking_begin] and [t_runtime_blocking_end]. For each
   blocked thread, one spare thread may run tasks, so ready tasks do not
   wait behind blocked threads. */

struct t_wait_slot;

struct t_task {
  struct t_context context;   /* The task, while it does not run */
  void *stack;
  struct t_group *group;
  void (*code)(void *environment, uint64_t item);
  void *environment;
  uint64_t item;
  struct t_task *next;        /* In the ready queue, or in the object it is parked on */
  uint64_t wait_key;          /* The key that it is parked on */
  _Atomic(struct t_wait_slot *) cancellable; /* Where it parks in a wait that a cancel ends */
  struct t_task *sibling;     /* In the group's [tasks] */
  _Atomic(pthread_t) thread;  /* The thread that runs it, which the interrupter reads */
  atomic_int blocking;        /* It is in a call of the operating system that can block */
  atomic_int state;           /* T_RUNNING, T_PARKING, or T_PARKED */
  int finished;
  struct t_coroutine *coroutine; /* The coroutine that it was in when it left its thread */
#ifdef T_ADDRESS_SANITIZER
  const void *suspended_stack;   /* The stack that it left, which is a coroutine's if it was in one */
  size_t suspended_stack_size;
  const void *thread_stack;
  size_t thread_stack_size;
#endif
#ifdef T_THREAD_SANITIZER
  void *fiber;
  void *suspended_fiber;
  void *thread_fiber;
#endif
};

/* A group counts its tasks that have not ended, and [join] waits until
   the count is zero. A group is cancelled once, and a task is cancelled
   when its group or a group that encloses it is. [parent] is the group of
   the task that opened this group. It outlives this group: the task that
   opened this group joins it before the task ends. A lock is always taken
   after the lock of the enclosing group. */
struct t_group {
  pthread_mutex_t lock;
  size_t running;
  atomic_int cancelled;
  struct t_group *parent;
  struct t_task *tasks;       /* The tasks that have not ended, under [lock] */
  struct t_group *children;   /* The groups that those tasks opened, under [lock] */
  struct t_group *next;       /* In the parent's [children], under the parent's [lock] */
  struct t_task *joiner;      /* A task that is parked in [join], under [lock] */
  atomic_int *joined;         /* The flag a thread that blocks in [join] waits for, under [lock] */
  struct t_group *interrupted; /* In the list of cancelled groups */
};

/* The states of a task. A task that parks releases the lock that guards
   its wait condition before it leaves its stack, so its waker can find it
   while it still runs on that stack. Making it ready then would let
   another thread run it on a stack that is in use. So the task marks
   itself [T_PARKING] before it releases the lock, and the thread that ran
   it marks it [T_PARKED] once the task is off its stack. A waker that
   finds the task [T_PARKING] marks it [T_RUNNING] and leaves it to that
   thread, which makes it ready. A ready task is [T_RUNNING] too. */
enum { T_RUNNING, T_PARKING, T_PARKED };

static _Thread_local struct t_task *t_task_running;
static _Thread_local struct t_context t_thread_context;

/* The task that the calling thread runs, or NULL, and the thread's own
   context. Code that runs after a switch may be on another thread, and
   must read that thread's variables. So these two are not inlined, and
   the empty assembly keeps the compiler from concluding that two calls
   return the same. */
__attribute__((noinline)) static struct t_task *t_task_self(void) {
  __asm__ __volatile__("");
  return t_task_running;
}

__attribute__((noinline)) static struct t_context *t_thread_context_self(void) {
  __asm__ __volatile__("");
  return &t_thread_context;
}

/* The ready queue. */
static pthread_mutex_t t_run_lock = PTHREAD_MUTEX_INITIALIZER;
static struct t_task *t_run_first;
static struct t_task *t_run_last;

static void t_run_push(struct t_task *task) {
  task->next = NULL;
  pthread_mutex_lock(&t_run_lock);
  if (t_run_last != NULL) t_run_last->next = task;
  else t_run_first = task;
  t_run_last = task;
  /* Sequentially consistent, so that of this and a thread that is about
     to sleep, one sees the other. */
  atomic_fetch_add(&t_run_count, 1);
  pthread_mutex_unlock(&t_run_lock);
  /* Every sleeper is woken: one that waits for a branch cannot run the
     task. */
  t_wake(1);
  t_spare_ensure();
}

static struct t_task *t_run_pop(void) {
  if (atomic_load(&t_run_count) == 0) return NULL;
  size_t left = 0;
  pthread_mutex_lock(&t_run_lock);
  struct t_task *task = t_run_first;
  if (task != NULL) {
    t_run_first = task->next;
    if (t_run_first == NULL) t_run_last = NULL;
    left = atomic_fetch_sub(&t_run_count, 1) - 1;
  }
  pthread_mutex_unlock(&t_run_lock);
  /* A thread that was woken for one task passes the wake on while more
     are ready. */
  if (left > 0) t_spare_ensure();
  return task;
}

/* Runs a task on the calling thread, which runs none, until the task
   parks, yields, or ends. */
static void t_task_run(struct t_task *task) {
  t_task_running = task;
  t_coroutine_self = task->coroutine;
  atomic_store(&task->thread, pthread_self());
#ifdef T_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(&fake, task->suspended_stack, task->suspended_stack_size);
#endif
#ifdef T_THREAD_SANITIZER
  task->thread_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(task->suspended_fiber, 0);
#endif
  t_context_switch(&t_thread_context, &task->context);
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &task->suspended_stack, &task->suspended_stack_size);
#endif
  t_task_running = NULL;
  task->coroutine = t_coroutine_self;
  t_coroutine_self = NULL;
  if (task->finished) {
#ifdef T_THREAD_SANITIZER
    __tsan_destroy_fiber(task->fiber);
#endif
    t_stack_release(task->stack);
    free(task);
    return;
  }
  /* A task that yielded, or that was woken before it left its stack, is
     ready. A task that is parked from here on belongs to its waker, which
     may already run it on another thread. */
  int state = T_PARKING;
  if (!atomic_compare_exchange_strong(&task->state, &state, T_PARKED)) t_run_push(task);
}

/* Switches from the calling task to the thread that runs it. Returns when
   the task runs again, on whatever thread that is. */
static void t_task_switch(struct t_task *task) {
#ifdef T_ADDRESS_SANITIZER
  void *fake = NULL;
  __sanitizer_start_switch_fiber(task->finished ? NULL : &fake, task->thread_stack,
                                 task->thread_stack_size);
#endif
#ifdef T_THREAD_SANITIZER
  task->suspended_fiber = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(task->thread_fiber, 0);
#endif
  t_context_switch(&task->context, t_thread_context_self());
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(fake, &task->thread_stack, &task->thread_stack_size);
#endif
}

/* Parks the calling task. The caller holds [lock], and under it has put
   the task where its waker finds it. This releases the lock, and returns
   once the task has been made ready and runs again. */
static void t_task_park(struct t_task *task, pthread_mutex_t *lock) {
  atomic_store(&task->state, T_PARKING);
  pthread_mutex_unlock(lock);
  t_task_switch(task);
}

/* Makes a task that parked ready. The caller took the task from where it
   parked, so no other caller makes it ready. A task that has not left its
   stack yet is made ready by the thread that runs it. */
static void t_task_ready(struct t_task *task) {
  int state = T_PARKING;
  if (atomic_compare_exchange_strong(&task->state, &state, T_RUNNING)) return;
  atomic_store(&task->state, T_RUNNING);
  t_run_push(task);
}

/* Spare threads. A blocked thread runs no task: it is in a call of the
   operating system, or it is not a task and waits for one. For each
   blocked thread, one spare thread may run tasks, so that as many threads
   run tasks as the pool has. A spare thread runs nothing else and never
   exits. It sleeps while no task is ready, and while as many spare
   threads run tasks as threads are blocked. It has a queue of branches,
   as a thread of the pool has, for the [parallel] blocks of its tasks. */
static pthread_mutex_t t_spare_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_spare_wake = PTHREAD_COND_INITIALIZER;
/* Under [t_spare_lock]: the spare threads, the ones that sleep, the ones
   that run tasks, and the calls that no sleeping one has answered yet. A
   thread that is called or started counts as running tasks from then on,
   so that one ready task calls one thread. */
static int t_spares;
static int t_spares_idle;
static int t_spares_busy;
static int t_spares_called;

static void *t_spare_main(void *argument) {
  t_self = argument;
  t_runner_signals();
  t_thread_signal_stack_install();
  for (;;) {
    struct t_task *task = t_run_pop();
    if (task != NULL) t_task_run(task);
    pthread_mutex_lock(&t_spare_lock);
    if (t_spares_busy > atomic_load(&t_blocked) || atomic_load(&t_run_count) == 0) {
      t_spares_busy -= 1;
      t_spares_idle += 1;
      while (t_spares_called == 0) pthread_cond_wait(&t_spare_wake, &t_spare_lock);
      t_spares_called -= 1;
    }
    pthread_mutex_unlock(&t_spare_lock);
  }
  return NULL;
}

static atomic_int t_monitor_asleep = 1;
static void t_monitor_rouse(void);

/* Called when a task has become ready, a thread has blocked, or a thread
   has begun a call that can block. Calls or starts a spare thread if a
   task is ready, no thread of the pool is about to take it, and fewer
   spare threads run tasks than threads are blocked. */
static void t_spare_ensure(void) {
  if (atomic_load(&t_run_count) == 0) return;
  /* While tasks are ready, the monitor counts the threads whose calls
     last. */
  if (atomic_load(&t_monitor_asleep)) t_monitor_rouse();
  if (atomic_load(&t_blocked) == 0 || atomic_load(&t_idle_runners) > 0) return;
  pthread_mutex_lock(&t_spare_lock);
  if (t_spares_busy < atomic_load(&t_blocked)) {
    if (t_spares_idle > 0) {
      t_spares_idle -= 1;
      t_spares_busy += 1;
      t_spares_called += 1;
      pthread_cond_signal(&t_spare_wake);
    } else if (t_spares < T_SPARES) {
      size_t index = atomic_load(&t_worker_count);
      struct t_worker *worker = &t_workers[index];
      worker->random = (uint64_t)index + 1;
      pthread_t thread;
      pthread_attr_t attributes;
      t_thread_attributes(&attributes);
      pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
      if (pthread_create(&thread, &attributes, t_spare_main, worker) == 0) {
        atomic_store(&t_worker_count, index + 1);
        t_spares += 1;
        t_spares_busy += 1;
      } else if (index == 1) {
        /* No thread can run the program's tasks, which would wait forever. */
        t_out_of_memory();
      }
      pthread_attr_destroy(&attributes);
    }
  }
  pthread_mutex_unlock(&t_spare_lock);
}

/* Calls that can block. Most such calls return at once: a read finds
   bytes, a write finds room. A thread that counted as blocked from the
   start of each would call a spare thread for nothing. So a thread only
   records the tick at which its call began, and the monitor, a thread of
   the runtime, counts it as blocked once the call has lasted a whole
   tick. Go's runtime does the same.

   The monitor ticks only while tasks are ready, since only then can a
   blocked thread keep a task waiting. */
#define T_COUNTED UINT_FAST64_MAX

struct t_caller {
  atomic_uint_fast64_t since; /* 0, the tick at which the call began, or T_COUNTED */
  struct t_caller *next;
};

static _Thread_local struct t_caller t_caller_own;
static _Thread_local int t_caller_listed;
static pthread_mutex_t t_monitor_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_monitor_wake = PTHREAD_COND_INITIALIZER;
static pthread_once_t t_monitor_once = PTHREAD_ONCE_INIT;
static struct t_caller *t_callers; /* Every thread that has made such a call, under the lock */
static atomic_uint_fast64_t t_tick = 1;

/* The calling thread's record. Not inlined, as [t_task_self] is not. */
__attribute__((noinline)) static struct t_caller *t_caller_self(void) {
  __asm__ __volatile__("");
  if (!t_caller_listed) {
    t_caller_listed = 1;
    pthread_mutex_lock(&t_monitor_lock);
    t_caller_own.next = t_callers;
    t_callers = &t_caller_own;
    pthread_mutex_unlock(&t_monitor_lock);
  }
  return &t_caller_own;
}

static void *t_monitor_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  pthread_mutex_lock(&t_monitor_lock);
  for (;;) {
    if (atomic_load(&t_run_count) == 0) {
      /* Sequentially consistent, so that of this and a thread that makes
         a task ready, one sees the other. */
      atomic_store(&t_monitor_asleep, 1);
      if (atomic_load(&t_run_count) == 0) pthread_cond_wait(&t_monitor_wake, &t_monitor_lock);
      continue;
    }
    atomic_store(&t_monitor_asleep, 0);
    uint_fast64_t tick = atomic_fetch_add(&t_tick, 1) + 1;
    int counted = 0;
    for (struct t_caller *caller = t_callers; caller != NULL; caller = caller->next) {
      uint_fast64_t since = atomic_load(&caller->since);
      /* A call that began during the tick before this one may have just
         begun. */
      if (since == 0 || since == T_COUNTED || tick - since < 2) continue;
      if (atomic_compare_exchange_strong(&caller->since, &since, T_COUNTED)) {
        atomic_fetch_add(&t_blocked, 1);
        counted = 1;
      }
    }
    pthread_mutex_unlock(&t_monitor_lock);
    if (counted) t_spare_ensure();
    struct timespec tick_length = {0, 1000000};
    nanosleep(&tick_length, NULL);
    pthread_mutex_lock(&t_monitor_lock);
  }
  return NULL;
}

static void t_monitor_start(void) {
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_monitor_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

static void t_monitor_rouse(void) {
  pthread_once(&t_monitor_once, t_monitor_start);
  pthread_mutex_lock(&t_monitor_lock);
  pthread_cond_signal(&t_monitor_wake);
  pthread_mutex_unlock(&t_monitor_lock);
}

/* Around a call of the operating system that can block. Neither changes
   [errno], which the code after the call reads. */
void t_runtime_blocking_begin(void) {
  struct t_task *task = t_task_self();
  if (task != NULL) {
    atomic_store(&task->thread, pthread_self());
    atomic_store(&task->blocking, 1);
  }
  atomic_store(&t_caller_self()->since, atomic_load(&t_tick));
  t_spare_ensure();
}

void t_runtime_blocking_end(void) {
  struct t_task *task = t_task_self();
  if (atomic_exchange(&t_caller_self()->since, 0) == T_COUNTED) atomic_fetch_sub(&t_blocked, 1);
  if (task != NULL) atomic_store(&task->blocking, 0);
}

/* A thread that waits and is not a task cannot park, so it blocks until
   [done] is set. It runs no task meanwhile. A task that ran on top of the
   thread's own computation could block for long, or wait for that
   computation, and would hold it up. */
static pthread_mutex_t t_block_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_block_wake = PTHREAD_COND_INITIALIZER;

static void t_block_until(atomic_int *done) {
  atomic_fetch_add(&t_blocked, 1);
  t_spare_ensure();
  pthread_mutex_lock(&t_block_lock);
  while (!atomic_load(done)) pthread_cond_wait(&t_block_wake, &t_block_lock);
  pthread_mutex_unlock(&t_block_lock);
  atomic_fetch_sub(&t_blocked, 1);
}

/* Sets [done] and wakes the thread that blocks until it is set. The frame
   that holds [done] may be gone as soon as it is set. */
static void t_unblock(atomic_int *done) {
  atomic_store(done, 1);
  pthread_mutex_lock(&t_block_lock);
  pthread_cond_broadcast(&t_block_wake);
  pthread_mutex_unlock(&t_block_lock);
}

/* Interrupting a blocked task. A cancelled task that is blocked in a call
   of the operating system, such as a read or a sleep, has to return from
   it. The runtime sends SIGURG to the thread that runs the task. The
   handler does nothing and is installed without SA_RESTART, so the call
   fails with EINTR, and the standard library returns its cancelled
   error. Nothing else in a program uses SIGURG.

   A task can start a blocking call just after an interrupt and miss it.
   So a thread of the runtime interrupts the tasks of every cancelled
   group again every few milliseconds, until the group is joined. */
static void t_interrupt_handler(int signal) { (void)signal; }

static pthread_mutex_t t_interrupter_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_interrupter_wake = PTHREAD_COND_INITIALIZER;
static struct t_group *t_interrupter_groups;
static pthread_once_t t_interrupt_once = PTHREAD_ONCE_INIT;

/* Interrupts the group's tasks that are blocked, and those of the groups
   that its tasks opened. The caller holds the group's lock. */
static void t_group_interrupt(struct t_group *group) {
  for (struct t_task *task = group->tasks; task != NULL; task = task->sibling)
    if (atomic_load(&task->blocking)) pthread_kill(atomic_load(&task->thread), SIGURG);
  for (struct t_group *child = group->children; child != NULL; child = child->next) {
    pthread_mutex_lock(&child->lock);
    t_group_interrupt(child);
    pthread_mutex_unlock(&child->lock);
  }
}

static void *t_interrupter_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  for (;;) {
    pthread_mutex_lock(&t_interrupter_lock);
    while (t_interrupter_groups == NULL)
      pthread_cond_wait(&t_interrupter_wake, &t_interrupter_lock);
    for (struct t_group *group = t_interrupter_groups; group != NULL; group = group->interrupted) {
      pthread_mutex_lock(&group->lock);
      t_group_interrupt(group);
      pthread_mutex_unlock(&group->lock);
    }
    pthread_mutex_unlock(&t_interrupter_lock);
    struct timespec pause = {0, 5000000};
    nanosleep(&pause, NULL);
  }
  return NULL;
}

static void t_interrupt_start(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = t_interrupt_handler;
  sigemptyset(&action.sa_mask);
  sigaction(SIGURG, &action, NULL);
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_interrupter_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

/* Waiting on a key. A key hashes to a slot, which counts the wakes of its
   keys and holds their waiters. [watch] reads the count as a ticket,
   [wait] parks the caller if the count still equals the ticket, and
   [wake] increments the count and makes the waiters of the key ready.
   Two keys can share a slot, so a wake of one key can make a [wait] on
   the other return at once, and its caller tests its condition again. */
#define T_WAIT_SLOTS 1024

/* A thread that is not a task, waiting on a key. */
struct t_thread_waiter {
  uint64_t key;
  atomic_int woken;
  struct t_thread_waiter *next;
};

struct t_wait_slot {
  pthread_mutex_t lock;
  atomic_uint_fast64_t wakes; /* Changed under [lock], and read without it */
  struct t_task *parked;
  struct t_thread_waiter *threads;
};

static struct t_wait_slot t_wait_slots[T_WAIT_SLOTS];
static pthread_once_t t_wait_slots_once = PTHREAD_ONCE_INIT;

static void t_wait_slots_start(void) {
  for (int index = 0; index < T_WAIT_SLOTS; index++) pthread_mutex_init(&t_wait_slots[index].lock, NULL);
}

static struct t_wait_slot *t_wait_slot(uint64_t key) {
  pthread_once(&t_wait_slots_once, t_wait_slots_start);
  return &t_wait_slots[(key * 0x9E3779B97F4A7C15ULL) >> 54];
}

int32_t t_runtime_tasks_cancelled(void) {
  struct t_task *task = t_task_self();
  for (struct t_group *group = task == NULL ? NULL : task->group; group != NULL; group = group->parent)
    if (atomic_load(&group->cancelled)) return 1;
  return 0;
}

/* A caller makes its condition true before it wakes a key, and tests the
   condition after it takes a ticket. So a ticket that already counts a
   wake belongs to a caller that sees the condition. */
uint64_t t_runtime_tasks_watch(uint64_t key) { return atomic_load(&t_wait_slot(key)->wakes); }

/* Waits until [key] is woken, unless its slot has been woken since
   [ticket] was issued. A cancellable wait does not start in a cancelled
   task, and a cancel makes the tasks of its group that are parked in one
   ready. */
static void t_wait(uint64_t key, uint64_t ticket, int cancellable) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task *task = t_task_self();
  pthread_mutex_lock(&slot->lock);
  /* The task says where it parks before it reads whether it is cancelled,
     and a cancel sets its flag before it looks for parked tasks. So the
     task sees the flag, or the cancel finds the task. */
  if (task != NULL && cancellable) atomic_store(&task->cancellable, slot);
  if (atomic_load(&slot->wakes) != ticket || (cancellable && t_runtime_tasks_cancelled())) {
    pthread_mutex_unlock(&slot->lock);
  } else if (task != NULL) {
    task->wait_key = key;
    task->next = slot->parked;
    slot->parked = task;
    t_task_park(task, &slot->lock);
  } else {
    struct t_thread_waiter waiter;
    waiter.key = key;
    atomic_init(&waiter.woken, 0);
    waiter.next = slot->threads;
    slot->threads = &waiter;
    pthread_mutex_unlock(&slot->lock);
    t_block_until(&waiter.woken);
  }
  if (task != NULL && cancellable) atomic_store(&task->cancellable, NULL);
}

int32_t t_runtime_tasks_wait(uint64_t key, uint64_t ticket) {
  t_wait(key, ticket, 1);
  return 0;
}

int32_t t_runtime_tasks_wake(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task *tasks = NULL;
  struct t_thread_waiter *threads = NULL;
  pthread_mutex_lock(&slot->lock);
  atomic_fetch_add(&slot->wakes, 1);
  for (struct t_task **link = &slot->parked; *link != NULL;) {
    struct t_task *task = *link;
    if (task->wait_key != key) {
      link = &task->next;
      continue;
    }
    *link = task->next;
    task->next = tasks;
    tasks = task;
  }
  for (struct t_thread_waiter **link = &slot->threads; *link != NULL;) {
    struct t_thread_waiter *waiter = *link;
    if (waiter->key != key) {
      link = &waiter->next;
      continue;
    }
    *link = waiter->next;
    waiter->next = threads;
    threads = waiter;
  }
  pthread_mutex_unlock(&slot->lock);
  while (tasks != NULL) {
    struct t_task *task = tasks;
    tasks = task->next;
    t_task_ready(task);
  }
  while (threads != NULL) {
    struct t_thread_waiter *waiter = threads;
    threads = waiter->next;
    t_unblock(&waiter->woken);
  }
  return 0;
}

/* Makes the group's tasks that are parked in a cancellable wait ready,
   and those of the groups that its tasks opened. The caller holds the
   group's lock. */
static void t_group_wake(struct t_group *group) {
  for (struct t_task *task = group->tasks; task != NULL; task = task->sibling) {
    struct t_wait_slot *slot = atomic_load(&task->cancellable);
    if (slot == NULL) continue;
    pthread_mutex_lock(&slot->lock);
    struct t_task **link = &slot->parked;
    while (*link != NULL && *link != task) link = &(*link)->next;
    int parked = *link == task;
    if (parked) *link = task->next;
    pthread_mutex_unlock(&slot->lock);
    if (parked) t_task_ready(task);
  }
  for (struct t_group *child = group->children; child != NULL; child = child->next) {
    pthread_mutex_lock(&child->lock);
    t_group_wake(child);
    pthread_mutex_unlock(&child->lock);
  }
}

/* Timers. A wait with a time limit has a timer, which is in a heap that
   is ordered by deadline until the timer fires or its wait ends. A thread
   of the runtime sleeps until the earliest deadline, then marks that
   timer fired and wakes its key. A timer is in the frame of its wait. */
struct t_timer {
  uint64_t deadline; /* On the monotonic clock, in nanoseconds */
  uint64_t key;
  size_t index;      /* In the heap, until it fires */
  int fired;
};

static pthread_mutex_t t_timer_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_timer_wake;
static pthread_once_t t_timer_once = PTHREAD_ONCE_INIT;
static struct t_timer **t_timers;
static size_t t_timer_count;
static size_t t_timer_room;

static uint64_t t_monotonic(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000000u + (uint64_t)now.tv_nsec;
}

static void t_timer_place(struct t_timer *timer, size_t index) {
  t_timers[index] = timer;
  timer->index = index;
}

/* Moves the timer at [index] up or down to where the heap is ordered. */
static void t_timer_settle(size_t index) {
  struct t_timer *timer = t_timers[index];
  while (index > 0) {
    size_t parent = (index - 1) / 2;
    if (t_timers[parent]->deadline <= timer->deadline) break;
    t_timer_place(t_timers[parent], index);
    index = parent;
  }
  for (;;) {
    size_t child = 2 * index + 1;
    if (child >= t_timer_count) break;
    if (child + 1 < t_timer_count && t_timers[child + 1]->deadline < t_timers[child]->deadline)
      child += 1;
    if (timer->deadline <= t_timers[child]->deadline) break;
    t_timer_place(t_timers[child], index);
    index = child;
  }
  t_timer_place(timer, index);
}

/* Takes a timer out of the heap. The caller holds [t_timer_lock]. */
static void t_timer_remove(struct t_timer *timer) {
  size_t index = timer->index;
  t_timer_count -= 1;
  if (index == t_timer_count) return;
  t_timer_place(t_timers[t_timer_count], index);
  t_timer_settle(index);
}

static void *t_timer_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  pthread_mutex_lock(&t_timer_lock);
  for (;;) {
    if (t_timer_count == 0) {
      pthread_cond_wait(&t_timer_wake, &t_timer_lock);
      continue;
    }
    struct t_timer *first = t_timers[0];
    uint64_t now = t_monotonic();
    if (first->deadline > now) {
#ifdef __APPLE__
      uint64_t left = first->deadline - now;
      struct timespec duration = {(time_t)(left / 1000000000u), (long)(left % 1000000000u)};
      pthread_cond_timedwait_relative_np(&t_timer_wake, &t_timer_lock, &duration);
#else
      struct timespec deadline = {(time_t)(first->deadline / 1000000000u),
                                  (long)(first->deadline % 1000000000u)};
      pthread_cond_timedwait(&t_timer_wake, &t_timer_lock, &deadline);
#endif
      continue;
    }
    t_timer_remove(first);
    first->fired = 1;
    uint64_t key = first->key;
    /* The timer's frame may be gone as soon as the lock is released. */
    pthread_mutex_unlock(&t_timer_lock);
    t_runtime_tasks_wake(key);
    pthread_mutex_lock(&t_timer_lock);
  }
  return NULL;
}

static void t_timer_start(void) {
#ifdef __APPLE__
  pthread_cond_init(&t_timer_wake, NULL);
#else
  /* The deadline of a timed wait is on the monotonic clock. */
  pthread_condattr_t clock;
  pthread_condattr_init(&clock);
  pthread_condattr_setclock(&clock, CLOCK_MONOTONIC);
  pthread_cond_init(&t_timer_wake, &clock);
  pthread_condattr_destroy(&clock);
#endif
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_timer_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

/* Starts a timer that fires after [nanoseconds] and then wakes [key]. */
static void t_timer_begin(struct t_timer *timer, uint64_t nanoseconds, uint64_t key) {
  pthread_once(&t_timer_once, t_timer_start);
  uint64_t now = t_monotonic();
  uint64_t latest = (uint64_t)INT64_MAX;
  timer->deadline = nanoseconds > latest - now ? latest : now + nanoseconds;
  timer->key = key;
  timer->fired = 0;
  pthread_mutex_lock(&t_timer_lock);
  if (t_timer_count == t_timer_room) {
    t_timer_room = t_timer_room == 0 ? 64 : t_timer_room * 2;
    t_timers = realloc(t_timers, t_timer_room * sizeof *t_timers);
    if (t_timers == NULL) t_out_of_memory();
  }
  t_timer_count += 1;
  t_timer_place(timer, t_timer_count - 1);
  t_timer_settle(t_timer_count - 1);
  if (timer->index == 0) pthread_cond_signal(&t_timer_wake);
  pthread_mutex_unlock(&t_timer_lock);
}

static int t_timer_fired(struct t_timer *timer) {
  pthread_mutex_lock(&t_timer_lock);
  int fired = timer->fired;
  pthread_mutex_unlock(&t_timer_lock);
  return fired;
}

/* Ends a timer before its frame goes. Returns whether it fired. */
static int t_timer_end(struct t_timer *timer) {
  pthread_mutex_lock(&t_timer_lock);
  int fired = timer->fired;
  if (!fired) t_timer_remove(timer);
  pthread_mutex_unlock(&t_timer_lock);
  return fired;
}

/* Waits for the time. Returns 0 afterwards, or 1 as soon as the calling
   task is cancelled. */
int32_t t_runtime_sleep(int64_t seconds, int64_t nanoseconds) {
  uint64_t duration = seconds <= 0 ? 0 : (uint64_t)seconds;
  duration = duration > UINT64_MAX / 1000000000u ? UINT64_MAX : duration * 1000000000u;
  uint64_t rest = nanoseconds <= 0 ? 0 : (uint64_t)nanoseconds;
  duration = duration > UINT64_MAX - rest ? UINT64_MAX : duration + rest;
  if (duration == 0) return 0;
  struct t_timer timer;
  uint64_t key = (uint64_t)(uintptr_t)&timer;
  t_timer_begin(&timer, duration, key);
  for (;;) {
    uint64_t ticket = t_runtime_tasks_watch(key);
    if (t_timer_fired(&timer)) return 0;
    if (t_runtime_tasks_cancelled()) return !t_timer_end(&timer);
    t_wait(key, ticket, 1);
  }
}

/* Waiting for a descriptor. A socket or a pipe that tasks wait for does
   not block:
   a call that would block fails with EAGAIN, and the task then waits
   here. The descriptor is registered with the system's poller (epoll on
   Linux, kqueue elsewhere) at its first wait, for both directions, and
   the system then reports each time the descriptor becomes readable or
   writable. A thread of the runtime takes those reports and wakes the
   key of the descriptor and direction.

   The caller takes a ticket before its system call and waits on it after
   EAGAIN, so a report between the two is not lost.

   A caller that waits for any of several descriptors registers each one
   with a key of its own instead, which a report that the descriptor is
   readable wakes. So one wait covers them all. */
#define T_DESCRIPTORS 65536

/* Whose key the reports of a registered descriptor wake. */
#define T_OWN_KEY 1
#define T_CALLERS_KEY 2

static atomic_uchar t_descriptor_registered[T_DESCRIPTORS];
static int t_poller = -1;
static pthread_once_t t_poller_once = PTHREAD_ONCE_INIT;

/* No address has the highest bit, so no mutex or timer has this key. */
static uint64_t t_descriptor_key(int32_t descriptor, int32_t writing) {
  return (uint64_t)1 << 63 | (uint64_t)(uint32_t)descriptor << 1 | (uint64_t)(writing != 0);
}

static void *t_poller_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  for (;;) {
#ifdef __linux__
    struct epoll_event events[64];
    int count = epoll_wait(t_poller, events, 64, -1);
    for (int index = 0; index < count; index++) {
      /* The key that the descriptor was registered with: its own for
         reading, which has the highest bit, or a caller's. */
      uint64_t key = events[index].data.u64;
      uint32_t found = events[index].events;
      /* An error or a hang-up ends the wait in both directions. */
      if (found & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) t_runtime_tasks_wake(key);
      if ((key >> 63) && (found & (EPOLLOUT | EPOLLHUP | EPOLLERR))) t_runtime_tasks_wake(key | 1);
    }
#else
    struct kevent events[64];
    int count = kevent(t_poller, NULL, 0, events, 64, NULL);
    for (int index = 0; index < count; index++) {
      /* The key that the descriptor was registered with, or 0 for its own. */
      uint64_t key = (uint64_t)(uintptr_t)events[index].udata;
      int writing = events[index].filter == EVFILT_WRITE;
      if (key == 0)
        t_runtime_tasks_wake(t_descriptor_key((int32_t)events[index].ident, writing));
      else if (!writing)
        t_runtime_tasks_wake(key);
    }
#endif
  }
  return NULL;
}

static void t_poller_start(void) {
#ifdef __linux__
  t_poller = epoll_create1(EPOLL_CLOEXEC);
#else
  t_poller = kqueue();
  if (t_poller >= 0) fcntl(t_poller, F_SETFD, FD_CLOEXEC);
#endif
  if (t_poller < 0) t_out_of_memory();
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_poller_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

/* Registers the descriptor with the poller, which reports at once if the
   descriptor is ready now. Its reports wake [key], or the key of the
   descriptor and direction where [key] is 0. A descriptor that is
   registered with one is registered again to change to the other, and a
   caller's key is registered each time, since the descriptor's last
   caller may have been another. Returns 0 if the system cannot report on
   the descriptor, as for a file. */
static int t_descriptor_register(int32_t descriptor, uint64_t key) {
  int known = descriptor >= 0 && descriptor < T_DESCRIPTORS;
  if (key == 0 && known && atomic_load(&t_descriptor_registered[descriptor]) == T_OWN_KEY) return 1;
  pthread_once(&t_poller_once, t_poller_start);
#ifdef __linux__
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN | EPOLLOUT | EPOLLRDHUP | EPOLLET;
  event.data.u64 = key == 0 ? t_descriptor_key(descriptor, 0) : key;
  if (epoll_ctl(t_poller, EPOLL_CTL_ADD, descriptor, &event) != 0
      && (*t_runtime_errno() != EEXIST || epoll_ctl(t_poller, EPOLL_CTL_MOD, descriptor, &event) != 0))
    return 0;
#else
  struct kevent changes[2];
  void *reported = (void *)(uintptr_t)key;
  EV_SET(&changes[0], descriptor, EVFILT_READ, EV_ADD | EV_CLEAR, 0, 0, reported);
  EV_SET(&changes[1], descriptor, EVFILT_WRITE, EV_ADD | EV_CLEAR, 0, 0, reported);
  if (kevent(t_poller, changes, 2, NULL, 0, NULL) != 0) return 0;
#endif
  if (known) atomic_store(&t_descriptor_registered[descriptor], key == 0 ? T_OWN_KEY : T_CALLERS_KEY);
  return 1;
}

uint64_t t_runtime_descriptor_watch(int32_t descriptor, int32_t writing) {
  return t_runtime_tasks_watch(t_descriptor_key(descriptor, writing));
}

/* Waits until the descriptor has become readable, or writable, since
   [ticket] was issued. Returns 1 when the caller is to make its system
   call again. Returns 0 when it is not, with [errno] set to say why:
   EINTR if the calling task is cancelled, and EAGAIN if the socket's time
   limit passed. */
int32_t t_runtime_descriptor_wait(int32_t descriptor, int32_t writing, uint64_t ticket) {
  int32_t ready = 1;
  if (!t_descriptor_register(descriptor, 0)) {
    t_runtime_blocking_begin();
    ready = t_descriptor_poll(descriptor, writing);
    t_runtime_blocking_end();
  } else {
    uint64_t key = t_descriptor_key(descriptor, writing);
    uint64_t limit = t_descriptor_limit(descriptor, writing);
    if (limit == 0) {
      t_wait(key, ticket, 1);
    } else {
      struct t_timer timer;
      t_timer_begin(&timer, limit, key);
      t_wait(key, ticket, 1);
      ready = !t_timer_end(&timer);
    }
  }
  if (t_runtime_tasks_cancelled()) {
    *t_runtime_errno() = EINTR;
    return 0;
  }
  if (!ready) *t_runtime_errno() = EAGAIN;
  return ready;
}

/* The key that the calling task or thread waits on for any of several
   descriptors. It is an address, so it has no highest bit, and it is the
   key of nothing else. */
static uint64_t t_descriptors_key(void) {
  struct t_task *task = t_task_self();
  return (uint64_t)(uintptr_t)(task != NULL ? (void *)&task->wait_key : (void *)t_thread_context_self());
}

uint64_t t_runtime_descriptors_watch(void) { return t_runtime_tasks_watch(t_descriptors_key()); }

/* Waits until one of the descriptors has become readable since [ticket]
   was issued. A negative descriptor is skipped. Returns 1 when the caller
   is to read again, and 0 with [errno] set to EINTR if the calling task
   is cancelled. */
int32_t t_runtime_descriptors_wait(const int32_t *descriptors, size_t count, uint64_t ticket) {
  uint64_t key = t_descriptors_key();
  int registered = 1;
  for (size_t index = 0; index < count && registered; index++)
    if (descriptors[index] >= 0) registered = t_descriptor_register(descriptors[index], key);
  if (registered) {
    t_wait(key, ticket, 1);
  } else {
    t_runtime_blocking_begin();
    t_descriptors_poll(descriptors, count);
    t_runtime_blocking_end();
  }
  if (t_runtime_tasks_cancelled()) {
    *t_runtime_errno() = EINTR;
    return 0;
  }
  return 1;
}

/* The system forgets a descriptor that is closed, and gives its number to
   the next one that is opened, so the runtime forgets it too. */
int32_t t_runtime_close(int32_t descriptor) {
  if (descriptor >= 0 && descriptor < T_DESCRIPTORS)
    atomic_store(&t_descriptor_registered[descriptor], 0);
  return close(descriptor);
}

uint64_t t_runtime_tasks_open(void) {
  struct t_group *group = malloc(sizeof *group);
  if (group == NULL) t_out_of_memory();
  pthread_mutex_init(&group->lock, NULL);
  group->running = 0;
  atomic_init(&group->cancelled, 0);
  struct t_task *task = t_task_self();
  group->parent = task == NULL ? NULL : task->group;
  group->tasks = NULL;
  group->children = NULL;
  group->next = NULL;
  group->joiner = NULL;
  group->joined = NULL;
  group->interrupted = NULL;
  if (group->parent != NULL) {
    pthread_mutex_lock(&group->parent->lock);
    group->next = group->parent->children;
    group->parent->children = group;
    pthread_mutex_unlock(&group->parent->lock);
  }
  return (uint64_t)(uintptr_t)group;
}

/* Where a task starts, on its own stack. It never returns: when its
   function returns, it leaves its group and switches to the thread for
   the last time. */
static void t_task_entry(void) {
  struct t_task *task = t_task_self();
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(NULL, &task->thread_stack, &task->thread_stack_size);
#endif
  task->code(task->environment, task->item);
  struct t_group *group = task->group;
  struct t_task *joiner = NULL;
  atomic_int *joined = NULL;
  pthread_mutex_lock(&group->lock);
  for (struct t_task **link = &group->tasks; *link != NULL; link = &(*link)->sibling)
    if (*link == task) {
      *link = task->sibling;
      break;
    }
  group->running -= 1;
  if (group->running == 0) {
    joiner = group->joiner;
    joined = group->joined;
    group->joiner = NULL;
    group->joined = NULL;
  }
  /* The group may be freed as soon as its lock is released. */
  pthread_mutex_unlock(&group->lock);
  if (joiner != NULL) t_task_ready(joiner);
  if (joined != NULL) t_unblock(joined);
  task->finished = 1;
  t_task_switch(task);
  t_runtime_compiler_bug();
}

uint8_t t_runtime_tasks_spawn(uint64_t handle, void (*code)(void *environment, uint64_t item),
                              void *environment, uint64_t item) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  if (atomic_load_explicit(&group->cancelled, memory_order_acquire)) return 0;
  pthread_once(&t_pool_once, t_pool_start);
  pthread_once(&t_interrupt_once, t_interrupt_start);
  struct t_task *task = malloc(sizeof *task);
  if (task == NULL) t_out_of_memory();
  task->stack = t_stack_acquire();
  t_context_start(&task->context, task->stack, t_stack_bytes, t_task_entry);
  task->group = group;
  task->code = code;
  task->environment = environment;
  task->item = item;
  task->next = NULL;
  atomic_init(&task->blocking, 0);
  atomic_init(&task->state, T_RUNNING);
  atomic_init(&task->cancellable, NULL);
  task->finished = 0;
  task->coroutine = NULL;
#ifdef T_ADDRESS_SANITIZER
  task->suspended_stack = task->stack;
  task->suspended_stack_size = t_stack_bytes;
#endif
#ifdef T_THREAD_SANITIZER
  task->fiber = __tsan_create_fiber(0);
  task->suspended_fiber = task->fiber;
#endif
  pthread_mutex_lock(&group->lock);
  group->running += 1;
  task->sibling = group->tasks;
  group->tasks = task;
  pthread_mutex_unlock(&group->lock);
  t_run_push(task);
  return 1;
}

/* Waits until every task of the group has ended, then frees the group. A
   task parks. A thread that is not a task blocks. */
int32_t t_runtime_tasks_join(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  pthread_mutex_lock(&group->lock);
  while (group->running > 0) {
    struct t_task *task = t_task_self();
    if (task != NULL) {
      group->joiner = task;
      t_task_park(task, &group->lock);
    } else {
      atomic_int joined;
      atomic_init(&joined, 0);
      group->joined = &joined;
      pthread_mutex_unlock(&group->lock);
      t_block_until(&joined);
    }
    pthread_mutex_lock(&group->lock);
  }
  pthread_mutex_unlock(&group->lock);
  if (atomic_load(&group->cancelled)) {
    pthread_mutex_lock(&t_interrupter_lock);
    for (struct t_group **link = &t_interrupter_groups; *link != NULL; link = &(*link)->interrupted)
      if (*link == group) {
        *link = group->interrupted;
        break;
      }
    pthread_mutex_unlock(&t_interrupter_lock);
  }
  if (group->parent != NULL) {
    pthread_mutex_lock(&group->parent->lock);
    for (struct t_group **link = &group->parent->children; *link != NULL; link = &(*link)->next)
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

/* Cancels the group. Returns 1 to the first caller. The group's tasks
   that are parked in a cancellable wait are made ready, so that each
   returns from its wait. The group's tasks that are blocked in the
   operating system are interrupted, now and again until the group is
   joined. */
int32_t t_runtime_tasks_cancel(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  int cancelled = 0;
  if (!atomic_compare_exchange_strong(&group->cancelled, &cancelled, 1)) return 0;
  pthread_mutex_lock(&group->lock);
  t_group_wake(group);
  pthread_mutex_unlock(&group->lock);
  pthread_once(&t_interrupt_once, t_interrupt_start);
  pthread_mutex_lock(&t_interrupter_lock);
  group->interrupted = t_interrupter_groups;
  t_interrupter_groups = group;
  pthread_cond_signal(&t_interrupter_wake);
  pthread_mutex_unlock(&t_interrupter_lock);
  return 1;
}

/* Makes one waiter of [key] ready: a thread if one waits, and otherwise
   the task that has waited longest. A caller that has taken a ticket and
   has not parked yet returns from its wait at once, since the count has
   changed. */
static void t_wake_one(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task **task = NULL;
  struct t_thread_waiter **thread = NULL;
  pthread_mutex_lock(&slot->lock);
  atomic_fetch_add(&slot->wakes, 1);
  /* A waiter is put at the front of its list, so the last one with the
     key has waited longest. A program has few threads that are not tasks,
     so taking a thread first keeps no task waiting for long, and taking a
     task first could keep a thread waiting for ever. */
  for (struct t_thread_waiter **link = &slot->threads; *link != NULL; link = &(*link)->next)
    if ((*link)->key == key) thread = link;
  if (thread == NULL)
    for (struct t_task **link = &slot->parked; *link != NULL; link = &(*link)->next)
      if ((*link)->wait_key == key) task = link;
  struct t_thread_waiter *woken_thread = NULL;
  struct t_task *woken_task = NULL;
  if (thread != NULL) {
    woken_thread = *thread;
    *thread = woken_thread->next;
  } else if (task != NULL) {
    woken_task = *task;
    *task = woken_task->next;
  }
  pthread_mutex_unlock(&slot->lock);
  if (woken_thread != NULL) t_unblock(&woken_thread->woken);
  if (woken_task != NULL) t_task_ready(woken_task);
}

/* A mutex is a [uint64_t] that its owner initialized to zero: 0 is
   unlocked, 1 is locked, and 2 is locked while a caller may wait for it.
   These are the states of Drepper's "Futexes Are Tricky". A caller that
   finds the mutex locked sets it to 2 and waits on its address as a key,
   and an unlock that finds 2 wakes one waiter. A caller that takes the
   mutex after it has waited takes it as 2, since it cannot tell whether
   another caller still waits. So a lock and an unlock that no other
   caller contends are one atomic operation each.

   The wait is not cancellable: a cancelled task still waits for the
   mutex, since the call it made has no other result to return. */
int32_t t_runtime_tasks_lock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  uint64_t unlocked = 0;
  if (__atomic_compare_exchange_n(word, &unlocked, 1, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
    return 0;
  for (;;) {
    uint64_t ticket = t_runtime_tasks_watch(mutex);
    if (__atomic_exchange_n(word, 2, __ATOMIC_SEQ_CST) == 0) return 0;
    t_wait(mutex, ticket, 0);
  }
}

int32_t t_runtime_tasks_unlock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  if (__atomic_exchange_n(word, 0, __ATOMIC_SEQ_CST) == 2) t_wake_one(mutex);
  return 0;
}

/* A task goes to the end of the ready queue. */
int32_t t_runtime_tasks_yield(void) {
  struct t_task *task = t_task_self();
  if (task != NULL) t_task_switch(task);
  else sched_yield();
  return 0;
}

/* Waiting for signals. Any thread can wait, so the signals cannot be
   blocked and taken with [sigwait], which needs them blocked in every
   thread. A handler records each signal in [t_signals_pending] and writes
   a byte to a pipe. A thread of the runtime reads the pipe and wakes the
   waiters, since a handler may not use a condition variable. That thread
   also unblocks every handled signal, so that a signal which the program
   was started with blocked is delivered to it. A waiter takes a pending
   signal that it waits for, or blocks until the next wake. A signal that
   no waiter takes stays pending for a later one. */
static atomic_uint_fast64_t t_signals_pending;
static uint64_t t_signals_handled;
static pthread_mutex_t t_signals_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t t_signals_once = PTHREAD_ONCE_INIT;
static int t_signals_pipe[2];

static void t_signals_handler(int signal) {
  int saved = errno;
  atomic_fetch_or(&t_signals_pending, (uint_fast64_t)1 << signal);
  ssize_t written = write(t_signals_pipe[1], "", 1);
  (void)written;
  errno = saved;
}

static void *t_signals_main(void *argument) {
  (void)argument;
  sigset_t all;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  for (;;) {
    char byte;
    if (read(t_signals_pipe[0], &byte, 1) != 1) continue;
    sigset_t handled;
    sigemptyset(&handled);
    pthread_mutex_lock(&t_signals_lock);
    for (int signal = 1; signal < 64; signal++)
      if (t_signals_handled & ((uint64_t)1 << signal)) sigaddset(&handled, signal);
    pthread_mutex_unlock(&t_signals_lock);
    pthread_sigmask(SIG_UNBLOCK, &handled, NULL);
    t_runtime_tasks_wake((uint64_t)(uintptr_t)&t_signals_pending);
  }
  return NULL;
}

static void t_signals_start(void) {
  if (pipe(t_signals_pipe) != 0) t_out_of_memory();
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_signals_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

/* Blocks until one of the signals arrives, and returns its number. Returns
   0 if the calling task is cancelled first. */
int32_t t_runtime_signals_wait(const int32_t *signals, size_t count) {
  pthread_once(&t_signals_once, t_signals_start);
  uint_fast64_t wanted = 0;
  int added = 0;
  pthread_mutex_lock(&t_signals_lock);
  for (size_t index = 0; index < count; index++) {
    int32_t signal = signals[index];
    if (signal <= 0 || signal >= 64) continue;
    uint64_t bit = (uint64_t)1 << signal;
    wanted |= bit;
    if (!(t_signals_handled & bit)) {
      struct sigaction action;
      memset(&action, 0, sizeof action);
      action.sa_handler = t_signals_handler;
      sigfillset(&action.sa_mask);
      action.sa_flags = SA_RESTART;
      if (sigaction(signal, &action, NULL) == 0) {
        t_signals_handled |= bit;
        added = 1;
      }
    }
  }
  pthread_mutex_unlock(&t_signals_lock);
  if (added) {
    ssize_t written = write(t_signals_pipe[1], "", 1);
    (void)written;
  }
  uint64_t key = (uint64_t)(uintptr_t)&t_signals_pending;
  for (;;) {
    uint64_t ticket = t_runtime_tasks_watch(key);
    /* A signal that was sent while every thread blocked it has run no
       handler: one that the program was started with blocked, and that
       arrived before the first wait for it. It is pending, and the
       calling thread takes it if it can see it. On macOS only the thread
       it is pending for can take it. On Linux any thread can, so the
       take must not block: the runtime's thread may have taken it. */
    sigset_t blocked;
    if (sigpending(&blocked) == 0)
      for (size_t index = 0; index < count; index++) {
        int32_t signal = signals[index];
        if (signal <= 0 || signal >= 64 || sigismember(&blocked, signal) != 1) continue;
        sigset_t one;
        sigemptyset(&one);
        sigaddset(&one, signal);
#ifdef __linux__
        struct timespec none = {0, 0};
        if (sigtimedwait(&one, NULL, &none) == signal) return signal;
#else
        int arrived = 0;
        if (sigwait(&one, &arrived) == 0) return arrived;
#endif
      }
    uint_fast64_t pending = atomic_load(&t_signals_pending);
    while (pending & wanted) {
      uint_fast64_t arrived = pending & wanted;
      uint_fast64_t lowest = arrived & (~arrived + 1);
      if (atomic_compare_exchange_weak(&t_signals_pending, &pending, pending & ~lowest))
        return (int32_t)__builtin_ctzll(lowest);
    }
    if (t_runtime_tasks_cancelled()) return 0;
    t_wait(key, ticket, 1);
  }
}

#endif
|}

let resolving =
  {|
/* A host's addresses, for the standard library, which cannot follow the
   chain of structures [getaddrinfo] gives. Each address is written as a
   byte that is 4 or 6 and then its 4 or 16 bytes, as many as there is room
   for. The result is how many bytes were written, -1 where the system knows
   no such host, and -2 where it could not find out. */
long t_runtime_addresses_of_host(const char *host, void *room, size_t size) {
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
/* The tests of a test program, which its [main] gives before it calls the
   runner. */
typedef void (*t_test)(void);
const t_test *t_runtime_tests;

void t_runtime_run_test(uint32_t index) { t_runtime_tests[index](); }
|}

let runtime (target : Memory_layout.target) ~tests ~in_order =
  String.concat ""
    [
      (if tests then "#define T_TESTS 1\n" else "");
      (if in_order then "#define T_IN_ORDER 1\n" else "");
      headers;
      (if target.usize_bytes = 8 then "typedef uint64_t t_usize;\ntypedef int64_t t_isize;\n"
       else "typedef uint32_t t_usize;\ntypedef int32_t t_isize;\n");
      Emit_c.anchor_struct;
      failing;
      allocation;
      threads;
      resolving;
      (if tests then tests_table else "");
    ]

let main_calling entry =
  Printf.sprintf
    "typedef __INT32_TYPE__ int32_t;\n\
     void t_runtime_install(void);\n\
     int32_t %s(void);\n\
     int main(int count, char **arguments) {\n\
    \  (void)count;\n\
    \  (void)arguments;\n\
    \  t_runtime_install();\n\
    \  return (int)%s();\n\
     }\n"
    entry entry

let tests_calling ~time_limit ~runner tests =
  let declarations =
    String.concat "" (List.map (fun symbol -> Printf.sprintf "void %s(void);\n" symbol) tests)
  in
  let table = String.concat ", " tests in
  Printf.sprintf
    "typedef __UINT32_TYPE__ uint32_t;\n\
     typedef __INT32_TYPE__ int32_t;\n\
     void t_runtime_install(void);\n\
     typedef void (*t_test)(void);\n\
     extern const t_test *t_runtime_tests;\n\
     int32_t %s(uint32_t count, uint32_t time_limit);\n\
     %sstatic const t_test t_tests[] = { %s };\n\
     int main(int count, char **arguments) {\n\
    \  (void)count;\n\
    \  (void)arguments;\n\
    \  t_runtime_install();\n\
    \  t_runtime_tests = t_tests;\n\
    \  return (int)%s(%d, %d);\n\
     }\n"
    runner declarations
    (if tests = [] then "0" else table)
    runner (List.length tests) time_limit

(* The startup of code run while compiling: it runs the evaluator, which
   writes its result. *)
let evaluator_calling entry =
  Printf.sprintf
    "void t_runtime_install(void);\n\
     void %s(void);\n\
     int main(void) {\n\
    \  t_runtime_install();\n\
    \  %s();\n\
    \  return 0;\n\
     }\n"
    entry entry

let program_calling entry =
  Printf.sprintf
    "typedef __INT32_TYPE__ int32_t;\n\
     void t_runtime_install(void);\n\
     int32_t %s(int32_t count, void *arguments);\n\
     int main(int count, char **arguments) {\n\
    \  t_runtime_install();\n\
    \  return (int)%s((int32_t)count, (void *)arguments);\n\
     }\n"
    entry entry

module For_testing = struct
  let main_calling = main_calling
end
