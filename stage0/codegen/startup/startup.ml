let headers =
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
#include <sys/timerfd.h>
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

__attribute__((noinline)) int *t_runtime_errno_address_uncached(void) {
  __asm__ __volatile__("");
  return &errno;
}

void *t_runtime_allocate(uint64_t size, uint64_t alignment);

static int t_report = -1;

void t_runtime_report_tests_to(int32_t descriptor) { t_report = descriptor; }

enum { t_passed, t_failed, t_panicked, t_incomplete, t_echoed };

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

static void t_text_position(const struct t_site *site) {
  t_text_add(site->file, site->file_length);
  t_text_string(":");
  t_text_number(site->line);
  t_text_string(":");
  t_text_number(site->column);
}

static void t_record(uint8_t kind) {
  uint8_t header[5];
  uint32_t length = (uint32_t)t_text_length;
  header[0] = kind;
  for (int byte = 0; byte < 4; byte++) header[1 + byte] = (uint8_t)(length >> (8 * byte));
  t_write_all(t_report, header, sizeof header);
  t_write_all(t_report, t_text, t_text_length);
}

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

static void t_describe(const uint8_t *message, uint64_t length, const struct t_site *site) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_add(message, length);
  t_text_string("\n  at ");
  t_text_position(site);
}

_Noreturn void t_runtime_panic(const uint8_t *message, uint64_t length, const struct t_site *site) {
  t_describe(message, length, site);
  t_end(t_panicked, "panic: ", 101);
}

_Noreturn void t_runtime_assertion_failed(const uint8_t *message, uint64_t length, const struct t_site *site) {
  t_describe(message, length, site);
  t_end(t_failed, "assertion failed: ", 1);
}

_Noreturn void t_runtime_todo(const uint8_t *message, uint64_t length, const struct t_site *site) {
  t_describe(message, length, site);
  t_end(t_incomplete, "", 101);
}

void t_runtime_echo(const uint8_t *text, uint64_t length, const struct t_site *site) {
  pthread_mutex_lock(&t_text_lock);
  t_text_length = 0;
  t_text_position(site);
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
  (void)pthread_mutex_trylock(&t_text_lock);
  t_text_length = 0;
  t_text_string("stack overflow");
  t_end(t_panicked, "", 101);
}

static void t_install_signal_dispositions(void) {
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
  signal(SIGPIPE, SIG_IGN);
  sigset_t runtime;
  sigemptyset(&runtime);
  sigaddset(&runtime, SIGSEGV);
  sigaddset(&runtime, SIGBUS);
  sigaddset(&runtime, SIGURG);
  pthread_sigmask(SIG_UNBLOCK, &runtime, NULL);
}
|}

let allocation =
  {|
#ifdef T_TESTS
static uint64_t t_live_blocks = 0;
#define t_block_allocated() (t_live_blocks += 1)
#define t_block_freed() (t_live_blocks -= 1)
uint64_t t_runtime_live_blocks(void) { return t_live_blocks; }
#else
#define t_block_allocated() ((void)0)
#define t_block_freed() ((void)0)
#endif

void *t_runtime_allocate(uint64_t size, uint64_t alignment) {
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

void *t_runtime_reallocate(void *pointer, uint64_t old_size, uint64_t size, uint64_t alignment) {
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
static size_t t_stack_size(void) {
  struct rlimit limit;
  size_t stack = (size_t)8 << 20;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY &&
      limit.rlim_cur >= ((rlim_t)1 << 16) && limit.rlim_cur <= ((rlim_t)1 << 30))
    stack = (size_t)limit.rlim_cur;
  return stack;
}

static void t_thread_signal_stack_install(void) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  stack.ss_sp = malloc(65536);
  if (stack.ss_sp == NULL) return;
  stack.ss_size = 65536;
  if (sigaltstack(&stack, NULL) != 0) free(stack.ss_sp);
}

static void t_thread_attributes(pthread_attr_t *attributes) {
  pthread_attr_init(attributes);
  pthread_attr_setstacksize(attributes, t_stack_size());
}

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

#define T_STACK_CACHE 64

static pthread_mutex_t t_stack_lock = PTHREAD_MUTEX_INITIALIZER;
static void *t_stack_cache[T_STACK_CACHE];
static size_t t_stack_cached;
static size_t t_stack_bytes;
static size_t t_stack_guard;

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

struct t_coroutine {
  struct t_context context;
  struct t_context resumer;
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

__attribute__((noinline)) static struct t_coroutine *t_coroutine_current(void) {
  __asm__ __volatile__("");
  return t_coroutine_self;
}

__attribute__((noinline)) static void t_coroutine_current_set(struct t_coroutine *coroutine) {
  __asm__ __volatile__("");
  t_coroutine_self = coroutine;
}

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

uint64_t t_runtime_coroutine_start(void (*code)(void *environment, uint64_t item), void *environment,
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
  return (uint64_t)coroutine;
}

uint8_t t_runtime_coroutine_resume(uint64_t handle) {
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

void t_runtime_coroutine_suspend(void) {
  struct t_coroutine *coroutine = t_coroutine_current();
  if (coroutine == NULL) t_runtime_compiler_bug();
  t_coroutine_leave(coroutine);
}

struct t_shared {
  void *block;
  atomic_size_t count;
  pthread_mutex_t mutex;
};

static struct t_shared *t_shared_header(void *value) { return (struct t_shared *)value - 1; }

void *t_runtime_shared_allocate(uint64_t size, uint64_t alignment) {
  if (alignment < _Alignof(struct t_shared)) alignment = _Alignof(struct t_shared);
  uint64_t offset = (sizeof(struct t_shared) + alignment - 1) / alignment * alignment;
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

static uint64_t t_descriptor_limit(int32_t descriptor, int32_t writing) {
  struct timeval limit;
  socklen_t size = sizeof limit;
  if (getsockopt(descriptor, SOL_SOCKET, writing ? SO_SNDTIMEO : SO_RCVTIMEO, &limit, &size) != 0)
    return 0;
  return (uint64_t)limit.tv_sec * 1000000000u + (uint64_t)limit.tv_usec * 1000u;
}

static int32_t t_descriptor_poll(int32_t descriptor, int32_t writing) {
  uint64_t limit = t_descriptor_limit(descriptor, writing);
  uint64_t milliseconds = (limit + 999999u) / 1000000u;
  struct pollfd one = {descriptor, writing ? POLLOUT : POLLIN, 0};
  int timeout = limit == 0 ? -1 : milliseconds > INT32_MAX ? INT32_MAX : (int)milliseconds;
  return poll(&one, 1, timeout) != 0;
}

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

struct t_branch {
  void (*run)(void *environment);
  void *environment;
};

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

static struct t_worker t_workers[T_WORKERS + T_SPARES];
static atomic_size_t t_worker_count;
static _Thread_local struct t_worker *t_self;

__attribute__((noinline)) static struct t_worker *t_worker_self(void) {
  __asm__ __volatile__("");
  return t_self;
}
static uint32_t t_requested_workers;
static size_t t_pool_workers = 1;
static pthread_once_t t_pool_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t t_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_pool_wake = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t t_spare_lock = PTHREAD_MUTEX_INITIALIZER;
static atomic_size_t t_sleepers;
static atomic_size_t t_idle_runners;

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

static void t_run_taken(struct t_job *job) {
  job->run(job->environment);
  atomic_store(&job->done, 1);
  t_wake(1);
}

static void t_rest(unsigned idle) {
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

static void t_sleep(atomic_int *done, int runner) {
  pthread_mutex_lock(&t_pool_lock);
  atomic_fetch_add(&t_sleepers, 1);
  if (runner) atomic_fetch_add(&t_idle_runners, 1);
  if (!(done != NULL && atomic_load(done)) && !t_any_job() &&
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
      atomic_fetch_add(&t_blocked, 1);
      t_spare_ensure();
      t_sleep(&job->done, 0);
      atomic_fetch_sub(&t_blocked, 1);
      idle = 0;
    }
  }
}

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

static void t_run_until(struct t_worker *self, atomic_int *done) {
  unsigned idle = 0;
  while (done == NULL || !atomic_load(done)) {
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
      t_sleep(done, 1);
      idle = 0;
    }
  }
}

static void *t_worker_main(void *argument) {
  struct t_worker *self = argument;
  t_self = self;
  t_runner_signals();
  t_thread_signal_stack_install();
  t_run_until(self, NULL);
  return NULL;
}

static void t_pool_start(void) {
  long count = t_requested_workers;
  if (count == 0) {
    count = sysconf(_SC_NPROCESSORS_ONLN);
    const char *requested = getenv("TRUSS_WORKERS");
    if (requested != NULL && requested[0] != 0) count = strtol(requested, NULL, 10);
  }
  if (count > T_WORKERS) count = T_WORKERS;
  pthread_attr_t attributes;
  t_thread_attributes(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  pthread_mutex_lock(&t_spare_lock);
  while ((long)t_pool_workers < count) {
    size_t index = atomic_load(&t_worker_count);
    t_workers[index].random = (uint64_t)index + 1;
    pthread_t thread;
    if (pthread_create(&thread, &attributes, t_worker_main, &t_workers[index]) != 0) break;
    atomic_store(&t_worker_count, index + 1);
    t_pool_workers += 1;
  }
  pthread_mutex_unlock(&t_spare_lock);
  pthread_attr_destroy(&attributes);
}

static void t_fork(struct t_worker *self, const struct t_branch *branches, size_t count) {
  struct t_job jobs[T_FORK];
  int offered = 0;
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
    struct t_job *back = t_take_back(self);
    if (back == job) job->run(job->environment);
    else if (back == NULL) t_wait_for(self, job);
    else t_runtime_compiler_bug();
  }
}

void t_runtime_parallel(const struct t_branch *branches, uint64_t count) {
  pthread_once(&t_pool_once, t_pool_start);
  if (t_pool_workers == 1) {
    for (uint64_t index = 0; index < count; index++) branches[index].run(branches[index].environment);
    return;
  }
  struct t_worker *self = t_worker_self();
  while (count > 0) {
    size_t batch = count > T_FORK + 1 ? T_FORK + 1 : (size_t)count;
    t_fork(self, branches, batch);
    branches += batch;
    count -= batch;
  }
}

struct t_range {
  void (*body)(void *environment, uint64_t first, uint64_t last);
  void *environment;
  uint64_t first;
  uint64_t last;
  uint64_t size;
};

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

void t_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t last),
                              void *environment, uint64_t first, uint64_t last) {
  struct t_range whole = {body, environment, first, last, ((last - first) >> 8) + 1};
  t_range_run(&whole);
}

struct t_wait_slot;

struct t_task {
  struct t_context context;
  void *stack;
  struct t_group *group;
  void (*code)(void *environment, uint64_t item);
  void *environment;
  uint64_t item;
  struct t_task *next;
  uint64_t wait_key;
  _Atomic(struct t_wait_slot *) cancellable;
  struct t_task *sibling;
  _Atomic(pthread_t) thread;
  atomic_int blocking;
  atomic_int state;
  int finished;
  struct t_coroutine *coroutine;
#ifdef T_ADDRESS_SANITIZER
  const void *suspended_stack;
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

struct t_group {
  pthread_mutex_t lock;
  size_t running;
  atomic_int cancelled;
  struct t_group *parent;
  struct t_task *tasks;
  struct t_group *children;
  struct t_group *next;
  struct t_task *joiner;
  struct t_group *interrupted;
};

enum { T_RUNNING, T_PARKING, T_PARKED };

static _Thread_local struct t_task *t_task_running;
static _Thread_local struct t_context t_thread_context;

__attribute__((noinline)) static struct t_task *t_task_self(void) {
  __asm__ __volatile__("");
  return t_task_running;
}

__attribute__((noinline)) static struct t_context *t_thread_context_self(void) {
  __asm__ __volatile__("");
  return &t_thread_context;
}

static pthread_mutex_t t_run_lock = PTHREAD_MUTEX_INITIALIZER;
static struct t_task *t_run_first;
static struct t_task *t_run_last;

static void t_run_push(struct t_task *task) {
  task->next = NULL;
  pthread_mutex_lock(&t_run_lock);
  if (t_run_last != NULL) t_run_last->next = task;
  else t_run_first = task;
  t_run_last = task;
  atomic_fetch_add(&t_run_count, 1);
  pthread_mutex_unlock(&t_run_lock);
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
  if (left > 0) t_spare_ensure();
  return task;
}

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
  int state = T_PARKING;
  if (!atomic_compare_exchange_strong(&task->state, &state, T_PARKED)) t_run_push(task);
}

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

static void t_task_park(struct t_task *task, pthread_mutex_t *lock) {
  atomic_store(&task->state, T_PARKING);
  pthread_mutex_unlock(lock);
  t_task_switch(task);
}

static void t_task_ready(struct t_task *task) {
  int state = T_PARKING;
  if (atomic_compare_exchange_strong(&task->state, &state, T_RUNNING)) return;
  atomic_store(&task->state, T_RUNNING);
  t_run_push(task);
}

static pthread_cond_t t_spare_wake = PTHREAD_COND_INITIALIZER;
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

static void t_spare_ensure(void) {
  if (atomic_load(&t_run_count) == 0) return;
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
        t_out_of_memory();
      }
      pthread_attr_destroy(&attributes);
    }
  }
  pthread_mutex_unlock(&t_spare_lock);
}

#define T_COUNTED UINT_FAST64_MAX

struct t_caller {
  atomic_uint_fast64_t since;
  struct t_caller *next;
};

static _Thread_local struct t_caller t_caller_own;
static _Thread_local int t_caller_listed;
static pthread_mutex_t t_monitor_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_monitor_wake = PTHREAD_COND_INITIALIZER;
static pthread_once_t t_monitor_once = PTHREAD_ONCE_INIT;
static struct t_caller *t_callers;
static atomic_uint_fast64_t t_tick = 1;

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
      atomic_store(&t_monitor_asleep, 1);
      if (atomic_load(&t_run_count) == 0) pthread_cond_wait(&t_monitor_wake, &t_monitor_lock);
      continue;
    }
    atomic_store(&t_monitor_asleep, 0);
    uint_fast64_t tick = atomic_fetch_add(&t_tick, 1) + 1;
    int counted = 0;
    for (struct t_caller *caller = t_callers; caller != NULL; caller = caller->next) {
      uint_fast64_t since = atomic_load(&caller->since);
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

void t_runtime_blocking_begin(void) {
  struct t_task *task = t_task_self();
  atomic_store(&task->thread, pthread_self());
  atomic_store(&task->blocking, 1);
  atomic_store(&t_caller_self()->since, atomic_load(&t_tick));
  t_spare_ensure();
}

void t_runtime_blocking_end(void) {
  if (atomic_exchange(&t_caller_self()->since, 0) == T_COUNTED) atomic_fetch_sub(&t_blocked, 1);
  atomic_store(&t_task_self()->blocking, 0);
}

static void t_interrupt_handler(int signal) { (void)signal; }

static pthread_mutex_t t_interrupter_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_interrupter_wake = PTHREAD_COND_INITIALIZER;
static struct t_group *t_interrupter_groups;
static pthread_once_t t_interrupt_once = PTHREAD_ONCE_INIT;

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

#define T_WAIT_SLOTS 1024

struct t_wait_slot {
  pthread_mutex_t lock;
  atomic_uint_fast64_t wakes;
  struct t_task *parked;
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
  for (struct t_group *group = t_task_self()->group; group != NULL; group = group->parent)
    if (atomic_load(&group->cancelled)) return 1;
  return 0;
}

uint64_t t_runtime_tasks_watch(uint64_t key) { return atomic_load(&t_wait_slot(key)->wakes); }

static void t_wait(uint64_t key, uint64_t ticket, int cancellable) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task *task = t_task_self();
  pthread_mutex_lock(&slot->lock);
  if (cancellable) atomic_store(&task->cancellable, slot);
  if (atomic_load(&slot->wakes) != ticket || (cancellable && t_runtime_tasks_cancelled())) {
    pthread_mutex_unlock(&slot->lock);
  } else {
    task->wait_key = key;
    task->next = slot->parked;
    slot->parked = task;
    t_task_park(task, &slot->lock);
  }
  if (cancellable) atomic_store(&task->cancellable, NULL);
}

int32_t t_runtime_tasks_wait(uint64_t key, uint64_t ticket) {
  t_wait(key, ticket, 1);
  return 0;
}

int32_t t_runtime_tasks_wake(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task *tasks = NULL;
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
  pthread_mutex_unlock(&slot->lock);
  while (tasks != NULL) {
    struct t_task *task = tasks;
    tasks = task->next;
    t_task_ready(task);
  }
  return 0;
}

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

struct t_timer {
  uint64_t deadline;
  uint64_t key;
  size_t index;
  int fired;
};

static pthread_mutex_t t_timer_lock = PTHREAD_MUTEX_INITIALIZER;
static struct t_timer **t_timers;
static size_t t_timer_count;
static size_t t_timer_room;

#define T_TIMERS_EVENT 1
#define T_SIGNALS_EVENT 2

static int t_poller = -1;
static pthread_once_t t_poller_once = PTHREAD_ONCE_INIT;
static void t_poller_start(void);
static void t_signals_arrived(void);

#ifdef __linux__
static int t_timer_descriptor = -1;
#endif

static uint64_t t_monotonic(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000000u + (uint64_t)now.tv_nsec;
}

static void t_timer_place(struct t_timer *timer, size_t index) {
  t_timers[index] = timer;
  timer->index = index;
}

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

static void t_timer_remove(struct t_timer *timer) {
  size_t index = timer->index;
  t_timer_count -= 1;
  if (index == t_timer_count) return;
  t_timer_place(t_timers[t_timer_count], index);
  t_timer_settle(index);
}

static void t_timer_arm(void) {
  uint64_t deadline = t_timers[0]->deadline;
#ifdef __linux__
  struct itimerspec setting;
  memset(&setting, 0, sizeof setting);
  setting.it_value.tv_sec = (time_t)(deadline / 1000000000u);
  setting.it_value.tv_nsec = (long)(deadline % 1000000000u);
  timerfd_settime(t_timer_descriptor, TFD_TIMER_ABSTIME, &setting, NULL);
#else
  uint64_t now = t_monotonic();
  struct kevent change;
  EV_SET(&change, T_TIMERS_EVENT, EVFILT_TIMER, EV_ADD | EV_ONESHOT, NOTE_NSECONDS,
         deadline > now ? (intptr_t)(deadline - now) : 1, NULL);
  kevent(t_poller, &change, 1, NULL, 0, NULL);
#endif
}

static void t_timers_fire(void) {
  uint64_t now = t_monotonic();
  pthread_mutex_lock(&t_timer_lock);
  while (t_timer_count > 0 && t_timers[0]->deadline <= now) {
    struct t_timer *first = t_timers[0];
    t_timer_remove(first);
    first->fired = 1;
    uint64_t key = first->key;
    pthread_mutex_unlock(&t_timer_lock);
    t_runtime_tasks_wake(key);
    pthread_mutex_lock(&t_timer_lock);
  }
  if (t_timer_count > 0) t_timer_arm();
  pthread_mutex_unlock(&t_timer_lock);
}

static void t_timer_begin(struct t_timer *timer, uint64_t nanoseconds, uint64_t key) {
  pthread_once(&t_poller_once, t_poller_start);
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
  if (timer->index == 0) t_timer_arm();
  pthread_mutex_unlock(&t_timer_lock);
}

static int t_timer_fired(struct t_timer *timer) {
  pthread_mutex_lock(&t_timer_lock);
  int fired = timer->fired;
  pthread_mutex_unlock(&t_timer_lock);
  return fired;
}

static int t_timer_end(struct t_timer *timer) {
  pthread_mutex_lock(&t_timer_lock);
  int fired = timer->fired;
  if (!fired) t_timer_remove(timer);
  pthread_mutex_unlock(&t_timer_lock);
  return fired;
}

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

#define T_DESCRIPTORS 65536

#define T_OWN_KEY 1
#define T_CALLERS_KEY 2

static atomic_uchar t_descriptor_registered[T_DESCRIPTORS];

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
      uint64_t key = events[index].data.u64;
      uint32_t ready = events[index].events;
      if (key == T_TIMERS_EVENT) {
        uint64_t expirations;
        ssize_t received = read(t_timer_descriptor, &expirations, sizeof expirations);
        (void)received;
        t_timers_fire();
      } else if (key == T_SIGNALS_EVENT) {
        t_signals_arrived();
      } else {
        if (ready & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) t_runtime_tasks_wake(key);
        if ((key >> 63) && (ready & (EPOLLOUT | EPOLLHUP | EPOLLERR))) t_runtime_tasks_wake(key | 1);
      }
    }
#else
    struct kevent events[64];
    int count = kevent(t_poller, NULL, 0, events, 64, NULL);
    for (int index = 0; index < count; index++) {
      uint64_t key = (uint64_t)(uintptr_t)events[index].udata;
      int writing = events[index].filter == EVFILT_WRITE;
      if (events[index].filter == EVFILT_TIMER)
        t_timers_fire();
      else if (key == T_SIGNALS_EVENT)
        t_signals_arrived();
      else if (key == 0)
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
  if (t_poller < 0) t_out_of_memory();
  t_timer_descriptor = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC | TFD_NONBLOCK);
  if (t_timer_descriptor < 0) t_out_of_memory();
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN;
  event.data.u64 = T_TIMERS_EVENT;
  if (epoll_ctl(t_poller, EPOLL_CTL_ADD, t_timer_descriptor, &event) != 0) t_out_of_memory();
#else
  t_poller = kqueue();
  if (t_poller < 0) t_out_of_memory();
  fcntl(t_poller, F_SETFD, FD_CLOEXEC);
#endif
  pthread_t thread;
  pthread_attr_t attributes;
  pthread_attr_init(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_poller_main, NULL);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
}

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
      && (*t_runtime_errno_address_uncached() != EEXIST || epoll_ctl(t_poller, EPOLL_CTL_MOD, descriptor, &event) != 0))
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
    *t_runtime_errno_address_uncached() = EINTR;
    return 0;
  }
  if (!ready) *t_runtime_errno_address_uncached() = EAGAIN;
  return ready;
}

static uint64_t t_descriptors_key(void) { return (uint64_t)(uintptr_t)&t_task_self()->wait_key; }

uint64_t t_runtime_descriptors_watch(void) { return t_runtime_tasks_watch(t_descriptors_key()); }

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
    *t_runtime_errno_address_uncached() = EINTR;
    return 0;
  }
  return 1;
}

int32_t t_runtime_close(int32_t descriptor) {
  if (descriptor >= 0 && descriptor < T_DESCRIPTORS)
    atomic_store(&t_descriptor_registered[descriptor], 0);
  return close(descriptor);
}

static struct t_group *t_group_new(struct t_group *parent) {
  struct t_group *group = malloc(sizeof *group);
  if (group == NULL) t_out_of_memory();
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

uint64_t t_runtime_tasks_open(void) { return (uint64_t)(uintptr_t)t_group_new(t_task_self()->group); }

static void t_task_entry(void) {
  struct t_task *task = t_task_self();
#ifdef T_ADDRESS_SANITIZER
  __sanitizer_finish_switch_fiber(NULL, &task->thread_stack, &task->thread_stack_size);
#endif
  task->code(task->environment, task->item);
  struct t_group *group = task->group;
  struct t_task *joiner = NULL;
  pthread_mutex_lock(&group->lock);
  for (struct t_task **link = &group->tasks; *link != NULL; link = &(*link)->sibling)
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
  if (joiner != NULL) t_task_ready(joiner);
  task->finished = 1;
  t_task_switch(task);
  t_runtime_compiler_bug();
}

static struct t_task *t_task_new(struct t_group *group, void (*code)(void *environment, uint64_t item),
                                 void *environment, uint64_t item) {
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
  return task;
}

uint8_t t_runtime_tasks_spawn(uint64_t handle, void (*code)(void *environment, uint64_t item),
                              void *environment, uint64_t item) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  if (atomic_load_explicit(&group->cancelled, memory_order_acquire)) return 0;
  pthread_once(&t_pool_once, t_pool_start);
  pthread_once(&t_interrupt_once, t_interrupt_start);
  t_run_push(t_task_new(group, code, environment, item));
  return 1;
}

int32_t t_runtime_tasks_join(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  pthread_mutex_lock(&group->lock);
  while (group->running > 0) {
    struct t_task *task = t_task_self();
    group->joiner = task;
    t_task_park(task, &group->lock);
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

struct t_root {
  void (*code)(void *environment, uint64_t item);
  void *environment;
  atomic_int ended;
};

static void t_root_run(void *argument, uint64_t item) {
  struct t_root *root = argument;
  root->code(root->environment, item);
  atomic_store(&root->ended, 1);
  t_wake(1);
}

void t_runtime_main(void (*code)(void *environment, uint64_t item), void *environment,
                    uint32_t requested_workers) {
  t_install_signal_dispositions();
  t_requested_workers = requested_workers;
  t_self = &t_workers[0];
  t_workers[0].random = 1;
  atomic_store(&t_worker_count, 1);
  struct t_root root = {code, environment, 0};
  t_task_run(t_task_new(t_group_new(NULL), t_root_run, &root, 0));
  t_run_until(&t_workers[0], &root.ended);
}

static void t_wake_one(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  struct t_task **link = NULL;
  pthread_mutex_lock(&slot->lock);
  atomic_fetch_add(&slot->wakes, 1);
  for (struct t_task **parked = &slot->parked; *parked != NULL; parked = &(*parked)->next)
    if ((*parked)->wait_key == key) link = parked;
  struct t_task *woken = NULL;
  if (link != NULL) {
    woken = *link;
    *link = woken->next;
  }
  pthread_mutex_unlock(&slot->lock);
  if (woken != NULL) t_task_ready(woken);
}

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

int32_t t_runtime_tasks_yield(void) {
  t_task_switch(t_task_self());
  return 0;
}

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

static void t_signals_arrived(void) {
  char bytes[64];
  while (read(t_signals_pipe[0], bytes, sizeof bytes) > 0) {
  }
  sigset_t handled;
  sigemptyset(&handled);
  pthread_mutex_lock(&t_signals_lock);
  for (int signal = 1; signal < 64; signal++)
    if (t_signals_handled & ((uint64_t)1 << signal)) sigaddset(&handled, signal);
  pthread_mutex_unlock(&t_signals_lock);
  pthread_sigmask(SIG_UNBLOCK, &handled, NULL);
  t_runtime_tasks_wake((uint64_t)(uintptr_t)&t_signals_pending);
}

static void t_signals_start(void) {
  if (pipe(t_signals_pipe) != 0) t_out_of_memory();
  for (int end = 0; end < 2; end++) {
    fcntl(t_signals_pipe[end], F_SETFD, FD_CLOEXEC);
    fcntl(t_signals_pipe[end], F_SETFL, fcntl(t_signals_pipe[end], F_GETFL) | O_NONBLOCK);
  }
  pthread_once(&t_poller_once, t_poller_start);
#ifdef __linux__
  struct epoll_event event;
  memset(&event, 0, sizeof event);
  event.events = EPOLLIN;
  event.data.u64 = T_SIGNALS_EVENT;
  if (epoll_ctl(t_poller, EPOLL_CTL_ADD, t_signals_pipe[0], &event) != 0) t_out_of_memory();
#else
  struct kevent change;
  EV_SET(&change, t_signals_pipe[0], EVFILT_READ, EV_ADD, 0, 0, (void *)(uintptr_t)T_SIGNALS_EVENT);
  if (kevent(t_poller, &change, 1, NULL, 0, NULL) != 0) t_out_of_memory();
#endif
}

int32_t t_runtime_signals_wait(const int32_t *signals, size_t count) {
  pthread_once(&t_signals_once, t_signals_start);
  uint_fast64_t wanted = 0;
  int installed = 0;
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
        installed = 1;
      }
    }
  }
  pthread_mutex_unlock(&t_signals_lock);
  if (installed) {
    ssize_t written = write(t_signals_pipe[1], "", 1);
    (void)written;
  }
  uint64_t key = (uint64_t)(uintptr_t)&t_signals_pending;
  for (;;) {
    uint64_t ticket = t_runtime_tasks_watch(key);
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
|}

let resolving =
  {|
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
typedef void (*t_test)(void);
const t_test *t_runtime_tests;

void t_runtime_run_test(uint32_t index) { t_runtime_tests[index](); }
|}

let runtime ~tests =
  String.concat ""
    [
      (if tests then "#define T_TESTS 1\n" else "");
      headers;
      Emit_c.site_struct;
      failing;
      allocation;
      threads;
      resolving;
      (if tests then tests_table else "");
    ]

let starting ?(before_start = "") ~declarations ~requested_workers root_call =
  Printf.sprintf
    "typedef __INT32_TYPE__ int32_t;\n\
     typedef __UINT32_TYPE__ uint32_t;\n\
     typedef __UINT64_TYPE__ uint64_t;\n\
     void t_runtime_main(void (*code)(void *environment, uint64_t item), void *environment,\n\
    \                    uint32_t requested_workers);\n\
     %sstruct t_program {\n\
    \  int32_t count;\n\
    \  void *arguments;\n\
    \  int32_t status;\n\
     };\n\
     static void t_program_run(void *environment, uint64_t item) {\n\
    \  struct t_program *program = environment;\n\
    \  (void)item;\n\
    \  %s;\n\
     }\n\
     int main(int count, char **arguments) {\n\
    \  struct t_program program = {(int32_t)count, (void *)arguments, 0};\n\
     %s  t_runtime_main(t_program_run, &program, %d);\n\
    \  return (int)program.status;\n\
     }\n"
    declarations root_call before_start requested_workers

let main_calling entry =
  starting
    ~declarations:(Printf.sprintf "int32_t %s(void);\n" entry)
    ~requested_workers:0
    (Printf.sprintf "program->status = %s()" entry)

let tests_calling ~time_limit_ms ~runner tests =
  let test_declarations =
    String.concat "" (List.map (fun symbol -> Printf.sprintf "void %s(void);\n" symbol) tests)
  in
  starting
    ~declarations:
      (Printf.sprintf
         "typedef void (*t_test)(void);\n\
          extern const t_test *t_runtime_tests;\n\
          int32_t %s(uint32_t count, uint32_t time_limit_milliseconds);\n\
          %sstatic const t_test t_tests[] = { %s };\n"
         runner test_declarations
         (if tests = [] then "0" else String.concat ", " tests))
    ~before_start:"  t_runtime_tests = t_tests;\n" ~requested_workers:1
    (Printf.sprintf "program->status = %s(%d, %d)" runner (List.length tests) time_limit_ms)

let evaluator_calling entry =
  starting
    ~declarations:(Printf.sprintf "void %s(void);\n" entry)
    ~requested_workers:1
    (Printf.sprintf "(void)program;\n  %s()" entry)

let program_calling entry =
  starting
    ~declarations:(Printf.sprintf "int32_t %s(int32_t count, void *arguments);\n" entry)
    ~requested_workers:0
    (Printf.sprintf "program->status = %s(program->count, program->arguments)" entry)

module For_testing = struct
  let main_calling = main_calling
end
