(* The runtime is C, kept here as text. Its parts: writing and failing,
   which every program uses; allocation; the threads that run branches at
   once; and what a test program gives the runner, which is Truss in the
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
#include <unistd.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/socket.h>
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
#ifdef T_TESTS
  /* The runner writes to workers that may have ended, which is an error for
     it to see, not a signal to end it. */
  signal(SIGPIPE, SIG_IGN);
#endif
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
/* The alternate signal stack that the runtime installed on a thread it
   created: the stack's memory, and the alternate stack that the thread
   had before. */
struct t_thread_signal_stack {
  void *memory;
  stack_t previous;
};

/* Installs an alternate signal stack on the calling thread, so that the
   handler of a stack overflow can run. */
static void t_thread_signal_stack_install(struct t_thread_signal_stack *installed) {
  stack_t stack;
  memset(&stack, 0, sizeof stack);
  installed->memory = malloc(65536);
  if (installed->memory == NULL) return;
  stack.ss_sp = installed->memory;
  stack.ss_size = 65536;
  if (sigaltstack(&stack, &installed->previous) != 0) {
    free(installed->memory);
    installed->memory = NULL;
  }
}

/* Restores the alternate signal stack that the thread had before and
   frees the installed one. A thread calls this before it exits.
   AddressSanitizer unmaps the alternate stack that it finds at thread
   exit, and aborts if that stack is not the one it installed. */
static void t_thread_signal_stack_remove(struct t_thread_signal_stack *installed) {
  if (installed->memory == NULL) return;
  sigaltstack(&installed->previous, NULL);
  free(installed->memory);
}

/* The attributes of a thread that the runtime creates: a stack as large as
   the main thread's, so that the recursion depth limit is the same on
   every thread. */
static void t_thread_attributes(pthread_attr_t *attributes) {
  struct rlimit limit;
  size_t stack = (size_t)8 << 20;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY &&
      limit.rlim_cur >= ((rlim_t)1 << 16) && limit.rlim_cur <= ((rlim_t)1 << 30))
    stack = (size_t)limit.rlim_cur;
  pthread_attr_init(attributes);
  pthread_attr_setstacksize(attributes, stack);
}

/* Coroutines.

   A coroutine is a function call with its own stack. It runs only between
   a resume and its next suspend. A scheduler that runs one task at a
   time, such as a test's, runs each task as a coroutine: it resumes the
   task it chose, and a task that must block suspends.

   Each coroutine is a thread. [running] says whether the coroutine or its
   resumer runs, and the other one blocks on [switched] until [running]
   changes. Exactly one of the two runs at any time, so the data they
   share needs no other lock. */
struct t_coroutine {
  pthread_t thread;
  pthread_mutex_t lock;
  pthread_cond_t switched;
  int running;
  int finished;
  void (*code)(void *environment, uint64_t item);
  void *environment;
  uint64_t item;
};

static _Thread_local struct t_coroutine *t_coroutine_self;

static void t_coroutine_switch(struct t_coroutine *coroutine, int to_coroutine) {
  coroutine->running = to_coroutine;
  pthread_cond_broadcast(&coroutine->switched);
  while (coroutine->running == to_coroutine && !coroutine->finished)
    pthread_cond_wait(&coroutine->switched, &coroutine->lock);
}

static void *t_coroutine_main(void *argument) {
  struct t_coroutine *coroutine = argument;
  t_coroutine_self = coroutine;
  struct t_thread_signal_stack signal_stack;
  t_thread_signal_stack_install(&signal_stack);
  pthread_mutex_lock(&coroutine->lock);
  while (!coroutine->running) pthread_cond_wait(&coroutine->switched, &coroutine->lock);
  pthread_mutex_unlock(&coroutine->lock);
  coroutine->code(coroutine->environment, coroutine->item);
  t_thread_signal_stack_remove(&signal_stack);
  pthread_mutex_lock(&coroutine->lock);
  coroutine->finished = 1;
  coroutine->running = 0;
  pthread_cond_broadcast(&coroutine->switched);
  pthread_mutex_unlock(&coroutine->lock);
  return NULL;
}

t_usize t_runtime_coroutine_start(void (*code)(void *environment, uint64_t item), void *environment,
                               uint64_t item) {
  struct t_coroutine *coroutine = malloc(sizeof *coroutine);
  if (coroutine == NULL) t_out_of_memory();
  pthread_mutex_init(&coroutine->lock, NULL);
  pthread_cond_init(&coroutine->switched, NULL);
  coroutine->running = 0;
  coroutine->finished = 0;
  coroutine->code = code;
  coroutine->environment = environment;
  coroutine->item = item;
  pthread_attr_t attributes;
  t_thread_attributes(&attributes);
  int failed = pthread_create(&coroutine->thread, &attributes, t_coroutine_main, coroutine);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
  return (t_usize)coroutine;
}

/* Runs a coroutine until it suspends or its function returns. Returns 1 if
   it suspended. Returns 0 if its function returned, and frees the
   coroutine. */
uint8_t t_runtime_coroutine_resume(t_usize handle) {
  struct t_coroutine *coroutine = (struct t_coroutine *)handle;
  pthread_mutex_lock(&coroutine->lock);
  t_coroutine_switch(coroutine, 1);
  int finished = coroutine->finished;
  pthread_mutex_unlock(&coroutine->lock);
  if (!finished) return 1;
  pthread_join(coroutine->thread, NULL);
  pthread_mutex_destroy(&coroutine->lock);
  pthread_cond_destroy(&coroutine->switched);
  free(coroutine);
  return 0;
}

/* Called in a coroutine. Switches to the code that resumed the coroutine,
   and returns when the coroutine is resumed again. */
void t_runtime_coroutine_suspend(void) {
  struct t_coroutine *coroutine = t_coroutine_self;
  if (coroutine == NULL) t_runtime_compiler_bug();
  pthread_mutex_lock(&coroutine->lock);
  t_coroutine_switch(coroutine, 0);
  pthread_mutex_unlock(&coroutine->lock);
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

/* Tasks. */

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

#else

/* Each task runs on a thread of its own.

   A group counts its tasks that have not ended, and [join] blocks until
   the count is zero. A group is cancelled once, and a task is cancelled
   when its group or a group that encloses it is. [parent] is the group of
   the task that opened this group. It outlives this group: the task that
   opened this group joins it before the task ends. */
struct t_group {
  pthread_mutex_t lock;
  pthread_cond_t ended;
  size_t running;
  atomic_int cancelled;
  struct t_group *parent;
};

/* The group of the task that the calling thread runs. NULL on a thread
   that runs no task. */
static _Thread_local struct t_group *t_task_group;

struct t_task {
  struct t_group *group;
  void (*code)(void *environment, uint64_t item);
  void *environment;
  uint64_t item;
};

/* Waiting on a key. A key hashes to a slot, which counts the wakes of its
   keys. [watch] reads the count as a ticket, [wait] blocks while the count
   equals the ticket, and [wake] increments the count. Two keys can share
   a slot, so [wait] can return without a wake of its own key, and its
   caller tests its condition again. */
#define T_WAIT_SLOTS 64

struct t_wait_slot {
  pthread_mutex_t lock;
  pthread_cond_t woken;
  uint64_t wakes;
};

static struct t_wait_slot t_wait_slots[T_WAIT_SLOTS];
static pthread_once_t t_wait_slots_once = PTHREAD_ONCE_INIT;

static void t_wait_slots_start(void) {
  for (int index = 0; index < T_WAIT_SLOTS; index++) {
    pthread_mutex_init(&t_wait_slots[index].lock, NULL);
    pthread_cond_init(&t_wait_slots[index].woken, NULL);
    t_wait_slots[index].wakes = 0;
  }
}

static struct t_wait_slot *t_wait_slot(uint64_t key) {
  pthread_once(&t_wait_slots_once, t_wait_slots_start);
  return &t_wait_slots[(key * 0x9E3779B97F4A7C15ULL) >> 58];
}

int32_t t_runtime_tasks_cancelled(void) {
  for (struct t_group *group = t_task_group; group != NULL; group = group->parent)
    if (atomic_load_explicit(&group->cancelled, memory_order_acquire)) return 1;
  return 0;
}

uint64_t t_runtime_tasks_watch(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  pthread_mutex_lock(&slot->lock);
  uint64_t ticket = slot->wakes;
  pthread_mutex_unlock(&slot->lock);
  return ticket;
}

/* Blocks until the slot of [key] has been woken after [ticket] was
   issued. A cancellable wait also returns when the calling task is
   cancelled. */
static void t_wait(uint64_t key, uint64_t ticket, int cancellable) {
  struct t_wait_slot *slot = t_wait_slot(key);
  pthread_mutex_lock(&slot->lock);
  while (slot->wakes == ticket && !(cancellable && t_runtime_tasks_cancelled()))
    pthread_cond_wait(&slot->woken, &slot->lock);
  pthread_mutex_unlock(&slot->lock);
}

int32_t t_runtime_tasks_wait(uint64_t key, uint64_t ticket) {
  t_wait(key, ticket, 1);
  return 0;
}

int32_t t_runtime_tasks_wake(uint64_t key) {
  struct t_wait_slot *slot = t_wait_slot(key);
  pthread_mutex_lock(&slot->lock);
  slot->wakes += 1;
  pthread_cond_broadcast(&slot->woken);
  pthread_mutex_unlock(&slot->lock);
  return 0;
}

uint64_t t_runtime_tasks_open(void) {
  struct t_group *group = malloc(sizeof *group);
  if (group == NULL) t_out_of_memory();
  pthread_mutex_init(&group->lock, NULL);
  pthread_cond_init(&group->ended, NULL);
  group->running = 0;
  atomic_init(&group->cancelled, 0);
  group->parent = t_task_group;
  return (uint64_t)(uintptr_t)group;
}

static void *t_task_main(void *argument) {
  struct t_task task = *(struct t_task *)argument;
  free(argument);
  t_task_group = task.group;
  /* Signals sent to the process go to the thread that started it, as they
     do in a program with one thread. */
  sigset_t all;
  sigfillset(&all);
  sigdelset(&all, SIGSEGV);
  sigdelset(&all, SIGBUS);
  sigdelset(&all, SIGFPE);
  sigdelset(&all, SIGILL);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  struct t_thread_signal_stack signal_stack;
  t_thread_signal_stack_install(&signal_stack);
  task.code(task.environment, task.item);
  t_thread_signal_stack_remove(&signal_stack);
  pthread_mutex_lock(&task.group->lock);
  task.group->running -= 1;
  if (task.group->running == 0) pthread_cond_broadcast(&task.group->ended);
  pthread_mutex_unlock(&task.group->lock);
  return NULL;
}

uint8_t t_runtime_tasks_spawn(uint64_t handle, void (*code)(void *environment, uint64_t item),
                              void *environment, uint64_t item) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  if (atomic_load_explicit(&group->cancelled, memory_order_acquire)) return 0;
  struct t_task *task = malloc(sizeof *task);
  if (task == NULL) t_out_of_memory();
  task->group = group;
  task->code = code;
  task->environment = environment;
  task->item = item;
  pthread_mutex_lock(&group->lock);
  group->running += 1;
  pthread_mutex_unlock(&group->lock);
  pthread_t thread;
  pthread_attr_t attributes;
  t_thread_attributes(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  int failed = pthread_create(&thread, &attributes, t_task_main, task);
  pthread_attr_destroy(&attributes);
  if (failed) t_out_of_memory();
  return 1;
}

int32_t t_runtime_tasks_join(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  pthread_mutex_lock(&group->lock);
  while (group->running > 0) pthread_cond_wait(&group->ended, &group->lock);
  pthread_mutex_unlock(&group->lock);
  pthread_mutex_destroy(&group->lock);
  pthread_cond_destroy(&group->ended);
  free(group);
  return 0;
}

/* Cancels the group. Returns 1 to the first caller. Every waiter is woken
   so that a cancelled one returns: the slot's lock is held for the
   broadcast, so a waiter either tests the flag after it is set or is
   already blocked when the broadcast comes. */
int32_t t_runtime_tasks_cancel(uint64_t handle) {
  struct t_group *group = (struct t_group *)(uintptr_t)handle;
  int cancelled = 0;
  if (!atomic_compare_exchange_strong(&group->cancelled, &cancelled, 1)) return 0;
  pthread_once(&t_wait_slots_once, t_wait_slots_start);
  for (int index = 0; index < T_WAIT_SLOTS; index++) {
    pthread_mutex_lock(&t_wait_slots[index].lock);
    pthread_cond_broadcast(&t_wait_slots[index].woken);
    pthread_mutex_unlock(&t_wait_slots[index].lock);
  }
  return 1;
}

/* A mutex is a [uint64_t] that its owner initialized to zero: 0 is
   unlocked and 1 is locked. A thread that finds it locked waits on the
   mutex's address as a key. The wait is not cancellable: a cancelled task
   still waits for the lock, since nothing else could answer for the
   method it called. */
int32_t t_runtime_tasks_lock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  for (;;) {
    uint64_t ticket = t_runtime_tasks_watch(mutex);
    uint64_t unlocked = 0;
    if (__atomic_compare_exchange_n(word, &unlocked, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))
      return 0;
    t_wait(mutex, ticket, 0);
  }
}

int32_t t_runtime_tasks_unlock(uint64_t mutex) {
  uint64_t *word = (uint64_t *)(uintptr_t)mutex;
  __atomic_store_n(word, 0, __ATOMIC_RELEASE);
  return t_runtime_tasks_wake(mutex);
}

int32_t t_runtime_tasks_yield(void) {
  sched_yield();
  return 0;
}

#endif

struct t_branch {
  void (*run)(void *environment);
  void *environment;
};

#ifdef T_IN_ORDER

/* A test program, and code run while compiling, run a fork's branches in
   order, which gives what running them at once gives. A test already has
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
#define T_FORK 32

struct t_worker {
  _Alignas(64) _Atomic(int64_t) top;
  _Alignas(64) _Atomic(int64_t) bottom;
  uint64_t random;
  _Alignas(64) _Atomic(struct t_job *) jobs[T_QUEUE];
};

static struct t_worker t_workers[T_WORKERS];
static size_t t_worker_count;
static _Thread_local struct t_worker *t_self;
static pthread_once_t t_pool_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t t_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t t_pool_wake = PTHREAD_COND_INITIALIZER;
static atomic_size_t t_sleepers;

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
  size_t count = t_worker_count;
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
  for (size_t index = 0; index < t_worker_count; index++)
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
   done or some thread has a job already. */
static void t_sleep(struct t_job *job) {
  pthread_mutex_lock(&t_pool_lock);
  atomic_fetch_add(&t_sleepers, 1);
  if (!(job != NULL && atomic_load(&job->done)) && !t_any_job())
    pthread_cond_wait(&t_pool_wake, &t_pool_lock);
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
      t_sleep(job);
      idle = 0;
    }
  }
}

static void *t_worker_main(void *argument) {
  struct t_worker *self = argument;
  t_self = self;
  /* Signals sent to the process go to the thread that started it, as they
     do in a program with one thread. */
  sigset_t all;
  sigfillset(&all);
  sigdelset(&all, SIGSEGV);
  sigdelset(&all, SIGBUS);
  sigdelset(&all, SIGFPE);
  sigdelset(&all, SIGILL);
  pthread_sigmask(SIG_SETMASK, &all, NULL);
  /* A worker never exits, so its alternate signal stack is never removed. */
  struct t_thread_signal_stack signal_stack;
  t_thread_signal_stack_install(&signal_stack);
  unsigned idle = 0;
  for (;;) {
    struct t_job *job = t_find(self);
    if (job != NULL) {
      t_run_taken(job);
      idle = 0;
    } else if (++idle < 40) {
      t_rest(idle);
    } else {
      t_sleep(NULL);
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
  t_worker_count = (size_t)count;
  if (count == 1) return;
  t_self = &t_workers[0];
  pthread_attr_t attributes;
  t_thread_attributes(&attributes);
  pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);
  for (long index = 1; index < count; index++) {
    pthread_t thread;
    if (pthread_create(&thread, &attributes, t_worker_main, &t_workers[index]) != 0) {
      /* Fewer threads than cores is slower and still right. */
      t_worker_count = (size_t)index;
      break;
    }
  }
  pthread_attr_destroy(&attributes);
  if (t_worker_count == 1) t_self = NULL;
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
    /* What the branches before this one offered, they took back or waited
       for, so the newest job on the queue is this one, unless a thief has
       it, and then a thief has every job offered before it too. */
    struct t_job *back = t_take_back(self);
    if (back == job) job->run(job->environment);
    else if (back == NULL) t_wait_for(self, job);
    else t_runtime_compiler_bug();
  }
}

void t_runtime_parallel(const struct t_branch *branches, t_usize count) {
  pthread_once(&t_pool_once, t_pool_start);
  struct t_worker *self = t_self;
  if (self == NULL) {
    /* One core, or a thread that is not the pool's: in order. */
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
