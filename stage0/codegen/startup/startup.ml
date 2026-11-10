(* The runtime is C, kept here as text. It has three parts: writing and
   failing, which every program uses; allocation; and the test runner,
   which only test programs call. *)

let headers =
  (* Strict C11 hides POSIX functions such as [posix_memalign] and
     [sigaltstack] in glibc unless they are asked for. *)
  {|#define _DEFAULT_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <errno.h>
#include <spawn.h>
#include <poll.h>
#include <time.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
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
static uint32_t t_current_test = 0;

enum { t_passed, t_failed, t_panicked, t_incomplete, t_echoed };

/* Text is built in a fixed buffer, so that failing never allocates, even
   when it fails because memory ran out. Longer text is cut short. */
static char t_text[65536];
static size_t t_text_length;

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

static void t_record(uint8_t kind) {
  uint8_t header[9];
  uint32_t length = (uint32_t)t_text_length;
  memcpy(header, &t_current_test, 4);
  header[4] = kind;
  memcpy(header + 5, &length, 4);
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
}

_Noreturn void t_runtime_compiler_bug(void) {
  t_text_length = 0;
  t_text_string("reached code the prover showed unreachable");
  t_end(t_panicked, "compiler bug: ", 101);
}

static _Noreturn void t_out_of_memory(void) {
  t_text_length = 0;
  t_text_string("out of memory");
  if (t_report >= 0) t_end(t_panicked, "", 101);
  t_write_all(2, "out of memory\n", 14);
  abort();
}

static char t_signal_stack[65536];

static void t_stack_overflow(int signal) {
  (void)signal;
  t_text_length = 0;
  t_text_string("stack overflow");
  t_end(t_panicked, "", 101);
}

/* A program argument as UTF-8: the argument itself when it is valid, and
   otherwise a copy with each bad sequence replaced by U+FFFD. Either way it
   lives as long as the program, so the [String] that holds it has capacity
   0 and never frees it. */
static t_usize t_utf8_sequence(const uint8_t *bytes, t_usize left) {
  uint8_t first = bytes[0];
  t_usize length = first < 0x80 ? 1 : (first & 0xe0) == 0xc0 ? 2 : (first & 0xf0) == 0xe0 ? 3 : (first & 0xf8) == 0xf0 ? 4 : 0;
  if (length == 0 || length > left) return 0;
  for (t_usize k = 1; k < length; k++) if ((bytes[k] & 0xc0) != 0x80) return 0;
  uint32_t code = length == 1 ? first : (uint32_t)(first & (0x7f >> length));
  for (t_usize k = 1; k < length; k++) code = (code << 6) | (bytes[k] & 0x3f);
  if ((length == 2 && code < 0x80) || (length == 3 && code < 0x800) || (length == 4 && code < 0x10000)) return 0;
  if (code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return 0;
  return length;
}

uint8_t *t_runtime_program_argument(void *arguments, int32_t index, t_usize *length) {
  uint8_t *bytes = (uint8_t *)((char **)arguments)[index];
  t_usize count = strlen((const char *)bytes);
  t_usize at = 0, fixed = 0;
  int valid = 1;
  while (at < count) {
    t_usize step = t_utf8_sequence(bytes + at, count - at);
    if (step == 0) { valid = 0; step = 1; fixed += 3; } else fixed += step;
    at += step;
  }
  if (valid) { *length = count; return bytes; }
  uint8_t *copy = t_runtime_allocate(fixed, 1);
  t_usize out = 0;
  at = 0;
  while (at < count) {
    t_usize step = t_utf8_sequence(bytes + at, count - at);
    if (step == 0) { copy[out++] = 0xef; copy[out++] = 0xbf; copy[out++] = 0xbd; step = 1; }
    else { memcpy(copy + out, bytes + at, step); out += step; }
    at += step;
  }
  *length = out;
  return copy;
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

/* Gives storage room for at least [minimum] elements, at least doubling it
   so that pushing is amortized O(1). Storage with capacity 0 owns no
   buffer: its elements, if any, are static, so they are copied, and the
   old buffer is never freed. */
void t_runtime_storage_grow(void **buffer, t_usize length, t_usize *capacity, t_usize size, t_usize alignment,
                            t_usize minimum) {
  t_usize wanted = *capacity * 2;
  if (wanted < minimum) wanted = minimum;
  if (wanted < 4) wanted = 4;
  if (size != 0 && wanted > (t_usize)-1 / size) t_out_of_memory();
  if (*capacity == 0) {
    void *fresh = t_runtime_allocate(wanted * size, alignment);
    if (length > 0) memcpy(fresh, *buffer, length * size);
    *buffer = fresh;
  } else {
    *buffer = t_runtime_reallocate(*buffer, *capacity * size, wanted * size, alignment);
  }
  *capacity = wanted;
}

/* Runs a program, found on the PATH as a shell finds it, with the
   arguments, each ending in a zero byte, and waits for it. It returns the
   exit status, or 128 and the signal that ended it; on failure to start it,
   -1 with the error number written. */
int32_t t_runtime_run(const uint8_t *program, t_usize length, const uint8_t *arguments, t_usize arguments_length,
                      int32_t *error) {
  t_usize count = 0;
  for (t_usize i = 0; i < arguments_length; i++)
    if (arguments[i] == 0) count += 1;
  char **argv = malloc((count + 2) * sizeof(char *));
  char *name = malloc(length + 1);
  char *copied = malloc(arguments_length + 1);
  if (argv == NULL || name == NULL || copied == NULL) t_out_of_memory();
  memcpy(name, program, length);
  name[length] = 0;
  if (arguments_length > 0) memcpy(copied, arguments, arguments_length);
  argv[0] = name;
  t_usize at = 0;
  for (t_usize k = 0; k < count; k++) {
    argv[k + 1] = copied + at;
    while (copied[at] != 0) at += 1;
    at += 1;
  }
  argv[count + 1] = NULL;
  pid_t pid;
  extern char **environ;
  int failed = posix_spawnp(&pid, name, NULL, NULL, argv, environ);
  int status = 0;
  if (failed == 0) {
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
  }
  free(argv);
  free(name);
  free(copied);
  if (failed != 0) {
    *error = failed;
    return -1;
  }
  *error = 0;
  return WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
}

/* An environment variable's value and its length, or null when it is
   unset. */
uint8_t *t_runtime_environment(const uint8_t *name, t_usize length, t_usize *value_length) {
  char *terminated = malloc(length + 1);
  if (terminated == NULL) t_out_of_memory();
  memcpy(terminated, name, length);
  terminated[length] = 0;
  char *value = getenv(terminated);
  free(terminated);
  if (value == NULL) return NULL;
  *value_length = strlen(value);
  return (uint8_t *)value;
}

/* Standard input is read a block at a time and handed out from this
   buffer, so that reading a line a byte at a time costs one system call a
   block. */
static uint8_t t_input[4096];
static t_usize t_input_start = 0, t_input_end = 0;

t_isize t_runtime_read(int32_t descriptor, uint8_t *bytes, t_usize count) {
  if (descriptor == 0) {
    if (t_input_start == t_input_end) {
      ssize_t got;
      do got = read(0, t_input, sizeof t_input);
      while (got < 0 && errno == EINTR);
      if (got <= 0) return got;
      t_input_start = 0;
      t_input_end = (t_usize)got;
    }
    t_usize available = t_input_end - t_input_start;
    t_usize given = count < available ? count : available;
    memcpy(bytes, t_input + t_input_start, given);
    t_input_start += given;
    return (t_isize)given;
  }
  for (;;) {
    ssize_t got = read(descriptor, bytes, count);
    if (got < 0 && errno == EINTR) continue;
    return got;
  }
}

/* Debug output: generated debug functions append a value's text here, and
   echo, failed asserts, and the test runner read it. Each thread has its
   own, since tasks run on threads. */
static _Thread_local char *t_debug_buffer;
static _Thread_local t_usize t_debug_used;
static _Thread_local t_usize t_debug_capacity;

void t_runtime_debug_begin(void) { t_debug_used = 0; }

void t_runtime_debug_text(const void *bytes, t_usize count) {
  if (t_debug_used + count > t_debug_capacity) {
    t_usize wanted = t_debug_capacity * 2;
    if (wanted < t_debug_used + count) wanted = t_debug_used + count;
    if (wanted < 256) wanted = 256;
    char *grown = realloc(t_debug_buffer, wanted);
    if (grown == NULL) t_out_of_memory();
    t_debug_buffer = grown;
    t_debug_capacity = wanted;
  }
  memcpy(t_debug_buffer + t_debug_used, bytes, count);
  t_debug_used += count;
}

static void t_debug_c(const char *text) { t_runtime_debug_text((const uint8_t *)text, strlen(text)); }

void t_runtime_debug_signed(int64_t value) {
  char digits[24];
  snprintf(digits, sizeof digits, "%lld", (long long)value);
  t_debug_c(digits);
}

void t_runtime_debug_unsigned(uint64_t value) {
  char digits[24];
  snprintf(digits, sizeof digits, "%llu", (unsigned long long)value);
  t_debug_c(digits);
}

/* The shortest decimal that reads back as the same value, written so that
   it reads as a float: with a point or an exponent. Both C libraries round
   correctly, so this is the same text on every platform. */
static t_usize t_real_text(double value, int float32, uint8_t *bytes) {
  char text[40];
  if (value != value) {
    strcpy(text, "NaN");
  } else if (value == 1.0 / 0.0) {
    strcpy(text, "infinity");
  } else if (value == -1.0 / 0.0) {
    strcpy(text, "-infinity");
  } else {
    for (int digits = 1; digits <= 17; digits++) {
      snprintf(text, sizeof text, "%.*g", digits, value);
      if (float32 ? (float)strtod(text, NULL) == (float)value : strtod(text, NULL) == value) break;
    }
    if (strpbrk(text, ".e") == NULL) strcat(text, ".0");
  }
  t_usize length = strlen(text);
  memcpy(bytes, text, length);
  return length;
}

t_usize t_runtime_float32_text(float value, uint8_t *bytes) { return t_real_text(value, 1, bytes); }
t_usize t_runtime_float64_text(double value, uint8_t *bytes) { return t_real_text(value, 0, bytes); }

static void t_debug_real(double value, int float32) {
  uint8_t text[40];
  t_runtime_debug_text(text, t_real_text(value, float32, text));
}

void t_runtime_debug_float32(float value) { t_debug_real(value, 1); }
void t_runtime_debug_float64(double value) { t_debug_real(value, 0); }
void t_runtime_debug_bool(uint8_t value) { t_debug_c(value ? "true" : "false"); }

/* A character as Truss writes it in a string, with the escapes of an
   ordinary string for what it cannot show. */
static void t_debug_escaped(uint32_t code, char quote) {
  char text[16];
  if (code == '\\') t_debug_c("\\\\");
  else if (code == (uint32_t)quote) { text[0] = '\\'; text[1] = quote; text[2] = 0; t_debug_c(text); }
  else if (code == '\n') t_debug_c("\\n");
  else if (code == '\t') t_debug_c("\\t");
  else if (code == '\r') t_debug_c("\\r");
  else if (code == 0) t_debug_c("\\0");
  else if (code == '$') t_debug_c("$");
  else if (code < 0x20 || code == 0x7f) { snprintf(text, sizeof text, "\\u{%X}", code); t_debug_c(text); }
  else {
    uint8_t bytes[4];
    t_usize count;
    if (code < 0x80) { bytes[0] = (uint8_t)code; count = 1; }
    else if (code < 0x800) { bytes[0] = (uint8_t)(0xc0 | (code >> 6)); bytes[1] = (uint8_t)(0x80 | (code & 0x3f)); count = 2; }
    else if (code < 0x10000) {
      bytes[0] = (uint8_t)(0xe0 | (code >> 12)); bytes[1] = (uint8_t)(0x80 | ((code >> 6) & 0x3f));
      bytes[2] = (uint8_t)(0x80 | (code & 0x3f)); count = 3;
    } else {
      bytes[0] = (uint8_t)(0xf0 | (code >> 18)); bytes[1] = (uint8_t)(0x80 | ((code >> 12) & 0x3f));
      bytes[2] = (uint8_t)(0x80 | ((code >> 6) & 0x3f)); bytes[3] = (uint8_t)(0x80 | (code & 0x3f)); count = 4;
    }
    t_runtime_debug_text(bytes, count);
  }
}

void t_runtime_debug_character(uint32_t value) {
  t_debug_c("Character\"");
  t_debug_escaped(value, '"');
  t_debug_c("\"");
}

/* A string's bytes are UTF-8, which the type checker guarantees. */
void t_runtime_debug_string(const uint8_t *bytes, t_usize count) {
  t_debug_c("\"");
  t_usize i = 0;
  while (i < count) {
    uint32_t code = bytes[i];
    t_usize length = code < 0x80 ? 1 : code < 0xe0 ? 2 : code < 0xf0 ? 3 : 4;
    if (length > 1) code &= (uint32_t)(0x7f >> length);
    for (t_usize k = 1; k < length && i + k < count; k++) code = (code << 6) | (bytes[i + k] & 0x3f);
    if (code == '$' && i + 1 < count && bytes[i + 1] == '{') t_debug_c("\\$");
    else t_debug_escaped(code, '"');
    i += length;
  }
  t_debug_c("\"");
}

uint8_t *t_runtime_debug_bytes(void) { return (uint8_t *)(t_debug_buffer ? t_debug_buffer : (char *)""); }
t_usize t_runtime_debug_length(void) { return t_debug_used; }
|}

let runner =
  {|
/* The test runner. It forks one worker per core after startup, so the
   workers share its loaded code, and hands each a test at a time over a
   pipe. A worker reports each test's end, and any echo output, as records
   on another pipe. A worker that fails, panics, reaches a todo, or dies
   ends; the runner records why and starts another. A test that runs past
   the time limit is killed. Each result is printed as soon as its test
   ends, with how long it ran, and a line as each test starts, so a driver
   can show progress; results come in the order tests end, and each names
   its test by number. */

typedef void (*t_test)(void);

struct t_result {
  uint8_t outcome;
  uint8_t done;
  uint64_t microseconds;
  char *message;
  size_t message_length;
  char *echo;
  size_t echo_length;
};

struct t_worker {
  pid_t pid;
  int commands;
  int reports;
  int64_t test;
  uint8_t ending; /* It reported a failure, so it is about to exit and gets no more tests. */
  uint64_t started; /* In microseconds. */
  uint8_t *buffer;
  size_t used;
  size_t capacity;
};

enum { t_timed_out = 5, t_crashed = 6 };

static uint64_t t_microseconds(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000 + (uint64_t)now.tv_nsec / 1000;
}

static void *t_runner_allocate(size_t size) {
  void *pointer = malloc(size ? size : 1);
  if (pointer == NULL) t_out_of_memory();
  return pointer;
}

static void t_append(char **text, size_t *length, const void *bytes, size_t count) {
  char *grown = realloc(*text, *length + count + 1);
  if (grown == NULL) t_out_of_memory();
  memcpy(grown + *length, bytes, count);
  *length += count;
  grown[*length] = 0;
  *text = grown;
}

static void t_worker_main(const t_test *tests, int commands) {
  for (;;) {
    uint32_t index;
    size_t got = 0;
    while (got < sizeof index) {
      ssize_t n = read(commands, (char *)&index + got, sizeof index - got);
      if (n < 0 && errno == EINTR) continue;
      if (n <= 0) _exit(0);
      got += (size_t)n;
    }
    t_current_test = index;
    t_usize live = t_live_blocks;
    tests[index]();
    if (t_live_blocks != live) {
      t_text_length = 0;
      t_usize left = t_live_blocks - live;
      t_text_string("compiler bug: the test left ");
      t_text_number((uint64_t)left);
      t_text_string(left == 1 ? " block allocated" : " blocks allocated");
      t_end(t_panicked, "", 101);
    }
    t_text_length = 0;
    t_record(t_passed);
  }
}

/* A new worker closes the runner's ends of every other worker's pipes,
   which it inherits, so that a worker sees the end of its commands when the
   runner closes them, and only the runner reads reports. */
static void t_spawn(struct t_worker *workers, uint32_t width, struct t_worker *worker, const t_test *tests) {
  int commands[2], reports[2];
  if (pipe(commands) != 0 || pipe(reports) != 0) t_out_of_memory();
  pid_t pid = fork();
  if (pid == 0) {
    for (uint32_t w = 0; w < width; w++) {
      if (&workers[w] != worker && workers[w].pid > 0) {
        close(workers[w].commands);
        close(workers[w].reports);
      }
    }
    close(commands[1]);
    close(reports[0]);
    t_report = reports[1];
    t_worker_main(tests, commands[0]);
  }
  close(commands[0]);
  close(reports[1]);
  worker->pid = pid;
  worker->commands = commands[1];
  worker->reports = reports[0];
  worker->test = -1;
  worker->ending = 0;
  worker->used = 0;
}

static const char *t_outcome_names[] = {"passed", "failed", "panicked", "incomplete", "echoed", "timed_out", "crashed"};

static void t_print_block(const char *label, const char *text, size_t length) {
  t_text_length = 0;
  t_text_string(label);
  t_text_string(" ");
  t_text_number(length);
  t_text_string("\n");
  t_write_all(1, t_text, t_text_length);
  t_write_all(1, text, length);
  t_write_all(1, "\n", 1);
}

/* Records a test's end, and prints it at once: its message and its echo
   output, then a line with its number, outcome, and duration, which ends
   the record, so a reader knows a record is whole when its line arrives. */
static void t_finish(struct t_result *results, uint32_t test, uint64_t started, uint8_t outcome, const char *message, size_t length) {
  struct t_result *result = &results[test];
  result->outcome = outcome;
  result->done = 1;
  result->microseconds = t_microseconds() - started;
  if (length > 0) t_append(&result->message, &result->message_length, message, length);
  if (result->message_length > 0) t_print_block("message", result->message, result->message_length);
  if (result->echo_length > 0) t_print_block("echo", result->echo, result->echo_length);
  t_text_length = 0;
  t_text_string("test ");
  t_text_number(test);
  t_text_string(" ");
  t_text_string(t_outcome_names[outcome]);
  t_text_string(" ");
  t_text_number(result->microseconds);
  t_text_string("\n");
  t_write_all(1, t_text, t_text_length);
}

/* Takes the complete records out of a worker's buffer. */
static void t_take_records(struct t_worker *worker, struct t_result *results, uint32_t *finished) {
  size_t at = 0;
  while (worker->used - at >= 9) {
    uint32_t test, length;
    memcpy(&test, worker->buffer + at, 4);
    uint8_t kind = worker->buffer[at + 4];
    memcpy(&length, worker->buffer + at + 5, 4);
    if (worker->used - at - 9 < length) break;
    const char *text = (const char *)worker->buffer + at + 9;
    if (kind == t_echoed) {
      t_append(&results[test].echo, &results[test].echo_length, text, length);
      t_append(&results[test].echo, &results[test].echo_length, "\n", 1);
    } else if (!results[test].done) {
      t_finish(results, test, worker->started, kind, text, length);
      *finished += 1;
      worker->test = -1;
      if (kind != t_passed) worker->ending = 1;
    }
    at += 9 + length;
  }
  memmove(worker->buffer, worker->buffer + at, worker->used - at);
  worker->used -= at;
}

/* Waits for a worker that has ended, and records its test as failed if it
   ended without saying why. */
static void t_bury(struct t_worker *worker, struct t_result *results, uint32_t *finished, uint8_t outcome) {
  int status = 0;
  close(worker->commands);
  close(worker->reports);
  waitpid(worker->pid, &status, 0);
  if (worker->test >= 0 && !results[worker->test].done) {
    t_text_length = 0;
    if (outcome == t_timed_out) {
      t_text_string("ran past the time limit");
    } else if (WIFSIGNALED(status)) {
      t_text_string("ended by signal ");
      t_text_number((uint64_t)WTERMSIG(status));
    } else {
      t_text_string("ended with status ");
      t_text_number((uint64_t)WEXITSTATUS(status));
    }
    /* t_finish builds its line in t_text, so the message is copied out first. */
    char *message = t_runner_allocate(t_text_length);
    size_t length = t_text_length;
    memcpy(message, t_text, length);
    t_finish(results, (uint32_t)worker->test, worker->started, outcome, message, length);
    free(message);
    *finished += 1;
  }
  worker->pid = -1;
}

int t_runtime_run_tests(uint32_t count, const t_test *tests, uint32_t time_limit) {
  signal(SIGPIPE, SIG_IGN);
  struct t_result *results = t_runner_allocate(sizeof *results * (count ? count : 1));
  memset(results, 0, sizeof *results * (count ? count : 1));
  long cores = sysconf(_SC_NPROCESSORS_ONLN);
  uint32_t width = cores > 0 ? (uint32_t)cores : 1;
  if (width > count) width = count;
  struct t_worker *workers = t_runner_allocate(sizeof *workers * (width ? width : 1));
  for (uint32_t w = 0; w < width; w++) {
    workers[w].capacity = 65536;
    workers[w].buffer = t_runner_allocate(workers[w].capacity);
    workers[w].pid = -1;
  }
  for (uint32_t w = 0; w < width; w++) {
    t_spawn(workers, width, &workers[w], tests);
  }
  uint32_t next = 0, finished = 0;
  struct pollfd *polls = t_runner_allocate(sizeof *polls * (width ? width : 1));
  while (finished < count) {
    for (uint32_t w = 0; w < width; w++) {
      if (workers[w].pid < 0 && next < count) t_spawn(workers, width, &workers[w], tests);
      if (workers[w].pid >= 0 && !workers[w].ending && workers[w].test < 0 && next < count) {
        uint32_t index = next++;
        workers[w].test = index;
        workers[w].started = t_microseconds();
        t_write_all(workers[w].commands, &index, sizeof index);
        t_text_length = 0;
        t_text_string("start ");
        t_text_number(index);
        t_text_string("\n");
        t_write_all(1, t_text, t_text_length);
      }
    }
    uint64_t now = t_microseconds();
    int wait = -1;
    for (uint32_t w = 0; w < width; w++) {
      polls[w].fd = workers[w].pid >= 0 ? workers[w].reports : -1;
      polls[w].events = POLLIN;
      polls[w].revents = 0;
      if (workers[w].pid >= 0 && workers[w].test >= 0) {
        uint64_t deadline = workers[w].started + (uint64_t)time_limit * 1000;
        int left = deadline > now ? (int)((deadline - now + 999) / 1000) : 0;
        if (wait < 0 || left < wait) wait = left;
      }
    }
    if (poll(polls, width, wait) < 0 && errno != EINTR) break;
    for (uint32_t w = 0; w < width; w++) {
      struct t_worker *worker = &workers[w];
      if (worker->pid < 0) continue;
      if (polls[w].revents & (POLLIN | POLLHUP)) {
        if (worker->capacity - worker->used < 65536) {
          worker->capacity *= 2;
          worker->buffer = realloc(worker->buffer, worker->capacity);
          if (worker->buffer == NULL) t_out_of_memory();
        }
        ssize_t n = read(worker->reports, worker->buffer + worker->used, worker->capacity - worker->used);
        if (n > 0) {
          worker->used += (size_t)n;
          t_take_records(worker, results, &finished);
        } else if (n == 0 || errno != EINTR) {
          t_take_records(worker, results, &finished);
          t_bury(worker, results, &finished, t_crashed);
          continue;
        }
      }
      if (worker->test >= 0 && t_microseconds() - worker->started > (uint64_t)time_limit * 1000) {
        kill(worker->pid, SIGKILL);
        t_bury(worker, results, &finished, t_timed_out);
      }
    }
  }
  for (uint32_t w = 0; w < width; w++) {
    if (workers[w].pid >= 0) {
      close(workers[w].commands);
      close(workers[w].reports);
      waitpid(workers[w].pid, NULL, 0);
    }
  }
  int failures = 0;
  for (uint32_t i = 0; i < count; i++) {
    if (results[i].outcome != t_passed) failures += 1;
  }
  return failures > 0 ? 1 : 0;
}
|}

let runtime (target : Memory_layout.target) ~tests =
  String.concat ""
    [
      (if tests then "#define T_TESTS 1\n" else "");
      headers;
      (if target.usize_bytes = 8 then "typedef uint64_t t_usize;\ntypedef int64_t t_isize;\n"
       else "typedef uint32_t t_usize;\ntypedef int32_t t_isize;\n");
      Emit_c.anchor_struct;
      failing;
      allocation;
      (if tests then runner else "");
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

let tests_calling ~time_limit tests =
  let declarations =
    String.concat "" (List.map (fun symbol -> Printf.sprintf "void %s(void);\n" symbol) tests)
  in
  let table = String.concat ", " tests in
  Printf.sprintf
    "typedef __UINT32_TYPE__ uint32_t;\n\
     void t_runtime_install(void);\n\
     typedef void (*t_test)(void);\n\
     int t_runtime_run_tests(uint32_t count, const t_test *tests, uint32_t time_limit);\n\
     %sstatic const t_test t_tests[] = { %s };\n\
     int main(int count, char **arguments) {\n\
    \  (void)count;\n\
    \  (void)arguments;\n\
    \  t_runtime_install();\n\
    \  return t_runtime_run_tests(%d, t_tests, %d);\n\
     }\n"
    declarations
    (if tests = [] then "0" else table)
    (List.length tests) time_limit

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
