(* The runtime is C, kept here as text. It has three parts: writing and
   failing, which every program uses; allocation; and what a test program
   gives the runner, which is Truss in the standard library. *)

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
