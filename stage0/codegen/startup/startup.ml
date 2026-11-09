let runtime (target : Memory_layout.target) =
  String.concat ""
    [
      (* Strict C11 hides POSIX functions such as [posix_memalign] and
         [sigaltstack] in glibc unless they are asked for. *)
      "#define _DEFAULT_SOURCE\n";
      "#include <stddef.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n";
      "#include <signal.h>\n#include <errno.h>\n#include <unistd.h>\n";
      Printf.sprintf "typedef %s t_usize;\n"
        (if target.usize_bytes = 8 then "uint64_t" else "uint32_t");
      Emit_c.anchor_struct;
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

static void t_write_text(int descriptor, const char *text) {
  t_write_all(descriptor, text, strlen(text));
}

static void t_write_number(int descriptor, uint64_t number) {
  char digits[20];
  size_t count = 0;
  do {
    digits[sizeof digits - 1 - count] = (char)('0' + number % 10);
    number /= 10;
    count += 1;
  } while (number > 0);
  t_write_all(descriptor, digits + sizeof digits - count, count);
}

_Noreturn void t_runtime_panic(const uint8_t *message, t_usize length,
                               const struct t_anchor *anchor, uint32_t line, uint32_t column) {
  t_write_text(2, "panic: ");
  t_write_all(2, message, length);
  t_write_text(2, "\n  at ");
  if (anchor) {
    t_write_all(2, anchor->path, anchor->path_length);
    t_write_text(2, ":");
    t_write_number(2, (uint64_t)anchor->line + line);
  } else {
    t_write_text(2, "generated code:");
    t_write_number(2, line);
  }
  t_write_text(2, ":");
  t_write_number(2, column);
  t_write_text(2, "\n");
  _exit(101);
}

_Noreturn void t_runtime_compiler_bug(void) {
  t_write_text(2, "compiler bug: reached code the prover showed unreachable\n");
  abort();
}

static _Noreturn void t_out_of_memory(void) {
  t_write_text(2, "out of memory\n");
  abort();
}

void *t_runtime_allocate(t_usize size, t_usize alignment) {
  void *pointer = NULL;
  if (size == 0) size = 1;
  if (alignment <= 16) {
    pointer = malloc(size);
  } else if (posix_memalign(&pointer, alignment, size) != 0) {
    pointer = NULL;
  }
  if (pointer == NULL) t_out_of_memory();
  return pointer;
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
  free(pointer);
  return moved;
}

void t_runtime_free(void *pointer) {
  free(pointer);
}

static char t_signal_stack[65536];

static void t_stack_overflow(int signal) {
  (void)signal;
  t_write_text(2, "stack overflow\n");
  _exit(101);
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
|};
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
