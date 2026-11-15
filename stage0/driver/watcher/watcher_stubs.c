#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

struct paths {
  char **items;
  size_t count;
  size_t capacity;
  int is_overflowed;
};

static void paths_add(struct paths *paths, const char *path, size_t length) {
  if (paths->count == paths->capacity) {
    size_t capacity = paths->capacity == 0 ? 64 : 2 * paths->capacity;
    char **items = realloc(paths->items, capacity * sizeof(char *));
    if (items == NULL) {
      paths->is_overflowed = 1;
      return;
    }
    paths->items = items;
    paths->capacity = capacity;
  }
  char *copy = malloc(length + 1);
  if (copy == NULL) {
    paths->is_overflowed = 1;
    return;
  }
  memcpy(copy, path, length);
  copy[length] = '\0';
  paths->items[paths->count++] = copy;
}

static value paths_take(struct paths *paths) {
  CAMLparam0();
  CAMLlocal3(result, list, cell);
  list = Val_emptylist;
  for (size_t index = paths->count; index > 0; index--) {
    cell = caml_alloc_small(2, Tag_cons);
    Field(cell, 0) = Val_unit;
    Field(cell, 1) = list;
    list = cell;
    Store_field(list, 0, caml_copy_string(paths->items[index - 1]));
    free(paths->items[index - 1]);
  }
  result = caml_alloc_tuple(2);
  Store_field(result, 0, list);
  Store_field(result, 1, Val_bool(paths->is_overflowed));
  paths->count = 0;
  paths->is_overflowed = 0;
  CAMLreturn(result);
}

static void paths_free(struct paths *paths) {
  for (size_t index = 0; index < paths->count; index++) free(paths->items[index]);
  free(paths->items);
}

#if defined(__APPLE__)

#include <CoreServices/CoreServices.h>
#include <dispatch/dispatch.h>
#include <pthread.h>

struct watcher {
  FSEventStreamRef stream;
  dispatch_queue_t queue;
  pthread_mutex_t lock;
  struct paths pending;
  int signal[2];
};

static void on_events(ConstFSEventStreamRef stream, void *context, size_t count, void *event_paths,
                      const FSEventStreamEventFlags flags[], const FSEventStreamEventId ids[]) {
  (void)stream;
  (void)ids;
  struct watcher *watcher = context;
  char **paths = event_paths;
  const FSEventStreamEventFlags lost = kFSEventStreamEventFlagMustScanSubDirs |
                                       kFSEventStreamEventFlagUserDropped |
                                       kFSEventStreamEventFlagKernelDropped |
                                       kFSEventStreamEventFlagRootChanged;
  pthread_mutex_lock(&watcher->lock);
  for (size_t index = 0; index < count; index++) {
    if (flags[index] & lost) watcher->pending.is_overflowed = 1;
    paths_add(&watcher->pending, paths[index], strlen(paths[index]));
  }
  pthread_mutex_unlock(&watcher->lock);
  char byte = 0;
  ssize_t written = write(watcher->signal[1], &byte, 1);
  (void)written;
}

static struct watcher *watcher_open(const char *root) {
  struct watcher *watcher = calloc(1, sizeof(struct watcher));
  if (watcher == NULL) return NULL;
  if (pipe(watcher->signal) != 0) {
    free(watcher);
    return NULL;
  }
  for (int end = 0; end < 2; end++) {
    fcntl(watcher->signal[end], F_SETFL, fcntl(watcher->signal[end], F_GETFL) | O_NONBLOCK);
    fcntl(watcher->signal[end], F_SETFD, FD_CLOEXEC);
  }
  pthread_mutex_init(&watcher->lock, NULL);
  CFStringRef path = CFStringCreateWithCString(NULL, root, kCFStringEncodingUTF8);
  CFArrayRef paths = CFArrayCreate(NULL, (const void **)&path, 1, &kCFTypeArrayCallBacks);
  FSEventStreamContext context = {0, watcher, NULL, NULL, NULL};
  watcher->stream = FSEventStreamCreate(
      NULL, on_events, &context, paths, kFSEventStreamEventIdSinceNow, 0.01,
      kFSEventStreamCreateFlagFileEvents | kFSEventStreamCreateFlagNoDefer);
  CFRelease(paths);
  CFRelease(path);
  watcher->queue = dispatch_queue_create("truss.watcher", DISPATCH_QUEUE_SERIAL);
  FSEventStreamSetDispatchQueue(watcher->stream, watcher->queue);
  if (!FSEventStreamStart(watcher->stream)) {
    FSEventStreamInvalidate(watcher->stream);
    FSEventStreamRelease(watcher->stream);
    dispatch_release(watcher->queue);
    close(watcher->signal[0]);
    close(watcher->signal[1]);
    free(watcher);
    return NULL;
  }
  return watcher;
}

static int watcher_is_recursive(void) { return 1; }

static int watcher_add(struct watcher *watcher, const char *directory) {
  (void)watcher;
  (void)directory;
  return 0;
}

static int watcher_descriptor(struct watcher *watcher) { return watcher->signal[0]; }

static value watcher_take(struct watcher *watcher) {
  char bytes[256];
  while (read(watcher->signal[0], bytes, sizeof bytes) > 0) {
  }
  struct paths taken;
  pthread_mutex_lock(&watcher->lock);
  taken = watcher->pending;
  memset(&watcher->pending, 0, sizeof watcher->pending);
  pthread_mutex_unlock(&watcher->lock);
  value result = paths_take(&taken);
  paths_free(&taken);
  return result;
}

static void watcher_close(struct watcher *watcher) {
  FSEventStreamStop(watcher->stream);
  FSEventStreamInvalidate(watcher->stream);
  FSEventStreamRelease(watcher->stream);
  dispatch_release(watcher->queue);
  close(watcher->signal[0]);
  close(watcher->signal[1]);
  pthread_mutex_destroy(&watcher->lock);
  paths_free(&watcher->pending);
  free(watcher);
}

#elif defined(__linux__)

#include <sys/inotify.h>

struct watcher {
  int descriptor;
  char **directories;
  int capacity;
  struct paths pending;
};

static const uint32_t watched = IN_CLOSE_WRITE | IN_MODIFY | IN_CREATE | IN_DELETE |
                                IN_MOVED_FROM | IN_MOVED_TO | IN_DELETE_SELF;

static struct watcher *watcher_open(const char *root) {
  (void)root;
  struct watcher *watcher = calloc(1, sizeof(struct watcher));
  if (watcher == NULL) return NULL;
  watcher->descriptor = inotify_init1(IN_NONBLOCK | IN_CLOEXEC);
  if (watcher->descriptor < 0) {
    free(watcher);
    return NULL;
  }
  return watcher;
}

static int watcher_is_recursive(void) { return 0; }

static int watcher_add(struct watcher *watcher, const char *directory) {
  int watch = inotify_add_watch(watcher->descriptor, directory, watched | IN_ONLYDIR);
  if (watch < 0) return errno == ENOENT || errno == ENOTDIR ? 0 : -1;
  if (watch >= watcher->capacity) {
    int capacity = watcher->capacity == 0 ? 64 : watcher->capacity;
    while (capacity <= watch) capacity *= 2;
    char **directories = realloc(watcher->directories, capacity * sizeof(char *));
    if (directories == NULL) return -1;
    memset(directories + watcher->capacity, 0, (capacity - watcher->capacity) * sizeof(char *));
    watcher->directories = directories;
    watcher->capacity = capacity;
  }
  free(watcher->directories[watch]);
  watcher->directories[watch] = strdup(directory);
  return 0;
}

static int watcher_descriptor(struct watcher *watcher) { return watcher->descriptor; }

static void record(struct watcher *watcher, const struct inotify_event *event) {
  if (event->mask & IN_Q_OVERFLOW) {
    watcher->pending.is_overflowed = 1;
    return;
  }
  if (event->wd < 0 || event->wd >= watcher->capacity) return;
  char *directory = watcher->directories[event->wd];
  if (directory == NULL) return;
  if (event->mask & IN_IGNORED) {
    free(directory);
    watcher->directories[event->wd] = NULL;
    return;
  }
  if (event->len == 0) {
    paths_add(&watcher->pending, directory, strlen(directory));
    return;
  }
  size_t directory_length = strlen(directory);
  size_t name_length = strlen(event->name);
  char *path = malloc(directory_length + 1 + name_length + 1);
  if (path == NULL) {
    watcher->pending.is_overflowed = 1;
    return;
  }
  memcpy(path, directory, directory_length);
  path[directory_length] = '/';
  memcpy(path + directory_length + 1, event->name, name_length + 1);
  paths_add(&watcher->pending, path, directory_length + 1 + name_length);
  free(path);
}

static value watcher_take(struct watcher *watcher) {
  char buffer[64 * 1024] __attribute__((aligned(__alignof__(struct inotify_event))));
  for (;;) {
    ssize_t length = read(watcher->descriptor, buffer, sizeof buffer);
    if (length <= 0) break;
    for (char *at = buffer; at < buffer + length;) {
      const struct inotify_event *event = (const struct inotify_event *)at;
      record(watcher, event);
      at += sizeof(struct inotify_event) + event->len;
    }
  }
  return paths_take(&watcher->pending);
}

static void watcher_close(struct watcher *watcher) {
  close(watcher->descriptor);
  for (int watch = 0; watch < watcher->capacity; watch++) free(watcher->directories[watch]);
  free(watcher->directories);
  paths_free(&watcher->pending);
  free(watcher);
}

#else
#error "the watcher supports only Linux and macOS"
#endif

#define Watcher_val(handle) (*((struct watcher **)Data_custom_val(handle)))

static struct custom_operations watcher_operations = {
    "truss.watcher",           custom_finalize_default,  custom_compare_default,
    custom_hash_default,       custom_serialize_default, custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

static struct watcher *open_watcher(value handle) {
  struct watcher *watcher = Watcher_val(handle);
  if (watcher == NULL) caml_failwith("the watcher is stopped");
  return watcher;
}

value truss_watcher_open(value root) {
  CAMLparam1(root);
  CAMLlocal1(handle);
  struct watcher *watcher = watcher_open(String_val(root));
  if (watcher == NULL) caml_failwith("the watcher cannot start");
  handle = caml_alloc_custom(&watcher_operations, sizeof(struct watcher *), 0, 1);
  Watcher_val(handle) = watcher;
  CAMLreturn(handle);
}

value truss_watcher_is_recursive(value unit) {
  (void)unit;
  return Val_bool(watcher_is_recursive());
}

value truss_watcher_add(value handle, value directory) {
  CAMLparam2(handle, directory);
  if (watcher_add(open_watcher(handle), String_val(directory)) != 0)
    caml_failwith("the watcher cannot watch a directory");
  CAMLreturn(Val_unit);
}

value truss_watcher_descriptor(value handle) {
  return Val_int(watcher_descriptor(open_watcher(handle)));
}

value truss_watcher_take(value handle) {
  CAMLparam1(handle);
  CAMLreturn(watcher_take(open_watcher(handle)));
}

value truss_watcher_close(value handle) {
  CAMLparam1(handle);
  struct watcher *watcher = Watcher_val(handle);
  if (watcher != NULL) {
    Watcher_val(handle) = NULL;
    watcher_close(watcher);
  }
  CAMLreturn(Val_unit);
}
