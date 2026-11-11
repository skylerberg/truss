type os = Linux | Macos
type architecture = X86_64 | Arm64
type system = { os : os; architecture : architecture }

let oses = [ Linux; Macos ]
let architectures = [ X86_64; Arm64 ]
let os_name = function Linux -> "Linux" | Macos -> "macOS"
let architecture_name = function X86_64 -> "x86-64" | Arm64 -> "ARM64"
let system_name system = os_name system.os ^ " on " ^ architecture_name system.architecture

let host =
  let os =
    if Built_for.system = "macosx" then Some Macos
    else if String.starts_with ~prefix:"linux" Built_for.system then Some Linux
    else None
  and architecture =
    match Built_for.architecture with "amd64" -> Some X86_64 | "arm64" -> Some Arm64 | _ -> None
  in
  match (os, architecture) with
  | Some os, Some architecture -> Some { os; architecture }
  | _ -> None

type scalar = UInt8 | Int32 | UInt32 | Int64 | UInt64 | USize | ISize | Float32 | Float64

type number =
  | O_rdonly
  | O_wronly
  | O_creat
  | O_trunc
  | O_cloexec
  | Eintr
  | Enoent
  | Eacces
  | Eio
  | Einval
  | Clock_realtime
  | Clock_monotonic
  | Sc_nprocessors_onln
  | Pollin
  | Pollhup
  | Sigkill
  | O_rdwr
  | O_append
  | O_excl
  | Seek_set
  | Seek_cur
  | Seek_end
  | Eperm
  | Ebadf
  | Eexist
  | Enotdir
  | Eisdir
  | Enfile
  | Emfile
  | Enospc
  | Epipe
  | Enosys
  | Enotempty
  | Enotsup
  | Eaddrinuse
  | Eaddrnotavail
  | Enetunreach
  | Econnaborted
  | Econnreset
  | Enotconn
  | Etimedout
  | Econnrefused
  | Ehostunreach
  | Stat_size
  | Stat_mode_offset
  | Stat_mode_size
  | Stat_length_offset
  | Stat_accessed_offset
  | Stat_modified_offset
  | Stat_created_offset
  | S_ifmt
  | S_ifreg
  | S_ifdir
  | S_iflnk
  | At_fdcwd
  | Utime_omit
  | Path_max
  | F_dupfd_cloexec
  | F_setfd
  | Fd_cloexec
  | Spawn_file_actions_size
  | Sigusr1
  | Sigusr2
  | O_directory
  | Dirent_length_offset
  | Dirent_kind_offset
  | Dirent_name_offset
  | Dt_unknown
  | Dt_dir
  | Dt_reg
  | Dt_lnk
  | Attr_bit_map_count
  | Attr_cmn_returned_attrs
  | Attr_cmn_name
  | Attr_cmn_objtype
  | Vreg
  | Vdir
  | Vlnk
  | Termios_size
  | Termios_iflag_offset
  | Termios_oflag_offset
  | Termios_cflag_offset
  | Termios_lflag_offset
  | Termios_flag_size
  | Termios_cc_offset
  | Vmin
  | Vtime
  | Tcsaflush
  | Tiocgwinsz
  | Icanon
  | Echo
  | Isig
  | Iexten
  | Ixon
  | Icrnl
  | Brkint
  | Inpck
  | Istrip
  | Opost
  | Cs8
  | Af_inet
  | Af_inet6
  | Sock_stream
  | Sock_dgram
  | Sol_socket
  | So_reuseaddr
  | So_rcvtimeo
  | So_sndtimeo
  | So_error
  | Shut_rd
  | Shut_wr
  | Shut_rdwr
  | Ipproto_ipv6
  | Ipv6_v6only
  | O_nonblock
  | F_getfl
  | F_setfl
  | Einprogress
  | Eagain
  | Pollout
  | Sockaddr_family_offset
  | Sockaddr_family_size

type extent =
  | Counted of { by : string; each : int }
  | Exactly of int
  | Number of number
  | Through_zero

type passes =
  | Value of scalar
  | Elements of scalar * extent
  | Room of scalar * extent
  | Elements_to_change of scalar * extent
  | Written of scalar * string list
  | Always of int
  | Fixed of number

type result = Returns of scalar | Points_at of scalar | Text | Never
type signature = { parameters : (string * passes) list; result : result; at_most : string option }

type declaration = {
  symbol : string;
  returns : string;
  takes : string list;
  variadic_from : int option;
}

type function_ =
  | Write
  | Read
  | Open
  | Close
  | Errno
  | Clock_gettime
  | Getentropy
  | Getenv
  | Posix_spawnp
  | Waitpid
  | Snprintf
  | Strtod
  | Strtof
  | Fork
  | Pipe
  | Poll
  | Kill
  | Sysconf
  | Exit
  | Pread
  | Pwrite
  | Lseek
  | Ftruncate
  | Fsync
  | Fstat
  | Stat
  | Lstat
  | Mkdir
  | Remove
  | Rename
  | Symlink
  | Link
  | Chmod
  | Utimensat
  | Readlink
  | Realpath
  | Getcwd
  | Gethostname
  | Getpid
  | Proc_pidpath
  | Fcntl_dupfd_cloexec
  | Fcntl_setfd_cloexec
  | Posix_spawn_file_actions_init
  | Posix_spawn_file_actions_destroy
  | Posix_spawn_file_actions_adddup2
  | Posix_spawn_file_actions_addopen
  | Posix_spawn_file_actions_addchdir
  | Getdents64
  | Getattrlistbulk
  | Ioctl_tiocgwinsz
  | Tcgetattr
  | Tcsetattr
  | Socket
  | Bind
  | Connect
  | Listen
  | Accept
  | Getsockname
  | Getpeername
  | Shutdown
  | Setsockopt
  | Getsockopt
  | Sendto
  | Recvfrom
  | Fcntl_getfl
  | Fcntl_setfl
  | Addresses_of_host
  | Signals_wait
  | Descriptor_watch
  | Descriptor_wait
  | Sleep
  | Tasks_open
  | Tasks_join
  | Tasks_cancel
  | Tasks_cancelled
  | Tasks_watch
  | Tasks_wait
  | Tasks_wake
  | Tasks_lock
  | Tasks_unlock
  | Tasks_yield

let functions =
  [
    Write;
    Read;
    Open;
    Close;
    Errno;
    Clock_gettime;
    Getentropy;
    Getenv;
    Posix_spawnp;
    Waitpid;
    Snprintf;
    Strtod;
    Strtof;
    Fork;
    Pipe;
    Poll;
    Kill;
    Sysconf;
    Exit;
    Pread;
    Pwrite;
    Lseek;
    Ftruncate;
    Fsync;
    Fstat;
    Stat;
    Lstat;
    Mkdir;
    Remove;
    Rename;
    Symlink;
    Link;
    Chmod;
    Utimensat;
    Readlink;
    Realpath;
    Getcwd;
    Gethostname;
    Getpid;
    Proc_pidpath;
    Fcntl_dupfd_cloexec;
    Fcntl_setfd_cloexec;
    Posix_spawn_file_actions_init;
    Posix_spawn_file_actions_destroy;
    Posix_spawn_file_actions_adddup2;
    Posix_spawn_file_actions_addopen;
    Posix_spawn_file_actions_addchdir;
    Getdents64;
    Getattrlistbulk;
    Ioctl_tiocgwinsz;
    Tcgetattr;
    Tcsetattr;
    Socket;
    Bind;
    Connect;
    Listen;
    Accept;
    Getsockname;
    Getpeername;
    Shutdown;
    Setsockopt;
    Getsockopt;
    Sendto;
    Recvfrom;
    Fcntl_getfl;
    Fcntl_setfl;
    Addresses_of_host;
    Signals_wait;
    Descriptor_watch;
    Descriptor_wait;
    Sleep;
    Tasks_open;
    Tasks_join;
    Tasks_cancel;
    Tasks_cancelled;
    Tasks_watch;
    Tasks_wait;
    Tasks_wake;
    Tasks_lock;
    Tasks_unlock;
    Tasks_yield;
  ]

let function_name = function
  | Write -> "write"
  | Read -> "read"
  | Open -> "open"
  | Close -> "close"
  | Errno -> "errno"
  | Clock_gettime -> "clock_gettime"
  | Getentropy -> "getentropy"
  | Getenv -> "getenv"
  | Posix_spawnp -> "posix_spawnp"
  | Waitpid -> "waitpid"
  | Snprintf -> "snprintf"
  | Strtod -> "strtod"
  | Strtof -> "strtof"
  | Fork -> "fork"
  | Pipe -> "pipe"
  | Poll -> "poll"
  | Kill -> "kill"
  | Sysconf -> "sysconf"
  | Exit -> "exit_at_once"
  | Pread -> "pread"
  | Pwrite -> "pwrite"
  | Lseek -> "lseek"
  | Ftruncate -> "ftruncate"
  | Fsync -> "fsync"
  | Fstat -> "fstat"
  | Stat -> "stat"
  | Lstat -> "lstat"
  | Mkdir -> "mkdir"
  | Remove -> "remove"
  | Rename -> "rename"
  | Symlink -> "symlink"
  | Link -> "link"
  | Chmod -> "chmod"
  | Utimensat -> "utimensat"
  | Readlink -> "readlink"
  | Realpath -> "realpath"
  | Getcwd -> "getcwd"
  | Gethostname -> "gethostname"
  | Getpid -> "getpid"
  | Proc_pidpath -> "proc_pidpath"
  | Fcntl_dupfd_cloexec -> "fcntl_dupfd_cloexec"
  | Fcntl_setfd_cloexec -> "fcntl_setfd_cloexec"
  | Posix_spawn_file_actions_init -> "posix_spawn_file_actions_init"
  | Posix_spawn_file_actions_destroy -> "posix_spawn_file_actions_destroy"
  | Posix_spawn_file_actions_adddup2 -> "posix_spawn_file_actions_adddup2"
  | Posix_spawn_file_actions_addopen -> "posix_spawn_file_actions_addopen"
  | Posix_spawn_file_actions_addchdir -> "posix_spawn_file_actions_addchdir"
  | Getdents64 -> "getdents64"
  | Getattrlistbulk -> "getattrlistbulk"
  | Ioctl_tiocgwinsz -> "ioctl_tiocgwinsz"
  | Tcgetattr -> "tcgetattr"
  | Tcsetattr -> "tcsetattr"
  | Socket -> "socket"
  | Bind -> "bind"
  | Connect -> "connect"
  | Listen -> "listen"
  | Accept -> "accept"
  | Getsockname -> "getsockname"
  | Getpeername -> "getpeername"
  | Shutdown -> "shutdown"
  | Setsockopt -> "setsockopt"
  | Getsockopt -> "getsockopt"
  | Sendto -> "sendto"
  | Recvfrom -> "recvfrom"
  | Fcntl_getfl -> "fcntl_getfl"
  | Fcntl_setfl -> "fcntl_setfl"
  | Addresses_of_host -> "addresses_of_host"
  | Signals_wait -> "signals_wait"
  | Descriptor_watch -> "descriptor_watch"
  | Descriptor_wait -> "descriptor_wait"
  | Sleep -> "sleep"
  | Tasks_open -> "tasks_open"
  | Tasks_join -> "tasks_join"
  | Tasks_cancel -> "tasks_cancel"
  | Tasks_cancelled -> "tasks_cancelled"
  | Tasks_watch -> "tasks_watch"
  | Tasks_wait -> "tasks_wait"
  | Tasks_wake -> "tasks_wake"
  | Tasks_lock -> "tasks_lock"
  | Tasks_unlock -> "tasks_unlock"
  | Tasks_yield -> "tasks_yield"

(* Everything about a function, written once: each parameter with how Truss
   passes it and its C type on each system. Only the check reads the rest:
   [headers] declare the function; [layout] is what must hold of a structure
   it takes for the storage passed to be that structure; and [named] gives a
   parameter the type the headers call it by, where that is a name only the
   headers have and the C that is emitted says [void]. *)
type row = {
  symbol : system -> string;
  returns : system -> string;
  result : result;
  at_most : string option;
  on : os -> bool;
  parameters : (string * passes * (system -> string)) list;
  variadic_from : int option;
  headers : string list;
  layout : string list;
  named : (string * string) list;
}

let everywhere c (_ : system) = c
let by_os choose (system : system) = choose system.os
let size = everywhere "__SIZE_TYPE__"

(* The symbol of a function that fills a [struct stat]. On macOS for
   x86-64 the plain symbol is an old function that fills a smaller
   structure, and the one the headers call has this suffix. *)
let status_symbol name (system : system) =
  match system with { os = Macos; architecture = X86_64 } -> name ^ "$INODE64" | _ -> name

(* [mode_t], a file's permission bits. *)
let mode = by_os (function Linux -> "unsigned int" | Macos -> "unsigned short")

(* [off_t], a position in a file. *)
let offset = by_os (function Linux -> "long" | Macos -> "long long")

let describe function_ =
  let row ?(symbol = everywhere (function_name function_)) ?variadic_from ?(layout = [])
      ?(named = []) ?at_most ?(on = fun _ -> true) returns result parameters ~headers =
    { symbol; returns; result; at_most; on; parameters; variadic_from; headers; layout; named }
  in
  let counted by = Counted { by; each = 1 } in
  match function_ with
  | Write ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements (UInt8, counted "count"), everywhere "const void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Read ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room (UInt8, counted "count"), everywhere "void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Open ->
      row (everywhere "int") (Returns Int32) ~variadic_from:2
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("flags", Value Int32, everywhere "int");
          ("mode", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Close ->
      (* The runtime's function, which calls the C library's. The runtime
         keeps which descriptors it has registered for waiting, and a closed
         descriptor's number is given to the next one that is opened. *)
      row (everywhere "int32_t") (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int32_t") ]
        ~symbol:(everywhere "t_runtime_close") ~headers:[]
  | Errno ->
      (* The runtime's function, and not the C library's own, which a
         compiler may assume returns the same address on every call. A task
         that has parked may resume on another thread, where the address
         differs. *)
      row (everywhere "int *") (Points_at Int32) [] ~symbol:(everywhere "t_runtime_errno")
        ~headers:[]
  | Clock_gettime ->
      row (everywhere "int") (Returns Int32)
        [
          (* macOS makes [clockid_t] an enumeration with no negative member,
             which C gives the representation of this type. *)
          ("clock", Value Int32, by_os (function Linux -> "int" | Macos -> "unsigned int"));
          ("time", Written (Int64, [ "seconds"; "nanoseconds" ]), everywhere "struct timespec *");
        ]
        ~headers:[ "time.h" ]
        ~layout:
          [
            "sizeof(struct timespec) == 16";
            "__builtin_offsetof(struct timespec, tv_sec) == 0";
            "sizeof(((struct timespec *)0)->tv_sec) == 8";
            "__builtin_offsetof(struct timespec, tv_nsec) == 8";
            "sizeof(((struct timespec *)0)->tv_nsec) == 8";
          ]
  | Getentropy ->
      (* Eight random bytes are a random [UInt64], whatever order the system
         keeps a number's bytes in. *)
      row (everywhere "int") (Returns Int32)
        [
          ("buffer", Written (UInt64, [ "value" ]), everywhere "void *"); ("count", Always 8, size);
        ]
        ~headers:[ "sys/types.h"; "sys/random.h" ]
  | Getenv ->
      row (everywhere "char *") Text
        [ ("name", Elements (UInt8, Through_zero), everywhere "const char *") ]
        ~headers:[ "stdlib.h" ]
  | Posix_spawnp ->
      row (everywhere "int") (Returns Int32)
        [
          ("process", Written (Int32, [ "process" ]), everywhere "int *");
          ("program", Elements (UInt8, Through_zero), everywhere "const char *");
          ( "file_actions",
            Elements (UInt8, Number Spawn_file_actions_size),
            everywhere "const void *" );
          ("attributes", Always 0, everywhere "const void *");
          ("arguments", Elements (USize, Through_zero), everywhere "char *const *");
          ("environment", Elements (USize, Through_zero), everywhere "char *const *");
        ]
        ~named:
          [
            ("file_actions", "const posix_spawn_file_actions_t *");
            ("attributes", "const posix_spawnattr_t *");
          ]
        ~headers:[ "spawn.h" ]
        ~layout:[ "sizeof(char *) == sizeof(__SIZE_TYPE__)" ]
  | Waitpid ->
      row (everywhere "int") (Returns Int32)
        [
          ("process", Value Int32, everywhere "int");
          ("status", Written (Int32, [ "status" ]), everywhere "int *");
          ("options", Value Int32, everywhere "int");
        ]
        ~headers:[ "sys/wait.h" ]
  | Snprintf ->
      (* The one use: a float written with a number of digits, by a format
         that takes the two. *)
      row (everywhere "int") (Returns Int32) ~variadic_from:3
        [
          ("buffer", Room (UInt8, counted "size"), everywhere "char *");
          ("size", Value USize, size);
          ("format", Elements (UInt8, Through_zero), everywhere "const char *");
          ("precision", Value Int32, everywhere "int");
          ("value", Value Float64, everywhere "double");
        ]
        ~headers:[ "stdio.h" ]
  | Strtod ->
      row (everywhere "double") (Returns Float64)
        [
          ("text", Elements (UInt8, Through_zero), everywhere "const char *");
          ("end", Always 0, everywhere "char **");
        ]
        ~headers:[ "stdlib.h" ]
  | Strtof ->
      row (everywhere "float") (Returns Float32)
        [
          ("text", Elements (UInt8, Through_zero), everywhere "const char *");
          ("end", Always 0, everywhere "char **");
        ]
        ~headers:[ "stdlib.h" ]
  | Fork -> row (everywhere "int") (Returns Int32) [] ~headers:[ "unistd.h" ]
  | Pipe ->
      row (everywhere "int") (Returns Int32)
        [ ("ends", Written (Int32, [ "read_end"; "write_end" ]), everywhere "int *") ]
        ~headers:[ "unistd.h" ]
  | Poll ->
      (* A [pollfd] is its descriptor and then two numbers of half the
         size, what to wait for and what was found, which are the low and
         the high half of one [Int32] where the low byte comes first. *)
      row ~at_most:"count" (everywhere "int") (Returns Int32)
        [
          ( "waited_for",
            Elements_to_change (Int32, Counted { by = "count"; each = 2 }),
            everywhere "struct pollfd *" );
          ( "count",
            Value USize,
            by_os (function Linux -> "unsigned long" | Macos -> "unsigned int") );
          ("timeout", Value Int32, everywhere "int");
        ]
        ~headers:[ "poll.h" ]
        ~layout:
          [
            "sizeof(struct pollfd) == 8";
            "__builtin_offsetof(struct pollfd, fd) == 0";
            "sizeof(((struct pollfd *)0)->fd) == 4";
            "__builtin_offsetof(struct pollfd, events) == 4";
            "sizeof(((struct pollfd *)0)->events) == 2";
            "__builtin_offsetof(struct pollfd, revents) == 6";
            "sizeof(((struct pollfd *)0)->revents) == 2";
            "__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__";
          ]
  | Kill ->
      row (everywhere "int") (Returns Int32)
        [ ("process", Value Int32, everywhere "int"); ("signal", Value Int32, everywhere "int") ]
        ~headers:[ "signal.h" ]
  | Sysconf ->
      row (everywhere "long") (Returns ISize)
        [ ("name", Value Int32, everywhere "int") ]
        ~headers:[ "unistd.h" ]
  | Exit ->
      row (everywhere "_Noreturn void") Never
        [ ("status", Value Int32, everywhere "int") ]
        ~symbol:(everywhere "_exit") ~headers:[ "unistd.h" ]
  | Pread ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room (UInt8, counted "count"), everywhere "void *");
          ("count", Value USize, size);
          ("offset", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Pwrite ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements (UInt8, counted "count"), everywhere "const void *");
          ("count", Value USize, size);
          ("offset", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Lseek ->
      row offset (Returns Int64)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("offset", Value Int64, offset);
          ("whence", Value Int32, everywhere "int");
        ]
        ~headers:[ "unistd.h" ]
  | Ftruncate ->
      row (everywhere "int") (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int"); ("length", Value Int64, offset) ]
        ~headers:[ "unistd.h" ]
  | Fsync ->
      row (everywhere "int") (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int") ]
        ~headers:[ "unistd.h" ]
  | Fstat ->
      (* The structure is filled as bytes, which the standard library reads
         at the offsets the table's numbers give. *)
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("status", Room (UInt8, Number Stat_size), everywhere "void *");
        ]
        ~symbol:(status_symbol "fstat")
        ~named:[ ("status", "struct stat *") ]
        ~headers:[ "sys/stat.h" ]
        ~layout:
          [
            "sizeof(((struct stat *)0)->st_size) == 8";
            "sizeof(struct timespec) == 16";
            "__builtin_offsetof(struct timespec, tv_sec) == 0";
            "__builtin_offsetof(struct timespec, tv_nsec) == 8";
            "__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__";
          ]
  | Stat ->
      row (everywhere "int") (Returns Int32)
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("status", Room (UInt8, Number Stat_size), everywhere "void *");
        ]
        ~symbol:(status_symbol "stat")
        ~named:[ ("status", "struct stat *") ]
        ~headers:[ "sys/stat.h" ]
  | Lstat ->
      row (everywhere "int") (Returns Int32)
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("status", Room (UInt8, Number Stat_size), everywhere "void *");
        ]
        ~symbol:(status_symbol "lstat")
        ~named:[ ("status", "struct stat *") ]
        ~headers:[ "sys/stat.h" ]
  | Mkdir ->
      row (everywhere "int") (Returns Int32)
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("mode", Value Int32, mode);
        ]
        ~headers:[ "sys/stat.h" ]
  | Remove ->
      row (everywhere "int") (Returns Int32)
        [ ("path", Elements (UInt8, Through_zero), everywhere "const char *") ]
        ~headers:[ "stdio.h" ]
  | Rename ->
      row (everywhere "int") (Returns Int32)
        [
          ("from", Elements (UInt8, Through_zero), everywhere "const char *");
          ("to", Elements (UInt8, Through_zero), everywhere "const char *");
        ]
        ~headers:[ "stdio.h" ]
  | Symlink ->
      row (everywhere "int") (Returns Int32)
        [
          ("target", Elements (UInt8, Through_zero), everywhere "const char *");
          ("link", Elements (UInt8, Through_zero), everywhere "const char *");
        ]
        ~headers:[ "unistd.h" ]
  | Link ->
      row (everywhere "int") (Returns Int32)
        [
          ("target", Elements (UInt8, Through_zero), everywhere "const char *");
          ("link", Elements (UInt8, Through_zero), everywhere "const char *");
        ]
        ~headers:[ "unistd.h" ]
  | Chmod ->
      row (everywhere "int") (Returns Int32)
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("mode", Value Int32, mode);
        ]
        ~headers:[ "sys/stat.h" ]
  | Utimensat ->
      (* The times are two [timespec]s, the time of access and then the time
         of modification, as four numbers. *)
      row (everywhere "int") (Returns Int32)
        [
          ("directory", Value Int32, everywhere "int");
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("times", Elements (Int64, Exactly 4), everywhere "const struct timespec *");
          ("flags", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h"; "sys/stat.h" ]
  | Readlink ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("buffer", Room (UInt8, counted "count"), everywhere "char *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Realpath ->
      (* The resolved path is written into the room given, which is to hold
         [PATH_MAX] bytes, and the address returned is that room's. *)
      row (everywhere "char *") Text
        [
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("resolved", Room (UInt8, Number Path_max), everywhere "char *");
        ]
        ~headers:[ "stdlib.h"; "limits.h" ]
  | Getcwd ->
      (* The path is written into the room given, and the address returned
         is that room's. *)
      row (everywhere "char *") Text
        [
          ("buffer", Room (UInt8, counted "size"), everywhere "char *"); ("size", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Gethostname ->
      (* The name ends with a zero byte unless it fills the bytes given. *)
      row (everywhere "int") (Returns Int32)
        [
          ("name", Elements_to_change (UInt8, counted "size"), everywhere "char *");
          ("size", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Getpid -> row (everywhere "int") (Returns Int32) [] ~headers:[ "unistd.h" ]
  | Proc_pidpath ->
      (* The path of a process's executable, which Linux gives as a link
         in its [/proc]. *)
      row ~at_most:"size"
        ~on:(fun os -> os = Macos)
        (everywhere "int") (Returns Int32)
        [
          ("process", Value Int32, everywhere "int");
          ("buffer", Room (UInt8, counted "size"), everywhere "void *");
          ("size", Value USize, everywhere "unsigned int");
        ]
        ~headers:[ "libproc.h" ]
  | Fcntl_dupfd_cloexec ->
      (* A new descriptor for the same open file, the lowest free one that
         is not less than [least], closed in programs the process runs.
         The request is the row's, since another request reads its third
         argument as an address. *)
      row (everywhere "int") (Returns Int32) ~symbol:(everywhere "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, everywhere "int");
          ("request", Fixed F_dupfd_cloexec, everywhere "int");
          ("least", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Fcntl_setfd_cloexec ->
      (* Has the descriptor closed in programs the process runs. *)
      row (everywhere "int") (Returns Int32) ~symbol:(everywhere "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, everywhere "int");
          ("request", Fixed F_setfd, everywhere "int");
          ("flags", Fixed Fd_cloexec, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Posix_spawn_file_actions_init ->
      (* What a program that is started does to its descriptors before it
         runs. The structure is storage of as many bytes as it takes, which
         only these functions read. *)
      row (everywhere "int") (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            everywhere "void *" );
        ]
        ~named:[ ("actions", "posix_spawn_file_actions_t *") ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_destroy ->
      row (everywhere "int") (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            everywhere "void *" );
        ]
        ~named:[ ("actions", "posix_spawn_file_actions_t *") ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_adddup2 ->
      row (everywhere "int") (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            everywhere "void *" );
          ("descriptor", Value Int32, everywhere "int");
          ("onto", Value Int32, everywhere "int");
        ]
        ~named:[ ("actions", "posix_spawn_file_actions_t *") ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_addopen ->
      row (everywhere "int") (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            everywhere "void *" );
          ("descriptor", Value Int32, everywhere "int");
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
          ("flags", Value Int32, everywhere "int");
          ("mode", Value Int32, mode);
        ]
        ~named:[ ("actions", "posix_spawn_file_actions_t *") ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_addchdir ->
      (* The directory the program starts in. *)
      row (everywhere "int") (Returns Int32)
        ~symbol:(everywhere "posix_spawn_file_actions_addchdir_np")
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            everywhere "void *" );
          ("path", Elements (UInt8, Through_zero), everywhere "const char *");
        ]
        ~named:[ ("actions", "posix_spawn_file_actions_t *") ]
        ~headers:[ "spawn.h" ]
  | Getdents64 ->
      (* The next entries of a directory that is open, as many as fit: each
         is a [struct dirent64], as long as it says it is. *)
      row ~at_most:"count"
        ~on:(fun os -> os = Linux)
        (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room (UInt8, counted "count"), everywhere "void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "dirent.h" ]
  | Getattrlistbulk ->
      (* The next entries of a directory that is open, as many as fit, and
         how many. Each is the attributes that [wanted], a
         [struct attrlist], asks for, in the order of their numbers. *)
      row
        ~on:(fun os -> os = Macos)
        (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("wanted", Elements (UInt8, Exactly 24), everywhere "void *");
          ("buffer", Elements_to_change (UInt8, counted "size"), everywhere "void *");
          ("size", Value USize, size);
          ("options", Value UInt64, everywhere "unsigned long long");
        ]
        ~headers:[ "sys/attr.h"; "unistd.h" ]
        ~layout:[ "sizeof(struct attrlist) == 24" ]
  | Ioctl_tiocgwinsz ->
      (* A terminal's size: its rows, its columns, and its width and height
         in pixels, each two bytes. *)
      row (everywhere "int") (Returns Int32) ~symbol:(everywhere "ioctl") ~variadic_from:2
        [
          ("descriptor", Value Int32, everywhere "int");
          ("request", Fixed Tiocgwinsz, everywhere "unsigned long");
          ("size", Elements_to_change (UInt8, Exactly 8), everywhere "void *");
        ]
        ~headers:[ "sys/ioctl.h" ]
        ~layout:
          [
            "sizeof(struct winsize) == 8";
            "__builtin_offsetof(struct winsize, ws_row) == 0";
            "__builtin_offsetof(struct winsize, ws_col) == 2";
          ]
  | Tcgetattr ->
      (* A terminal's settings, a [struct termios] as bytes, which the
         standard library reads and changes at the offsets the table's
         numbers give. *)
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("settings", Elements_to_change (UInt8, Number Termios_size), everywhere "void *");
        ]
        ~named:[ ("settings", "struct termios *") ]
        ~headers:[ "termios.h" ]
  | Tcsetattr ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("when", Fixed Tcsaflush, everywhere "int");
          ("settings", Elements (UInt8, Number Termios_size), everywhere "const void *");
        ]
        ~named:[ ("settings", "const struct termios *") ]
        ~headers:[ "termios.h" ]
  | Socket ->
      row (everywhere "int") (Returns Int32)
        [
          ("domain", Value Int32, everywhere "int");
          ("kind", Value Int32, everywhere "int");
          ("protocol", Value Int32, everywhere "int");
        ]
        ~headers:[ "sys/socket.h" ]
  | Bind ->
      (* An address is a [struct sockaddr_in] or [sockaddr_in6] as bytes:
         where its family is differs between systems, and the rest is laid
         out as the check holds it to. *)
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("address", Elements (UInt8, counted "length"), everywhere "const void *");
          ("length", Value USize, everywhere "unsigned int");
        ]
        ~named:[ ("address", "const struct sockaddr *") ]
        ~headers:[ "sys/socket.h"; "netinet/in.h" ]
        ~layout:
          [
            "sizeof(struct sockaddr_in) == 16";
            "__builtin_offsetof(struct sockaddr_in, sin_port) == 2";
            "__builtin_offsetof(struct sockaddr_in, sin_addr) == 4";
            "sizeof(struct sockaddr_in6) == 28";
            "__builtin_offsetof(struct sockaddr_in6, sin6_port) == 2";
            "__builtin_offsetof(struct sockaddr_in6, sin6_addr) == 8";
          ]
  | Connect ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("address", Elements (UInt8, counted "length"), everywhere "const void *");
          ("length", Value USize, everywhere "unsigned int");
        ]
        ~named:[ ("address", "const struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Listen ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int"); ("waiting", Value Int32, everywhere "int");
        ]
        ~headers:[ "sys/socket.h" ]
  | Accept ->
      (* The length is how much room the address has, and then how long
         the address is. *)
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("address", Elements_to_change (UInt8, counted "length"), everywhere "void *");
          ("length", Written (UInt32, [ "length" ]), everywhere "unsigned int *");
        ]
        ~named:[ ("address", "struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Getsockname ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("address", Elements_to_change (UInt8, counted "length"), everywhere "void *");
          ("length", Written (UInt32, [ "length" ]), everywhere "unsigned int *");
        ]
        ~named:[ ("address", "struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Getpeername ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("address", Elements_to_change (UInt8, counted "length"), everywhere "void *");
          ("length", Written (UInt32, [ "length" ]), everywhere "unsigned int *");
        ]
        ~named:[ ("address", "struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Shutdown ->
      row (everywhere "int") (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int"); ("how", Value Int32, everywhere "int") ]
        ~headers:[ "sys/socket.h" ]
  | Setsockopt ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("level", Value Int32, everywhere "int");
          ("option", Value Int32, everywhere "int");
          ("value", Elements (UInt8, counted "length"), everywhere "const void *");
          ("length", Value USize, everywhere "unsigned int");
        ]
        ~headers:[ "sys/socket.h"; "sys/time.h" ]
        ~layout:
          [ "sizeof(struct timeval) == 16"; "__builtin_offsetof(struct timeval, tv_usec) == 8" ]
  | Getsockopt ->
      row (everywhere "int") (Returns Int32)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("level", Value Int32, everywhere "int");
          ("option", Value Int32, everywhere "int");
          ("value", Elements_to_change (UInt8, counted "length"), everywhere "void *");
          ("length", Written (UInt32, [ "length" ]), everywhere "unsigned int *");
        ]
        ~headers:[ "sys/socket.h" ]
  | Sendto ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements (UInt8, counted "count"), everywhere "const void *");
          ("count", Value USize, size);
          ("flags", Value Int32, everywhere "int");
          ("address", Elements (UInt8, counted "length"), everywhere "const void *");
          ("length", Value USize, everywhere "unsigned int");
        ]
        ~named:[ ("address", "const struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Recvfrom ->
      row ~at_most:"count" (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room (UInt8, counted "count"), everywhere "void *");
          ("count", Value USize, size);
          ("flags", Value Int32, everywhere "int");
          ("address", Elements_to_change (UInt8, counted "length"), everywhere "void *");
          ("length", Written (UInt32, [ "length" ]), everywhere "unsigned int *");
        ]
        ~named:[ ("address", "struct sockaddr *") ]
        ~headers:[ "sys/socket.h" ]
  | Fcntl_getfl ->
      row (everywhere "int") (Returns Int32) ~symbol:(everywhere "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, everywhere "int");
          ("request", Fixed F_getfl, everywhere "int");
          ("unused", Always 0, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Fcntl_setfl ->
      row (everywhere "int") (Returns Int32) ~symbol:(everywhere "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, everywhere "int");
          ("request", Fixed F_setfl, everywhere "int");
          ("flags", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Addresses_of_host ->
      (* The runtime's, and no function of the C library: [getaddrinfo]
         gives a host's addresses as a chain of structures that hold
         addresses of one another, which no row can describe. The runtime
         follows the chain and writes each address into the room it is
         given, as a byte that is 4 or 6 and then the address's 4 or 16
         bytes. It returns how many bytes it wrote, -1 where the system
         knows no such host, and -2 where it could not find out. *)
      row ~at_most:"room"
        ~symbol:(everywhere "t_runtime_addresses_of_host")
        (everywhere "long") (Returns ISize)
        [
          ("host", Elements (UInt8, Through_zero), everywhere "const char *");
          ("addresses", Room (UInt8, counted "room"), everywhere "void *");
          ("room", Value USize, size);
        ]
        ~headers:[]
  | Signals_wait ->
      (* The runtime's. It blocks until one of the signals arrives and
         returns the signal's number, or 0 if the calling task is cancelled
         first. The runtime handles the signals itself, so that a task on
         any thread can wait for them. *)
      row
        ~symbol:(everywhere "t_runtime_signals_wait")
        (everywhere "int32_t") (Returns Int32)
        [
          ("signals", Elements (Int32, counted "count"), everywhere "const int32_t *");
          ("count", Value USize, size);
        ]
        ~headers:[]
  | (Descriptor_watch | Descriptor_wait) as waiting ->
      (* The runtime's. A socket that tasks wait for does not block: a call
         that would block fails with [EAGAIN]. The caller takes a ticket
         before the call and waits on it after [EAGAIN], so that it does
         not miss the descriptor becoming ready between the two. The wait
         returns 1 when the call is to be made again. It returns 0 when it
         is not, and sets [errno]: to [EINTR] if the calling task is
         cancelled, and to [EAGAIN] if the time limit that the program set
         on the socket passed. *)
      let descriptor = ("descriptor", Value Int32, everywhere "int32_t") in
      let writing = ("writing", Value Int32, everywhere "int32_t") in
      if waiting = Descriptor_watch then
        row
          ~symbol:(everywhere "t_runtime_descriptor_watch")
          (everywhere "uint64_t") (Returns UInt64) [ descriptor; writing ] ~headers:[]
      else
        row
          ~symbol:(everywhere "t_runtime_descriptor_wait")
          (everywhere "int32_t") (Returns Int32)
          [ descriptor; writing; ("ticket", Value UInt64, everywhere "uint64_t") ]
          ~headers:[]
  | Sleep ->
      (* The runtime's. It waits for the time and returns 0, or returns 1 as
         soon as the calling task is cancelled. *)
      row ~symbol:(everywhere "t_runtime_sleep") (everywhere "int32_t") (Returns Int32)
        [
          ("seconds", Value Int64, everywhere "int64_t");
          ("nanoseconds", Value Int64, everywhere "int64_t");
        ]
        ~headers:[]
  | ( Tasks_open | Tasks_join | Tasks_cancel | Tasks_cancelled | Tasks_watch | Tasks_wait
    | Tasks_wake | Tasks_lock | Tasks_unlock | Tasks_yield ) as task -> (
      (* The runtime's task functions. A group, a key, a ticket, and a
         mutex are each a [UInt64]. A function with no result to return
         returns 0. *)
      let handle name = (name, Value UInt64, everywhere "uint64_t") in
      let symbol = everywhere ("t_runtime_" ^ function_name task) in
      let returns_handle = row ~symbol (everywhere "uint64_t") (Returns UInt64) ~headers:[] in
      let returns_flag = row ~symbol (everywhere "int32_t") (Returns Int32) ~headers:[] in
      match task with
      | Tasks_open -> returns_handle []
      | Tasks_watch -> returns_handle [ handle "key" ]
      | Tasks_join | Tasks_cancel -> returns_flag [ handle "group" ]
      | Tasks_cancelled | Tasks_yield -> returns_flag []
      | Tasks_wait -> returns_flag [ handle "key"; handle "ticket" ]
      | Tasks_wake -> returns_flag [ handle "key" ]
      | Tasks_lock | Tasks_unlock -> returns_flag [ handle "mutex" ]
      | _ -> returns_flag [])

let available system function_ = (describe function_).on system.os

(* Every function is named, so that a new row says whether it blocks. *)
let blocks = function
  | Write | Read | Pread | Pwrite | Open | Fsync | Waitpid | Poll | Addresses_of_host -> true
  (* The standard library's sockets do not block. *)
  | Connect | Accept | Sendto | Recvfrom -> false
  | Close | Errno | Clock_gettime | Getentropy | Getenv | Posix_spawnp | Snprintf | Strtod | Strtof
  | Fork | Pipe | Kill | Sysconf | Exit | Lseek | Ftruncate | Fstat | Stat | Lstat | Mkdir | Remove
  | Rename | Symlink | Link | Chmod | Utimensat | Readlink | Realpath | Getcwd | Gethostname
  | Getpid | Proc_pidpath | Fcntl_dupfd_cloexec | Fcntl_setfd_cloexec
  | Posix_spawn_file_actions_init | Posix_spawn_file_actions_destroy
  | Posix_spawn_file_actions_adddup2 | Posix_spawn_file_actions_addopen
  | Posix_spawn_file_actions_addchdir | Getdents64 | Getattrlistbulk | Ioctl_tiocgwinsz | Tcgetattr
  | Tcsetattr | Socket | Bind | Listen | Getsockname | Getpeername | Shutdown | Setsockopt
  | Getsockopt | Fcntl_getfl | Fcntl_setfl ->
      false
  (* The runtime's own functions that wait park the calling task, or count
     its thread as blocked, themselves. *)
  | Signals_wait | Descriptor_watch | Descriptor_wait | Sleep | Tasks_open | Tasks_join
  | Tasks_cancel | Tasks_cancelled | Tasks_watch | Tasks_wait | Tasks_wake | Tasks_lock
  | Tasks_unlock | Tasks_yield ->
      false

let of_the_runtime = function
  | Addresses_of_host | Signals_wait | Descriptor_watch | Descriptor_wait | Sleep | Tasks_open
  | Tasks_join | Tasks_cancel | Tasks_cancelled | Tasks_watch | Tasks_wait | Tasks_wake | Tasks_lock
  | Tasks_unlock | Tasks_yield ->
      true
  | _ -> false

let signature function_ =
  let row = describe function_ in
  {
    parameters = List.map (fun (name, passes, _) -> (name, passes)) row.parameters;
    result = row.result;
    at_most = row.at_most;
  }

let declaration system function_ : declaration =
  let row = describe function_ in
  {
    symbol = row.symbol system;
    returns = row.returns system;
    takes = List.map (fun (_, _, c) -> c system) row.parameters;
    variadic_from = row.variadic_from;
  }

(* The structures a C type names, which a file that includes no header
   declares before it can mention them. *)
let structures c =
  let word = "struct " in
  let length = String.length c and skip = String.length word in
  let rec from start found =
    if start + skip > length then List.rev found
    else if String.sub c start skip = word then begin
      let stop = ref (start + skip) in
      while
        !stop < length
        && match c.[!stop] with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false
      do
        incr stop
      done;
      from !stop (String.sub c start (!stop - start) :: found)
    end
    else from (start + 1) found
  in
  from 0 []

let prototype (declaration : declaration) =
  let named =
    List.filteri
      (fun index _ ->
        match declaration.variadic_from with Some first -> index < first | None -> true)
      declaration.takes
  in
  let declared =
    List.sort_uniq String.compare (List.concat_map structures (declaration.returns :: named))
  in
  let parameters =
    match (named, declaration.variadic_from) with
    | [], None -> "void"
    | named, None -> String.concat ", " named
    | named, Some _ -> String.concat ", " (named @ [ "..." ])
  in
  String.concat "" (List.map (fun structure -> structure ^ ";\n") declared)
  ^ Printf.sprintf "%s %s(%s);\n" declaration.returns declaration.symbol parameters

let numbers =
  [
    O_rdonly;
    O_wronly;
    O_creat;
    O_trunc;
    O_cloexec;
    Eintr;
    Enoent;
    Eacces;
    Eio;
    Einval;
    Clock_realtime;
    Clock_monotonic;
    Sc_nprocessors_onln;
    Pollin;
    Pollhup;
    Sigkill;
    O_rdwr;
    O_append;
    O_excl;
    Seek_set;
    Seek_cur;
    Seek_end;
    Eperm;
    Ebadf;
    Eexist;
    Enotdir;
    Eisdir;
    Enfile;
    Emfile;
    Enospc;
    Epipe;
    Enosys;
    Enotempty;
    Enotsup;
    Eaddrinuse;
    Eaddrnotavail;
    Enetunreach;
    Econnaborted;
    Econnreset;
    Enotconn;
    Etimedout;
    Econnrefused;
    Ehostunreach;
    Stat_size;
    Stat_mode_offset;
    Stat_mode_size;
    Stat_length_offset;
    Stat_accessed_offset;
    Stat_modified_offset;
    Stat_created_offset;
    S_ifmt;
    S_ifreg;
    S_ifdir;
    S_iflnk;
    At_fdcwd;
    Utime_omit;
    Path_max;
    F_dupfd_cloexec;
    F_setfd;
    Fd_cloexec;
    Spawn_file_actions_size;
    Sigusr1;
    Sigusr2;
    O_directory;
    Dirent_length_offset;
    Dirent_kind_offset;
    Dirent_name_offset;
    Dt_unknown;
    Dt_dir;
    Dt_reg;
    Dt_lnk;
    Attr_bit_map_count;
    Attr_cmn_returned_attrs;
    Attr_cmn_name;
    Attr_cmn_objtype;
    Vreg;
    Vdir;
    Vlnk;
    Termios_size;
    Termios_iflag_offset;
    Termios_oflag_offset;
    Termios_cflag_offset;
    Termios_lflag_offset;
    Termios_flag_size;
    Termios_cc_offset;
    Vmin;
    Vtime;
    Tcsaflush;
    Tiocgwinsz;
    Icanon;
    Echo;
    Isig;
    Iexten;
    Ixon;
    Icrnl;
    Brkint;
    Inpck;
    Istrip;
    Opost;
    Cs8;
    Af_inet;
    Af_inet6;
    Sock_stream;
    Sock_dgram;
    Sol_socket;
    So_reuseaddr;
    So_rcvtimeo;
    So_sndtimeo;
    So_error;
    Shut_rd;
    Shut_wr;
    Shut_rdwr;
    Ipproto_ipv6;
    Ipv6_v6only;
    O_nonblock;
    F_getfl;
    F_setfl;
    Einprogress;
    Eagain;
    Pollout;
    Sockaddr_family_offset;
    Sockaddr_family_size;
  ]

let number_name = function
  | O_rdonly -> "O_RDONLY"
  | O_wronly -> "O_WRONLY"
  | O_creat -> "O_CREAT"
  | O_trunc -> "O_TRUNC"
  | O_cloexec -> "O_CLOEXEC"
  | Eintr -> "EINTR"
  | Enoent -> "ENOENT"
  | Eacces -> "EACCES"
  | Eio -> "EIO"
  | Einval -> "EINVAL"
  | Clock_realtime -> "CLOCK_REALTIME"
  | Clock_monotonic -> "CLOCK_MONOTONIC"
  | Sc_nprocessors_onln -> "_SC_NPROCESSORS_ONLN"
  | Pollin -> "POLLIN"
  | Pollhup -> "POLLHUP"
  | Sigkill -> "SIGKILL"
  | O_rdwr -> "O_RDWR"
  | O_append -> "O_APPEND"
  | O_excl -> "O_EXCL"
  | Seek_set -> "SEEK_SET"
  | Seek_cur -> "SEEK_CUR"
  | Seek_end -> "SEEK_END"
  | Eperm -> "EPERM"
  | Ebadf -> "EBADF"
  | Eexist -> "EEXIST"
  | Enotdir -> "ENOTDIR"
  | Eisdir -> "EISDIR"
  | Enfile -> "ENFILE"
  | Emfile -> "EMFILE"
  | Enospc -> "ENOSPC"
  | Epipe -> "EPIPE"
  | Enosys -> "ENOSYS"
  | Enotempty -> "ENOTEMPTY"
  | Enotsup -> "ENOTSUP"
  | Eaddrinuse -> "EADDRINUSE"
  | Eaddrnotavail -> "EADDRNOTAVAIL"
  | Enetunreach -> "ENETUNREACH"
  | Econnaborted -> "ECONNABORTED"
  | Econnreset -> "ECONNRESET"
  | Enotconn -> "ENOTCONN"
  | Etimedout -> "ETIMEDOUT"
  | Econnrefused -> "ECONNREFUSED"
  | Ehostunreach -> "EHOSTUNREACH"
  | Stat_size -> "STAT_SIZE"
  | Stat_mode_offset -> "STAT_MODE_OFFSET"
  | Stat_mode_size -> "STAT_MODE_SIZE"
  | Stat_length_offset -> "STAT_LENGTH_OFFSET"
  | Stat_accessed_offset -> "STAT_ACCESSED_OFFSET"
  | Stat_modified_offset -> "STAT_MODIFIED_OFFSET"
  | Stat_created_offset -> "STAT_CREATED_OFFSET"
  | S_ifmt -> "S_IFMT"
  | S_ifreg -> "S_IFREG"
  | S_ifdir -> "S_IFDIR"
  | S_iflnk -> "S_IFLNK"
  | At_fdcwd -> "AT_FDCWD"
  | Utime_omit -> "UTIME_OMIT"
  | Path_max -> "PATH_MAX"
  | F_dupfd_cloexec -> "F_DUPFD_CLOEXEC"
  | F_setfd -> "F_SETFD"
  | Fd_cloexec -> "FD_CLOEXEC"
  | Spawn_file_actions_size -> "SPAWN_FILE_ACTIONS_SIZE"
  | Sigusr1 -> "SIGUSR1"
  | Sigusr2 -> "SIGUSR2"
  | O_directory -> "O_DIRECTORY"
  | Dirent_length_offset -> "DIRENT_LENGTH_OFFSET"
  | Dirent_kind_offset -> "DIRENT_KIND_OFFSET"
  | Dirent_name_offset -> "DIRENT_NAME_OFFSET"
  | Dt_unknown -> "DT_UNKNOWN"
  | Dt_dir -> "DT_DIR"
  | Dt_reg -> "DT_REG"
  | Dt_lnk -> "DT_LNK"
  | Attr_bit_map_count -> "ATTR_BIT_MAP_COUNT"
  | Attr_cmn_returned_attrs -> "ATTR_CMN_RETURNED_ATTRS"
  | Attr_cmn_name -> "ATTR_CMN_NAME"
  | Attr_cmn_objtype -> "ATTR_CMN_OBJTYPE"
  | Vreg -> "VREG"
  | Vdir -> "VDIR"
  | Vlnk -> "VLNK"
  | Termios_size -> "TERMIOS_SIZE"
  | Termios_iflag_offset -> "TERMIOS_IFLAG_OFFSET"
  | Termios_oflag_offset -> "TERMIOS_OFLAG_OFFSET"
  | Termios_cflag_offset -> "TERMIOS_CFLAG_OFFSET"
  | Termios_lflag_offset -> "TERMIOS_LFLAG_OFFSET"
  | Termios_flag_size -> "TERMIOS_FLAG_SIZE"
  | Termios_cc_offset -> "TERMIOS_CC_OFFSET"
  | Vmin -> "VMIN"
  | Vtime -> "VTIME"
  | Tcsaflush -> "TCSAFLUSH"
  | Tiocgwinsz -> "TIOCGWINSZ"
  | Icanon -> "ICANON"
  | Echo -> "ECHO"
  | Isig -> "ISIG"
  | Iexten -> "IEXTEN"
  | Ixon -> "IXON"
  | Icrnl -> "ICRNL"
  | Brkint -> "BRKINT"
  | Inpck -> "INPCK"
  | Istrip -> "ISTRIP"
  | Opost -> "OPOST"
  | Cs8 -> "CS8"
  | Af_inet -> "AF_INET"
  | Af_inet6 -> "AF_INET6"
  | Sock_stream -> "SOCK_STREAM"
  | Sock_dgram -> "SOCK_DGRAM"
  | Sol_socket -> "SOL_SOCKET"
  | So_reuseaddr -> "SO_REUSEADDR"
  | So_rcvtimeo -> "SO_RCVTIMEO"
  | So_sndtimeo -> "SO_SNDTIMEO"
  | So_error -> "SO_ERROR"
  | Shut_rd -> "SHUT_RD"
  | Shut_wr -> "SHUT_WR"
  | Shut_rdwr -> "SHUT_RDWR"
  | Ipproto_ipv6 -> "IPPROTO_IPV6"
  | Ipv6_v6only -> "IPV6_V6ONLY"
  | O_nonblock -> "O_NONBLOCK"
  | F_getfl -> "F_GETFL"
  | F_setfl -> "F_SETFL"
  | Einprogress -> "EINPROGRESS"
  | Eagain -> "EAGAIN"
  | Pollout -> "POLLOUT"
  | Sockaddr_family_offset -> "SOCKADDR_FAMILY_OFFSET"
  | Sockaddr_family_size -> "SOCKADDR_FAMILY_SIZE"

(* A size or an offset in a structure is a [USize], and the bits of a
   file's mode are compared with a number read out of the structure. *)
let number_type = function
  | Stat_size | Stat_mode_offset | Stat_mode_size | Stat_length_offset | Stat_accessed_offset
  | Stat_modified_offset | Stat_created_offset ->
      USize
  | S_ifmt | S_ifreg | S_ifdir | S_iflnk -> UInt64
  | Utime_omit -> Int64
  | Path_max | Spawn_file_actions_size | Dirent_length_offset | Dirent_kind_offset
  | Dirent_name_offset | Termios_size | Termios_iflag_offset | Termios_oflag_offset
  | Termios_cflag_offset | Termios_lflag_offset | Termios_flag_size | Termios_cc_offset | Vmin
  | Vtime | Sockaddr_family_offset | Sockaddr_family_size ->
      USize
  | Tiocgwinsz | Icanon | Echo | Isig | Iexten | Ixon | Icrnl | Brkint | Inpck | Istrip | Opost
  | Cs8 ->
      UInt64
  | Dt_unknown | Dt_dir | Dt_reg | Dt_lnk | Attr_bit_map_count | Attr_cmn_returned_attrs
  | Attr_cmn_name | Attr_cmn_objtype | Vreg | Vdir | Vlnk ->
      UInt64
  | _ -> Int32

let number_headers = function
  | O_rdonly | O_wronly | O_creat | O_trunc | O_cloexec | O_rdwr | O_append | O_excl ->
      [ "fcntl.h" ]
  | Eintr | Enoent | Eacces | Eio | Einval | Eperm | Ebadf | Eexist | Enotdir | Eisdir | Enfile
  | Emfile | Enospc | Epipe | Enosys | Enotempty | Enotsup | Eaddrinuse | Eaddrnotavail
  | Enetunreach | Econnaborted | Econnreset | Enotconn | Etimedout | Econnrefused | Ehostunreach ->
      [ "errno.h" ]
  | Seek_set | Seek_cur | Seek_end -> [ "unistd.h" ]
  | Clock_realtime | Clock_monotonic -> [ "time.h" ]
  | Sc_nprocessors_onln -> [ "unistd.h" ]
  | Pollin | Pollhup -> [ "poll.h" ]
  | Sigkill | Sigusr1 | Sigusr2 -> [ "signal.h" ]
  | Spawn_file_actions_size -> [ "spawn.h" ]
  | Stat_size | Stat_mode_offset | Stat_mode_size | Stat_length_offset | Stat_accessed_offset
  | Stat_modified_offset | Stat_created_offset | S_ifmt | S_ifreg | S_ifdir | S_iflnk | Utime_omit
    ->
      [ "sys/stat.h" ]
  | At_fdcwd | F_dupfd_cloexec | F_setfd | Fd_cloexec | O_directory -> [ "fcntl.h" ]
  | Dirent_length_offset | Dirent_kind_offset | Dirent_name_offset | Dt_unknown | Dt_dir | Dt_reg
  | Dt_lnk ->
      [ "dirent.h" ]
  | Attr_bit_map_count | Attr_cmn_returned_attrs | Attr_cmn_name | Attr_cmn_objtype ->
      [ "sys/attr.h" ]
  | Vreg | Vdir | Vlnk -> [ "sys/vnode.h" ]
  | Termios_size | Termios_iflag_offset | Termios_oflag_offset | Termios_cflag_offset
  | Termios_lflag_offset | Termios_flag_size | Termios_cc_offset | Vmin | Vtime | Tcsaflush | Icanon
  | Echo | Isig | Iexten | Ixon | Icrnl | Brkint | Inpck | Istrip | Opost | Cs8 ->
      [ "termios.h" ]
  | Tiocgwinsz -> [ "sys/ioctl.h" ]
  | Af_inet | Af_inet6 | Sock_stream | Sock_dgram | Sol_socket | So_reuseaddr | So_rcvtimeo
  | So_sndtimeo | So_error | Shut_rd | Shut_wr | Shut_rdwr | Sockaddr_family_offset
  | Sockaddr_family_size ->
      [ "sys/socket.h" ]
  | Ipproto_ipv6 | Ipv6_v6only -> [ "netinet/in.h" ]
  | O_nonblock | F_getfl | F_setfl -> [ "fcntl.h" ]
  | Einprogress | Eagain -> [ "errno.h" ]
  | Pollout -> [ "poll.h" ]
  | Path_max -> [ "limits.h" ]

(* The C expression that a number is the value of, which the check compares
   with the table's value. Most numbers are constants that the headers
   name. A size or an offset in [struct stat] is an expression over the
   structure. [None] where this system's structure has no such field. *)
let number_expression (system : system) number =
  let offset_of field = Some (Printf.sprintf "__builtin_offsetof(struct stat, %s)" field) in
  match (number, system.os) with
  | Stat_size, _ -> Some "sizeof(struct stat)"
  | Sockaddr_family_offset, _ -> Some "__builtin_offsetof(struct sockaddr, sa_family)"
  | Sockaddr_family_size, _ -> Some "sizeof(((struct sockaddr *)0)->sa_family)"
  | Termios_size, _ -> Some "sizeof(struct termios)"
  | Termios_iflag_offset, _ -> Some "__builtin_offsetof(struct termios, c_iflag)"
  | Termios_oflag_offset, _ -> Some "__builtin_offsetof(struct termios, c_oflag)"
  | Termios_cflag_offset, _ -> Some "__builtin_offsetof(struct termios, c_cflag)"
  | Termios_lflag_offset, _ -> Some "__builtin_offsetof(struct termios, c_lflag)"
  | Termios_flag_size, _ -> Some "sizeof(((struct termios *)0)->c_lflag)"
  | Termios_cc_offset, _ -> Some "__builtin_offsetof(struct termios, c_cc)"
  | Dirent_length_offset, Linux -> Some "__builtin_offsetof(struct dirent64, d_reclen)"
  | Dirent_kind_offset, Linux -> Some "__builtin_offsetof(struct dirent64, d_type)"
  | Dirent_name_offset, Linux -> Some "__builtin_offsetof(struct dirent64, d_name)"
  | (Dirent_length_offset | Dirent_kind_offset | Dirent_name_offset), Macos -> None
  | ( ( Attr_bit_map_count | Attr_cmn_returned_attrs | Attr_cmn_name | Attr_cmn_objtype | Vreg
      | Vdir | Vlnk ),
      Linux ) ->
      None
  | Spawn_file_actions_size, _ -> Some "sizeof(posix_spawn_file_actions_t)"
  | Stat_mode_offset, _ -> offset_of "st_mode"
  | Stat_mode_size, _ -> Some "sizeof(((struct stat *)0)->st_mode)"
  | Stat_length_offset, _ -> offset_of "st_size"
  | Stat_accessed_offset, Linux -> offset_of "st_atim"
  | Stat_accessed_offset, Macos -> offset_of "st_atimespec"
  | Stat_modified_offset, Linux -> offset_of "st_mtim"
  | Stat_modified_offset, Macos -> offset_of "st_mtimespec"
  | Stat_created_offset, Linux -> None
  | Stat_created_offset, Macos -> offset_of "st_birthtimespec"
  | number, _ -> Some (number_name number)

let value (system : system) number =
  match (number, system.os) with
  | O_rdonly, (Linux | Macos) -> 0
  | O_wronly, (Linux | Macos) -> 1
  | O_creat, Linux -> 0x40
  | O_creat, Macos -> 0x200
  | O_trunc, Linux -> 0x200
  | O_trunc, Macos -> 0x400
  | O_cloexec, Linux -> 0x80000
  | O_cloexec, Macos -> 0x1000000
  | Eintr, (Linux | Macos) -> 4
  | Enoent, (Linux | Macos) -> 2
  | Eacces, (Linux | Macos) -> 13
  | Eio, (Linux | Macos) -> 5
  | Einval, (Linux | Macos) -> 22
  | Clock_realtime, (Linux | Macos) -> 0
  | Clock_monotonic, Linux -> 1
  | Clock_monotonic, Macos -> 6
  | Sc_nprocessors_onln, Linux -> 84
  | Sc_nprocessors_onln, Macos -> 58
  | Pollin, (Linux | Macos) -> 0x1
  | Pollhup, (Linux | Macos) -> 0x10
  | Sigkill, (Linux | Macos) -> 9
  | O_rdwr, (Linux | Macos) -> 2
  | O_append, Linux -> 0x400
  | O_append, Macos -> 0x8
  | O_excl, Linux -> 0x80
  | O_excl, Macos -> 0x800
  | Seek_set, (Linux | Macos) -> 0
  | Seek_cur, (Linux | Macos) -> 1
  | Seek_end, (Linux | Macos) -> 2
  | Eperm, (Linux | Macos) -> 1
  | Ebadf, (Linux | Macos) -> 9
  | Eexist, (Linux | Macos) -> 17
  | Enotdir, (Linux | Macos) -> 20
  | Eisdir, (Linux | Macos) -> 21
  | Enfile, (Linux | Macos) -> 23
  | Emfile, (Linux | Macos) -> 24
  | Enospc, (Linux | Macos) -> 28
  | Epipe, (Linux | Macos) -> 32
  | Enosys, Linux -> 38
  | Enosys, Macos -> 78
  | Enotempty, Linux -> 39
  | Enotempty, Macos -> 66
  | Enotsup, Linux -> 95
  | Enotsup, Macos -> 45
  | Eaddrinuse, Linux -> 98
  | Eaddrinuse, Macos -> 48
  | Eaddrnotavail, Linux -> 99
  | Eaddrnotavail, Macos -> 49
  | Enetunreach, Linux -> 101
  | Enetunreach, Macos -> 51
  | Econnaborted, Linux -> 103
  | Econnaborted, Macos -> 53
  | Econnreset, Linux -> 104
  | Econnreset, Macos -> 54
  | Enotconn, Linux -> 107
  | Enotconn, Macos -> 57
  | Etimedout, Linux -> 110
  | Etimedout, Macos -> 60
  | Econnrefused, Linux -> 111
  | Econnrefused, Macos -> 61
  | Ehostunreach, Linux -> 113
  | Ehostunreach, Macos -> 65
  | Stat_size, Linux -> ( match system.architecture with X86_64 -> 144 | Arm64 -> 128)
  | Stat_size, Macos -> 144
  | Stat_mode_offset, Linux -> ( match system.architecture with X86_64 -> 24 | Arm64 -> 16)
  | Stat_mode_offset, Macos -> 4
  | Stat_mode_size, Linux -> 4
  | Stat_mode_size, Macos -> 2
  | Stat_length_offset, Linux -> 48
  | Stat_length_offset, Macos -> 96
  | Stat_accessed_offset, Linux -> 72
  | Stat_accessed_offset, Macos -> 32
  | Stat_modified_offset, Linux -> 88
  | Stat_modified_offset, Macos -> 48
  (* Linux's structure has no time of creation, which 0 says: no time is at
     the start of the structure. *)
  | Stat_created_offset, Linux -> 0
  | Stat_created_offset, Macos -> 80
  | S_ifmt, (Linux | Macos) -> 0o170000
  | S_ifreg, (Linux | Macos) -> 0o100000
  | S_ifdir, (Linux | Macos) -> 0o040000
  | S_iflnk, (Linux | Macos) -> 0o120000
  | At_fdcwd, Linux -> -100
  | At_fdcwd, Macos -> -2
  | Utime_omit, Linux -> 1073741822
  | Utime_omit, Macos -> -2
  | Path_max, Linux -> 4096
  | Path_max, Macos -> 1024
  | F_dupfd_cloexec, Linux -> 1030
  | F_dupfd_cloexec, Macos -> 67
  | F_setfd, (Linux | Macos) -> 2
  | Fd_cloexec, (Linux | Macos) -> 1
  | Spawn_file_actions_size, Linux -> 80
  | Spawn_file_actions_size, Macos -> 8
  | Sigusr1, Linux -> 10
  | Sigusr1, Macos -> 30
  | Sigusr2, Linux -> 12
  | Sigusr2, Macos -> 31
  | O_directory, Linux -> ( match system.architecture with X86_64 -> 0x10000 | Arm64 -> 0x4000)
  | O_directory, Macos -> 0x100000
  | Dirent_length_offset, Linux -> 16
  | Dirent_kind_offset, Linux -> 18
  | Dirent_name_offset, Linux -> 19
  | (Dirent_length_offset | Dirent_kind_offset | Dirent_name_offset), Macos -> 0
  | Dt_unknown, (Linux | Macos) -> 0
  | Dt_dir, (Linux | Macos) -> 4
  | Dt_reg, (Linux | Macos) -> 8
  | Dt_lnk, (Linux | Macos) -> 10
  | Attr_bit_map_count, Macos -> 5
  | Attr_cmn_returned_attrs, Macos -> 0x80000000
  | Attr_cmn_name, Macos -> 1
  | Attr_cmn_objtype, Macos -> 8
  | Termios_size, Linux -> 60
  | Termios_size, Macos -> 72
  | Termios_iflag_offset, Linux -> 0
  | Termios_iflag_offset, Macos -> 0
  | Termios_oflag_offset, Linux -> 4
  | Termios_oflag_offset, Macos -> 8
  | Termios_cflag_offset, Linux -> 8
  | Termios_cflag_offset, Macos -> 16
  | Termios_lflag_offset, Linux -> 12
  | Termios_lflag_offset, Macos -> 24
  | Termios_flag_size, Linux -> 4
  | Termios_flag_size, Macos -> 8
  | Termios_cc_offset, Linux -> 17
  | Termios_cc_offset, Macos -> 32
  | Vmin, Linux -> 6
  | Vmin, Macos -> 16
  | Vtime, Linux -> 5
  | Vtime, Macos -> 17
  | Tcsaflush, (Linux | Macos) -> 2
  | Tiocgwinsz, Linux -> 0x5413
  | Tiocgwinsz, Macos -> 0x40087468
  | Icanon, Linux -> 2
  | Icanon, Macos -> 256
  | Echo, (Linux | Macos) -> 8
  | Isig, Linux -> 1
  | Isig, Macos -> 128
  | Iexten, Linux -> 32768
  | Iexten, Macos -> 1024
  | Ixon, Linux -> 1024
  | Ixon, Macos -> 512
  | Icrnl, (Linux | Macos) -> 256
  | Brkint, (Linux | Macos) -> 2
  | Inpck, (Linux | Macos) -> 16
  | Istrip, (Linux | Macos) -> 32
  | Opost, (Linux | Macos) -> 1
  | Cs8, Linux -> 48
  | Cs8, Macos -> 768
  | Af_inet, (Linux | Macos) -> 2
  | Af_inet6, Linux -> 10
  | Af_inet6, Macos -> 30
  | Sock_stream, (Linux | Macos) -> 1
  | Sock_dgram, (Linux | Macos) -> 2
  | Sol_socket, Linux -> 1
  | Sol_socket, Macos -> 65535
  | So_reuseaddr, Linux -> 2
  | So_reuseaddr, Macos -> 4
  | So_rcvtimeo, Linux -> 20
  | So_rcvtimeo, Macos -> 4102
  | So_sndtimeo, Linux -> 21
  | So_sndtimeo, Macos -> 4101
  | So_error, Linux -> 4
  | So_error, Macos -> 4103
  | Shut_rd, (Linux | Macos) -> 0
  | Shut_wr, (Linux | Macos) -> 1
  | Shut_rdwr, (Linux | Macos) -> 2
  | Ipproto_ipv6, (Linux | Macos) -> 41
  | Ipv6_v6only, Linux -> 26
  | Ipv6_v6only, Macos -> 27
  | O_nonblock, Linux -> 2048
  | O_nonblock, Macos -> 4
  | F_getfl, (Linux | Macos) -> 3
  | F_setfl, (Linux | Macos) -> 4
  | Einprogress, Linux -> 115
  | Einprogress, Macos -> 36
  | Eagain, Linux -> 11
  | Eagain, Macos -> 35
  | Pollout, (Linux | Macos) -> 4
  | Sockaddr_family_offset, Linux -> 0
  | Sockaddr_family_offset, Macos -> 1
  | Sockaddr_family_size, Linux -> 2
  | Sockaddr_family_size, Macos -> 1
  | Vreg, Macos -> 1
  | Vdir, Macos -> 2
  | Vlnk, Macos -> 5
  | ( ( Attr_bit_map_count | Attr_cmn_returned_attrs | Attr_cmn_name | Attr_cmn_objtype | Vreg
      | Vdir | Vlnk ),
      Linux ) ->
      0

(* How many bytes a number the function reaches through an address takes,
   which the C type it is declared with must take too. [USize] has no one
   width: code run while compiling for a narrower target has the target's. *)
let bytes = function
  | UInt8 -> 1
  | Int32 | UInt32 | Float32 -> 4
  | Int64 | UInt64 | Float64 -> 8
  | USize | ISize -> invalid_arg "a USize the C library reaches through an address"

let check system =
  let functions = List.filter (available system) functions in
  let headers =
    List.fold_left
      (fun seen header -> if List.mem header seen then seen else seen @ [ header ])
      []
      (List.concat_map (fun function_ -> (describe function_).headers) functions
      @ List.concat_map number_headers
          (List.filter (fun number -> number_expression system number <> None) numbers))
  in
  let holds what condition = Printf.sprintf "_Static_assert(%s, \"%s\");\n" condition what in
  (* The address is of one of the numbers, where C takes the first of
     several, or of a structure that is all of them. *)
  let reached symbol c count scalar =
    holds
      (symbol ^ " reaches numbers of another size")
      (Printf.sprintf "sizeof(*(%s)0) == %d || sizeof(*(%s)0) == %d" c (bytes scalar) c
         (count * bytes scalar))
  in
  let is_void c =
    String.starts_with ~prefix:"void" c || String.starts_with ~prefix:"const void" c
  in
  String.concat ""
    ([
       (* The headers are to declare each function plainly, not as a macro
          that checks its arguments. *)
       "#undef _FORTIFY_SOURCE\n#define _FORTIFY_SOURCE 0\n#define _GNU_SOURCE\n";
     ]
    @ List.map (fun header -> Printf.sprintf "#include <%s>\n" header) headers
    (* A header may also define a function as a macro, as macOS does
       [sigaddset]. The function is what a program calls. *)
    @ List.sort_uniq String.compare
        (List.map
           (fun function_ -> Printf.sprintf "#undef %s\n" (declaration system function_).symbol)
           functions)
    @ List.filter_map
        (fun number ->
          Option.map
            (fun expression ->
              holds (number_name number)
                (Printf.sprintf "%s == %d" expression (value system number)))
            (number_expression system number))
        numbers
    @ List.concat_map
        (fun function_ ->
          let row = describe function_ and declaration = declaration system function_ in
          let as_the_headers_name_it =
            {
              declaration with
              takes =
                List.map
                  (fun (name, _, c) ->
                    match List.assoc_opt name row.named with
                    | Some named -> named
                    | None -> c system)
                  row.parameters;
            }
          in
          (prototype as_the_headers_name_it :: List.map (holds declaration.symbol) row.layout)
          @ (match row.result with
            | Points_at scalar -> [ reached declaration.symbol declaration.returns 1 scalar ]
            | Returns _ | Text | Never -> [])
          @ List.filter_map
              (fun (_, passes, c) ->
                match passes with
                | Written (scalar, names) when not (is_void (c system)) ->
                    Some (reached declaration.symbol (c system) (List.length names) scalar)
                | Written _ | Value _ | Elements _ | Room _ | Elements_to_change _ | Always _
                | Fixed _ ->
                    None)
              row.parameters)
        functions)
