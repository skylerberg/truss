type os = Linux | Macos
type architecture = X86_64 | Arm64
type system = { os : os; architecture : architecture }

let oses = [ Linux; Macos ]
let architectures = [ X86_64; Arm64 ]
let show_os = function Linux -> "Linux" | Macos -> "macOS"
let show_architecture = function X86_64 -> "x86-64" | Arm64 -> "ARM64"
let show_system system = show_os system.os ^ " on " ^ show_architecture system.architecture

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

type scalar = UInt8 | Int32 | UInt32 | Int64 | UInt64 | Float32 | Float64

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
  | Af_unix
  | Ipproto_tcp
  | Tcp_nodelay
  | So_keepalive
  | Tcp_keepidle
  | So_reuseport
  | Sockaddr_un_path_size

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
type c_type = Void | Named of string | Struct of string | Const of c_type | Pointer of c_type

let rec show_c_type = function
  | Void -> "void"
  | Named name -> name
  | Struct name -> "struct " ^ name
  | Const (Pointer _ as pointer) -> show_c_type pointer ^ "const"
  | Const c_type -> "const " ^ show_c_type c_type
  | Pointer (Pointer _ as inner) -> show_c_type inner ^ "*"
  | Pointer inner -> show_c_type inner ^ " *"

let rec list_structures = function
  | Struct name -> [ name ]
  | Const c_type | Pointer c_type -> list_structures c_type
  | Void | Named _ -> []

type declaration = {
  symbol : string;
  returns : c_type;
  never_returns : bool;
  takes : c_type list;
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
  | Descriptors_watch
  | Descriptors_wait
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
    Descriptors_watch;
    Descriptors_wait;
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

let show_function = function
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
  | Descriptors_watch -> "descriptors_watch"
  | Descriptors_wait -> "descriptors_wait"
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

type row = {
  symbol : system -> string;
  returns : system -> c_type;
  result : result;
  at_most : string option;
  on : os -> bool;
  parameters : (string * passes * (system -> c_type)) list;
  variadic_from : int option;
  headers : string list;
  layout : string list;
  named : (string * c_type) list;
}

let make_portable_type c_type (_ : system) = c_type
let choose_by_os choose (system : system) = choose system.os
let size = make_portable_type (Named "__SIZE_TYPE__")

let show_status_symbol name (system : system) =
  match system with { os = Macos; architecture = X86_64 } -> name ^ "$INODE64" | _ -> name

let mode = choose_by_os (function Linux -> Named "unsigned int" | Macos -> Named "unsigned short")
let offset = choose_by_os (function Linux -> Named "long" | Macos -> Named "long long")

let describe function_ =
  let row ?(symbol = make_portable_type (show_function function_)) ?variadic_from ?(layout = [])
      ?(named = []) ?at_most ?(on = fun _ -> true) returns result parameters ~headers =
    { symbol; returns; result; at_most; on; parameters; variadic_from; headers; layout; named }
  in
  let counted by = Counted { by; each = 1 } in
  match function_ with
  | Write ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("bytes", Elements (UInt8, counted "count"), make_portable_type (Pointer (Const Void)));
          ("count", Value UInt64, size);
        ]
        ~headers:[ "unistd.h" ]
  | Read ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("buffer", Room (UInt8, counted "count"), make_portable_type (Pointer Void));
          ("count", Value UInt64, size);
        ]
        ~headers:[ "unistd.h" ]
  | Open ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~variadic_from:2
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("flags", Value Int32, make_portable_type (Named "int"));
          ("mode", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h" ]
  | Close ->
      row
        (make_portable_type (Named "int32_t"))
        (Returns Int32)
        [ ("descriptor", Value Int32, make_portable_type (Named "int32_t")) ]
        ~symbol:(make_portable_type "t_runtime_close")
        ~headers:[]
  | Errno ->
      row
        (make_portable_type (Pointer (Named "int")))
        (Points_at Int32) []
        ~symbol:(make_portable_type "t_runtime_errno_address_uncached")
        ~headers:[]
  | Clock_gettime ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "clock",
            Value Int32,
            choose_by_os (function Linux -> Named "int" | Macos -> Named "unsigned int") );
          ( "time",
            Written (Int64, [ "seconds"; "nanoseconds" ]),
            make_portable_type (Pointer (Struct "timespec")) );
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
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("buffer", Written (UInt64, [ "value" ]), make_portable_type (Pointer Void));
          ("count", Always 8, size);
        ]
        ~headers:[ "sys/types.h"; "sys/random.h" ]
  | Getenv ->
      row
        (make_portable_type (Pointer (Named "char")))
        Text
        [
          ( "name",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
        ]
        ~headers:[ "stdlib.h" ]
  | Posix_spawnp ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("process", Written (Int32, [ "process" ]), make_portable_type (Pointer (Named "int")));
          ( "program",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ( "file_actions",
            Elements (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer (Const Void)) );
          ("attributes", Always 0, make_portable_type (Pointer (Const Void)));
          ( "arguments",
            Elements (UInt64, Through_zero),
            make_portable_type (Pointer (Const (Pointer (Named "char")))) );
          ( "environment",
            Elements (UInt64, Through_zero),
            make_portable_type (Pointer (Const (Pointer (Named "char")))) );
        ]
        ~named:
          [
            ("file_actions", Pointer (Const (Named "posix_spawn_file_actions_t")));
            ("attributes", Pointer (Const (Named "posix_spawnattr_t")));
          ]
        ~headers:[ "spawn.h" ]
        ~layout:[ "sizeof(char *) == sizeof(__SIZE_TYPE__)" ]
  | Waitpid ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("process", Value Int32, make_portable_type (Named "int"));
          ("status", Written (Int32, [ "status" ]), make_portable_type (Pointer (Named "int")));
          ("options", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "sys/wait.h" ]
  | Snprintf ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~variadic_from:3
        [
          ("buffer", Room (UInt8, counted "size"), make_portable_type (Pointer (Named "char")));
          ("size", Value UInt64, size);
          ( "format",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("precision", Value Int32, make_portable_type (Named "int"));
          ("value", Value Float64, make_portable_type (Named "double"));
        ]
        ~headers:[ "stdio.h" ]
  | Strtod ->
      row
        (make_portable_type (Named "double"))
        (Returns Float64)
        [
          ( "text",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("end", Always 0, make_portable_type (Pointer (Pointer (Named "char"))));
        ]
        ~headers:[ "stdlib.h" ]
  | Strtof ->
      row
        (make_portable_type (Named "float"))
        (Returns Float32)
        [
          ( "text",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("end", Always 0, make_portable_type (Pointer (Pointer (Named "char"))));
        ]
        ~headers:[ "stdlib.h" ]
  | Fork -> row (make_portable_type (Named "int")) (Returns Int32) [] ~headers:[ "unistd.h" ]
  | Pipe ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "ends",
            Written (Int32, [ "read_end"; "write_end" ]),
            make_portable_type (Pointer (Named "int")) );
        ]
        ~headers:[ "unistd.h" ]
  | Poll ->
      row ~at_most:"count"
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "waited_for",
            Elements_to_change (Int32, Counted { by = "count"; each = 2 }),
            make_portable_type (Pointer (Struct "pollfd")) );
          ( "count",
            Value UInt64,
            choose_by_os (function Linux -> Named "unsigned long" | Macos -> Named "unsigned int")
          );
          ("timeout", Value Int32, make_portable_type (Named "int"));
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
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("process", Value Int32, make_portable_type (Named "int"));
          ("signal", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "signal.h" ]
  | Sysconf ->
      row
        (make_portable_type (Named "long"))
        (Returns Int64)
        [ ("name", Value Int32, make_portable_type (Named "int")) ]
        ~headers:[ "unistd.h" ]
  | Exit ->
      row (make_portable_type Void) Never
        [ ("status", Value Int32, make_portable_type (Named "int")) ]
        ~symbol:(make_portable_type "_exit") ~headers:[ "unistd.h" ]
  | Pread ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("buffer", Room (UInt8, counted "count"), make_portable_type (Pointer Void));
          ("count", Value UInt64, size);
          ("offset", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Pwrite ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("bytes", Elements (UInt8, counted "count"), make_portable_type (Pointer (Const Void)));
          ("count", Value UInt64, size);
          ("offset", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Lseek ->
      row offset (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("offset", Value Int64, offset);
          ("whence", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "unistd.h" ]
  | Ftruncate ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("length", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Fsync ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [ ("descriptor", Value Int32, make_portable_type (Named "int")) ]
        ~headers:[ "unistd.h" ]
  | Fstat ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("status", Room (UInt8, Number Stat_size), make_portable_type (Pointer Void));
        ]
        ~symbol:(show_status_symbol "fstat")
        ~named:[ ("status", Pointer (Struct "stat")) ]
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
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("status", Room (UInt8, Number Stat_size), make_portable_type (Pointer Void));
        ]
        ~symbol:(show_status_symbol "stat")
        ~named:[ ("status", Pointer (Struct "stat")) ]
        ~headers:[ "sys/stat.h" ]
  | Lstat ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("status", Room (UInt8, Number Stat_size), make_portable_type (Pointer Void));
        ]
        ~symbol:(show_status_symbol "lstat")
        ~named:[ ("status", Pointer (Struct "stat")) ]
        ~headers:[ "sys/stat.h" ]
  | Mkdir ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("mode", Value Int32, mode);
        ]
        ~headers:[ "sys/stat.h" ]
  | Remove ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
        ]
        ~headers:[ "stdio.h" ]
  | Rename ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "from",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("to", Elements (UInt8, Through_zero), make_portable_type (Pointer (Const (Named "char"))));
        ]
        ~headers:[ "stdio.h" ]
  | Symlink ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "target",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ( "link",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
        ]
        ~headers:[ "unistd.h" ]
  | Link ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "target",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ( "link",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
        ]
        ~headers:[ "unistd.h" ]
  | Chmod ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("mode", Value Int32, mode);
        ]
        ~headers:[ "sys/stat.h" ]
  | Utimensat ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("directory", Value Int32, make_portable_type (Named "int"));
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ( "times",
            Elements (Int64, Exactly 4),
            make_portable_type (Pointer (Const (Struct "timespec"))) );
          ("flags", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h"; "sys/stat.h" ]
  | Readlink ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("buffer", Room (UInt8, counted "count"), make_portable_type (Pointer (Named "char")));
          ("count", Value UInt64, size);
        ]
        ~headers:[ "unistd.h" ]
  | Realpath ->
      row
        (make_portable_type (Pointer (Named "char")))
        Text
        [
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("resolved", Room (UInt8, Number Path_max), make_portable_type (Pointer (Named "char")));
        ]
        ~headers:[ "stdlib.h"; "limits.h" ]
  | Getcwd ->
      row
        (make_portable_type (Pointer (Named "char")))
        Text
        [
          ("buffer", Room (UInt8, counted "size"), make_portable_type (Pointer (Named "char")));
          ("size", Value UInt64, size);
        ]
        ~headers:[ "unistd.h" ]
  | Gethostname ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "name",
            Elements_to_change (UInt8, counted "size"),
            make_portable_type (Pointer (Named "char")) );
          ("size", Value UInt64, size);
        ]
        ~headers:[ "unistd.h" ]
  | Getpid -> row (make_portable_type (Named "int")) (Returns Int32) [] ~headers:[ "unistd.h" ]
  | Proc_pidpath ->
      row ~at_most:"size"
        ~on:(fun os -> os = Macos)
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("process", Value Int32, make_portable_type (Named "int"));
          ("buffer", Room (UInt8, counted "size"), make_portable_type (Pointer Void));
          ("size", Value UInt64, make_portable_type (Named "unsigned int"));
        ]
        ~headers:[ "libproc.h" ]
  | Fcntl_dupfd_cloexec ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~symbol:(make_portable_type "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("request", Fixed F_dupfd_cloexec, make_portable_type (Named "int"));
          ("least", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h" ]
  | Fcntl_setfd_cloexec ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~symbol:(make_portable_type "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("request", Fixed F_setfd, make_portable_type (Named "int"));
          ("flags", Fixed Fd_cloexec, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h" ]
  | Posix_spawn_file_actions_init ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer Void) );
        ]
        ~named:[ ("actions", Pointer (Named "posix_spawn_file_actions_t")) ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_destroy ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer Void) );
        ]
        ~named:[ ("actions", Pointer (Named "posix_spawn_file_actions_t")) ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_adddup2 ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer Void) );
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("onto", Value Int32, make_portable_type (Named "int"));
        ]
        ~named:[ ("actions", Pointer (Named "posix_spawn_file_actions_t")) ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_addopen ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer Void) );
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("flags", Value Int32, make_portable_type (Named "int"));
          ("mode", Value Int32, mode);
        ]
        ~named:[ ("actions", Pointer (Named "posix_spawn_file_actions_t")) ]
        ~headers:[ "spawn.h" ]
  | Posix_spawn_file_actions_addchdir ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        ~symbol:(make_portable_type "posix_spawn_file_actions_addchdir_np")
        [
          ( "actions",
            Elements_to_change (UInt8, Number Spawn_file_actions_size),
            make_portable_type (Pointer Void) );
          ( "path",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
        ]
        ~named:[ ("actions", Pointer (Named "posix_spawn_file_actions_t")) ]
        ~headers:[ "spawn.h" ]
  | Getdents64 ->
      row ~at_most:"count"
        ~on:(fun os -> os = Linux)
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("buffer", Room (UInt8, counted "count"), make_portable_type (Pointer Void));
          ("count", Value UInt64, size);
        ]
        ~headers:[ "dirent.h" ]
  | Getattrlistbulk ->
      row
        ~on:(fun os -> os = Macos)
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("wanted", Elements (UInt8, Exactly 24), make_portable_type (Pointer Void));
          ("buffer", Elements_to_change (UInt8, counted "size"), make_portable_type (Pointer Void));
          ("size", Value UInt64, size);
          ("options", Value UInt64, make_portable_type (Named "unsigned long long"));
        ]
        ~headers:[ "sys/attr.h"; "unistd.h" ]
        ~layout:[ "sizeof(struct attrlist) == 24" ]
  | Ioctl_tiocgwinsz ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~symbol:(make_portable_type "ioctl") ~variadic_from:2
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("request", Fixed Tiocgwinsz, make_portable_type (Named "unsigned long"));
          ("size", Elements_to_change (UInt8, Exactly 8), make_portable_type (Pointer Void));
        ]
        ~headers:[ "sys/ioctl.h" ]
        ~layout:
          [
            "sizeof(struct winsize) == 8";
            "__builtin_offsetof(struct winsize, ws_row) == 0";
            "__builtin_offsetof(struct winsize, ws_col) == 2";
          ]
  | Tcgetattr ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ( "settings",
            Elements_to_change (UInt8, Number Termios_size),
            make_portable_type (Pointer Void) );
        ]
        ~named:[ ("settings", Pointer (Struct "termios")) ]
        ~headers:[ "termios.h" ]
  | Tcsetattr ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("when", Fixed Tcsaflush, make_portable_type (Named "int"));
          ( "settings",
            Elements (UInt8, Number Termios_size),
            make_portable_type (Pointer (Const Void)) );
        ]
        ~named:[ ("settings", Pointer (Const (Struct "termios"))) ]
        ~headers:[ "termios.h" ]
  | Socket ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("domain", Value Int32, make_portable_type (Named "int"));
          ("kind", Value Int32, make_portable_type (Named "int"));
          ("protocol", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "sys/socket.h" ]
  | Bind ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("address", Elements (UInt8, counted "length"), make_portable_type (Pointer (Const Void)));
          ("length", Value UInt64, make_portable_type (Named "unsigned int"));
        ]
        ~named:[ ("address", Pointer (Const (Struct "sockaddr"))) ]
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
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("address", Elements (UInt8, counted "length"), make_portable_type (Pointer (Const Void)));
          ("length", Value UInt64, make_portable_type (Named "unsigned int"));
        ]
        ~named:[ ("address", Pointer (Const (Struct "sockaddr"))) ]
        ~headers:[ "sys/socket.h" ]
  | Listen ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("waiting", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "sys/socket.h" ]
  | Accept ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ( "address",
            Elements_to_change (UInt8, counted "length"),
            make_portable_type (Pointer Void) );
          ( "length",
            Written (UInt32, [ "length" ]),
            make_portable_type (Pointer (Named "unsigned int")) );
        ]
        ~named:[ ("address", Pointer (Struct "sockaddr")) ]
        ~headers:[ "sys/socket.h" ]
  | Getsockname ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ( "address",
            Elements_to_change (UInt8, counted "length"),
            make_portable_type (Pointer Void) );
          ( "length",
            Written (UInt32, [ "length" ]),
            make_portable_type (Pointer (Named "unsigned int")) );
        ]
        ~named:[ ("address", Pointer (Struct "sockaddr")) ]
        ~headers:[ "sys/socket.h" ]
  | Getpeername ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ( "address",
            Elements_to_change (UInt8, counted "length"),
            make_portable_type (Pointer Void) );
          ( "length",
            Written (UInt32, [ "length" ]),
            make_portable_type (Pointer (Named "unsigned int")) );
        ]
        ~named:[ ("address", Pointer (Struct "sockaddr")) ]
        ~headers:[ "sys/socket.h" ]
  | Shutdown ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("how", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "sys/socket.h" ]
  | Setsockopt ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("level", Value Int32, make_portable_type (Named "int"));
          ("option", Value Int32, make_portable_type (Named "int"));
          ("value", Elements (UInt8, counted "length"), make_portable_type (Pointer (Const Void)));
          ("length", Value UInt64, make_portable_type (Named "unsigned int"));
        ]
        ~headers:[ "sys/socket.h"; "sys/time.h" ]
        ~layout:
          [ "sizeof(struct timeval) == 16"; "__builtin_offsetof(struct timeval, tv_usec) == 8" ]
  | Getsockopt ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("level", Value Int32, make_portable_type (Named "int"));
          ("option", Value Int32, make_portable_type (Named "int"));
          ("value", Elements_to_change (UInt8, counted "length"), make_portable_type (Pointer Void));
          ( "length",
            Written (UInt32, [ "length" ]),
            make_portable_type (Pointer (Named "unsigned int")) );
        ]
        ~headers:[ "sys/socket.h" ]
  | Sendto ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("bytes", Elements (UInt8, counted "count"), make_portable_type (Pointer (Const Void)));
          ("count", Value UInt64, size);
          ("flags", Value Int32, make_portable_type (Named "int"));
          ("address", Elements (UInt8, counted "length"), make_portable_type (Pointer (Const Void)));
          ("length", Value UInt64, make_portable_type (Named "unsigned int"));
        ]
        ~named:[ ("address", Pointer (Const (Struct "sockaddr"))) ]
        ~headers:[ "sys/socket.h" ]
  | Recvfrom ->
      row ~at_most:"count"
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("buffer", Room (UInt8, counted "count"), make_portable_type (Pointer Void));
          ("count", Value UInt64, size);
          ("flags", Value Int32, make_portable_type (Named "int"));
          ( "address",
            Elements_to_change (UInt8, counted "length"),
            make_portable_type (Pointer Void) );
          ( "length",
            Written (UInt32, [ "length" ]),
            make_portable_type (Pointer (Named "unsigned int")) );
        ]
        ~named:[ ("address", Pointer (Struct "sockaddr")) ]
        ~headers:[ "sys/socket.h" ]
  | Fcntl_getfl ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~symbol:(make_portable_type "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("request", Fixed F_getfl, make_portable_type (Named "int"));
          ("unused", Always 0, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h" ]
  | Fcntl_setfl ->
      row
        (make_portable_type (Named "int"))
        (Returns Int32) ~symbol:(make_portable_type "fcntl") ~variadic_from:2
        [
          ("descriptor", Value Int32, make_portable_type (Named "int"));
          ("request", Fixed F_setfl, make_portable_type (Named "int"));
          ("flags", Value Int32, make_portable_type (Named "int"));
        ]
        ~headers:[ "fcntl.h" ]
  | Addresses_of_host ->
      row ~at_most:"room"
        ~symbol:(make_portable_type "t_runtime_addresses_of_host")
        (make_portable_type (Named "long"))
        (Returns Int64)
        [
          ( "host",
            Elements (UInt8, Through_zero),
            make_portable_type (Pointer (Const (Named "char"))) );
          ("addresses", Room (UInt8, counted "room"), make_portable_type (Pointer Void));
          ("room", Value UInt64, size);
        ]
        ~headers:[]
  | Signals_wait ->
      row
        ~symbol:(make_portable_type "t_runtime_signals_wait")
        (make_portable_type (Named "int32_t"))
        (Returns Int32)
        [
          ( "signals",
            Elements (Int32, counted "count"),
            make_portable_type (Pointer (Const (Named "int32_t"))) );
          ("count", Value UInt64, size);
        ]
        ~headers:[]
  | (Descriptor_watch | Descriptor_wait) as waiting ->
      let descriptor = ("descriptor", Value Int32, make_portable_type (Named "int32_t")) in
      let writing = ("writing", Value Int32, make_portable_type (Named "int32_t")) in
      if waiting = Descriptor_watch then
        row
          ~symbol:(make_portable_type "t_runtime_descriptor_watch")
          (make_portable_type (Named "uint64_t"))
          (Returns UInt64) [ descriptor; writing ] ~headers:[]
      else
        row
          ~symbol:(make_portable_type "t_runtime_descriptor_wait")
          (make_portable_type (Named "int32_t"))
          (Returns Int32)
          [ descriptor; writing; ("ticket", Value UInt64, make_portable_type (Named "uint64_t")) ]
          ~headers:[]
  | Descriptors_watch ->
      row
        ~symbol:(make_portable_type "t_runtime_descriptors_watch")
        (make_portable_type (Named "uint64_t"))
        (Returns UInt64) [] ~headers:[]
  | Descriptors_wait ->
      row
        ~symbol:(make_portable_type "t_runtime_descriptors_wait")
        (make_portable_type (Named "int32_t"))
        (Returns Int32)
        [
          ( "descriptors",
            Elements (Int32, counted "count"),
            make_portable_type (Pointer (Const (Named "int32_t"))) );
          ("count", Value UInt64, size);
          ("ticket", Value UInt64, make_portable_type (Named "uint64_t"));
        ]
        ~headers:[]
  | Sleep ->
      row
        ~symbol:(make_portable_type "t_runtime_sleep")
        (make_portable_type (Named "int32_t"))
        (Returns Int32)
        [
          ("seconds", Value Int64, make_portable_type (Named "int64_t"));
          ("nanoseconds", Value Int64, make_portable_type (Named "int64_t"));
        ]
        ~headers:[]
  | ( Tasks_open | Tasks_join | Tasks_cancel | Tasks_cancelled | Tasks_watch | Tasks_wait
    | Tasks_wake | Tasks_lock | Tasks_unlock | Tasks_yield ) as task -> (
      let handle name = (name, Value UInt64, make_portable_type (Named "uint64_t")) in
      let symbol = make_portable_type ("t_runtime_" ^ show_function task) in
      let returns_handle =
        row ~symbol (make_portable_type (Named "uint64_t")) (Returns UInt64) ~headers:[]
      in
      let returns_flag =
        row ~symbol (make_portable_type (Named "int32_t")) (Returns Int32) ~headers:[]
      in
      match task with
      | Tasks_open -> returns_handle []
      | Tasks_watch -> returns_handle [ handle "key" ]
      | Tasks_join | Tasks_cancel -> returns_flag [ handle "group" ]
      | Tasks_cancelled | Tasks_yield -> returns_flag []
      | Tasks_wait -> returns_flag [ handle "key"; handle "ticket" ]
      | Tasks_wake -> returns_flag [ handle "key" ]
      | Tasks_lock | Tasks_unlock -> returns_flag [ handle "mutex" ]
      | _ -> returns_flag [])

let is_available system function_ = (describe function_).on system.os

let is_blocking = function
  | Write | Read | Pread | Pwrite | Open | Fsync | Waitpid | Poll | Addresses_of_host -> true
  | Connect | Accept | Sendto | Recvfrom | Close | Errno | Clock_gettime | Getentropy | Getenv
  | Posix_spawnp | Snprintf | Strtod | Strtof | Fork | Pipe | Kill | Sysconf | Exit | Lseek
  | Ftruncate | Fstat | Stat | Lstat | Mkdir | Remove | Rename | Symlink | Link | Chmod | Utimensat
  | Readlink | Realpath | Getcwd | Gethostname | Getpid | Proc_pidpath | Fcntl_dupfd_cloexec
  | Fcntl_setfd_cloexec | Posix_spawn_file_actions_init | Posix_spawn_file_actions_destroy
  | Posix_spawn_file_actions_adddup2 | Posix_spawn_file_actions_addopen
  | Posix_spawn_file_actions_addchdir | Getdents64 | Getattrlistbulk | Ioctl_tiocgwinsz | Tcgetattr
  | Tcsetattr | Socket | Bind | Listen | Getsockname | Getpeername | Shutdown | Setsockopt
  | Getsockopt | Fcntl_getfl | Fcntl_setfl | Signals_wait | Descriptor_watch | Descriptor_wait
  | Descriptors_watch | Descriptors_wait | Sleep | Tasks_open | Tasks_join | Tasks_cancel
  | Tasks_cancelled | Tasks_watch | Tasks_wait | Tasks_wake | Tasks_lock | Tasks_unlock
  | Tasks_yield ->
      false

let is_runtime_function = function
  | Addresses_of_host | Signals_wait | Descriptor_watch | Descriptor_wait | Descriptors_watch
  | Descriptors_wait | Sleep | Tasks_open | Tasks_join | Tasks_cancel | Tasks_cancelled
  | Tasks_watch | Tasks_wait | Tasks_wake | Tasks_lock | Tasks_unlock | Tasks_yield ->
      true
  | _ -> false

let make_signature function_ =
  let row = describe function_ in
  {
    parameters = List.map (fun (name, passes, _) -> (name, passes)) row.parameters;
    result = row.result;
    at_most = row.at_most;
  }

let make_declaration system function_ : declaration =
  let row = describe function_ in
  {
    symbol = row.symbol system;
    returns = row.returns system;
    never_returns = row.result = Never;
    takes = List.map (fun (_, _, c_type) -> c_type system) row.parameters;
    variadic_from = row.variadic_from;
  }

let render_prototype (declaration : declaration) =
  let named =
    match declaration.variadic_from with
    | Some first -> List.take first declaration.takes
    | None -> declaration.takes
  in
  let declared =
    List.sort_uniq String.compare (List.concat_map list_structures (declaration.returns :: named))
  in
  let named = List.map show_c_type named in
  let parameters =
    match (named, declaration.variadic_from) with
    | [], None -> "void"
    | named, None -> String.concat ", " named
    | named, Some _ -> String.concat ", " (named @ [ "..." ])
  in
  String.concat "" (List.map (fun structure -> "struct " ^ structure ^ ";\n") declared)
  ^ Printf.sprintf "%s%s %s(%s);\n"
      (if declaration.never_returns then "_Noreturn " else "")
      (show_c_type declaration.returns) declaration.symbol parameters

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
    Af_unix;
    Ipproto_tcp;
    Tcp_nodelay;
    So_keepalive;
    Tcp_keepidle;
    So_reuseport;
    Sockaddr_un_path_size;
  ]

let show_number = function
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
  | Af_unix -> "AF_UNIX"
  | Ipproto_tcp -> "IPPROTO_TCP"
  | Tcp_nodelay -> "TCP_NODELAY"
  | So_keepalive -> "SO_KEEPALIVE"
  | Tcp_keepidle -> "TCP_KEEPIDLE"
  | So_reuseport -> "SO_REUSEPORT"
  | Sockaddr_un_path_size -> "SOCKADDR_UN_PATH_SIZE"

let classify_number = function
  | Stat_size | Stat_mode_offset | Stat_mode_size | Stat_length_offset | Stat_accessed_offset
  | Stat_modified_offset | Stat_created_offset ->
      UInt64
  | S_ifmt | S_ifreg | S_ifdir | S_iflnk -> UInt64
  | Utime_omit -> Int64
  | Path_max | Spawn_file_actions_size | Dirent_length_offset | Dirent_kind_offset
  | Dirent_name_offset | Termios_size | Termios_iflag_offset | Termios_oflag_offset
  | Termios_cflag_offset | Termios_lflag_offset | Termios_flag_size | Termios_cc_offset | Vmin
  | Vtime | Sockaddr_family_offset | Sockaddr_family_size | Sockaddr_un_path_size ->
      UInt64
  | Tiocgwinsz | Icanon | Echo | Isig | Iexten | Ixon | Icrnl | Brkint | Inpck | Istrip | Opost
  | Cs8 ->
      UInt64
  | Dt_unknown | Dt_dir | Dt_reg | Dt_lnk | Attr_bit_map_count | Attr_cmn_returned_attrs
  | Attr_cmn_name | Attr_cmn_objtype | Vreg | Vdir | Vlnk ->
      UInt64
  | _ -> Int32

let list_number_headers = function
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
  | Af_unix | So_keepalive | So_reuseport -> [ "sys/socket.h" ]
  | Ipproto_ipv6 | Ipv6_v6only | Ipproto_tcp -> [ "netinet/in.h" ]
  | Tcp_nodelay | Tcp_keepidle -> [ "netinet/tcp.h" ]
  | Sockaddr_un_path_size -> [ "sys/un.h" ]
  | O_nonblock | F_getfl | F_setfl -> [ "fcntl.h" ]
  | Einprogress | Eagain -> [ "errno.h" ]
  | Pollout -> [ "poll.h" ]
  | Path_max -> [ "limits.h" ]

let render_number_expression (system : system) number =
  let offset_of field = Some (Printf.sprintf "__builtin_offsetof(struct stat, %s)" field) in
  match (number, system.os) with
  | Stat_size, _ -> Some "sizeof(struct stat)"
  | Sockaddr_family_offset, _ -> Some "__builtin_offsetof(struct sockaddr, sa_family)"
  | Sockaddr_family_size, _ -> Some "sizeof(((struct sockaddr *)0)->sa_family)"
  | Sockaddr_un_path_size, _ -> Some "sizeof(((struct sockaddr_un *)0)->sun_path)"
  | Tcp_keepidle, Macos -> Some "TCP_KEEPALIVE"
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
  | number, _ -> Some (show_number number)

let evaluate_number (system : system) number =
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
  | Af_unix, (Linux | Macos) -> 1
  | Ipproto_tcp, (Linux | Macos) -> 6
  | Tcp_nodelay, (Linux | Macos) -> 1
  | So_keepalive, Linux -> 9
  | So_keepalive, Macos -> 8
  | Tcp_keepidle, Linux -> 4
  | Tcp_keepidle, Macos -> 16
  | So_reuseport, Linux -> 15
  | So_reuseport, Macos -> 512
  | Sockaddr_un_path_size, Linux -> 108
  | Sockaddr_un_path_size, Macos -> 104
  | Vreg, Macos -> 1
  | Vdir, Macos -> 2
  | Vlnk, Macos -> 5
  | ( ( Attr_bit_map_count | Attr_cmn_returned_attrs | Attr_cmn_name | Attr_cmn_objtype | Vreg
      | Vdir | Vlnk ),
      Linux ) ->
      0

let measure_scalar = function
  | UInt8 -> 1
  | Int32 | UInt32 | Float32 -> 4
  | Int64 | UInt64 | Float64 -> 8

let check system =
  let functions = List.filter (is_available system) functions in
  let headers =
    List.fold_left
      (fun seen header -> if List.mem header seen then seen else seen @ [ header ])
      []
      (List.concat_map (fun function_ -> (describe function_).headers) functions
      @ List.concat_map list_number_headers
          (List.filter (fun number -> render_number_expression system number <> None) numbers))
  in
  let holds message condition = Printf.sprintf "_Static_assert(%s, \"%s\");\n" condition message in
  let reached symbol c_type count scalar =
    let c_type = show_c_type c_type in
    holds
      (symbol ^ " reaches numbers of another size")
      (Printf.sprintf "sizeof(*(%s)0) == %d || sizeof(*(%s)0) == %d" c_type (measure_scalar scalar)
         c_type
         (count * measure_scalar scalar))
  in
  let is_void = function Pointer (Void | Const Void) -> true | _ -> false in
  String.concat ""
    ([ "#undef _FORTIFY_SOURCE\n#define _FORTIFY_SOURCE 0\n#define _GNU_SOURCE\n" ]
    @ List.map (fun header -> Printf.sprintf "#include <%s>\n" header) headers
    @ List.sort_uniq String.compare
        (List.map
           (fun function_ ->
             Printf.sprintf "#undef %s\n" (make_declaration system function_).symbol)
           functions)
    @ List.filter_map
        (fun number ->
          Option.map
            (fun expression ->
              holds (show_number number)
                (Printf.sprintf "%s == %d" expression (evaluate_number system number)))
            (render_number_expression system number))
        numbers
    @ List.concat_map
        (fun function_ ->
          let row = describe function_ and declaration = make_declaration system function_ in
          let as_the_headers_name_it =
            {
              declaration with
              takes =
                List.map
                  (fun (name, _, c_type) ->
                    match List.assoc_opt name row.named with
                    | Some named -> named
                    | None -> c_type system)
                  row.parameters;
            }
          in
          (render_prototype as_the_headers_name_it :: List.map (holds declaration.symbol) row.layout)
          @ (match row.result with
            | Points_at scalar -> [ reached declaration.symbol declaration.returns 1 scalar ]
            | Returns _ | Text | Never -> [])
          @ List.filter_map
              (fun (_, passes, c_type) ->
                match passes with
                | Written (scalar, names) when not (is_void (c_type system)) ->
                    Some (reached declaration.symbol (c_type system) (List.length names) scalar)
                | Written _ | Value _ | Elements _ | Room _ | Elements_to_change _ | Always _
                | Fixed _ ->
                    None)
              row.parameters)
        functions)

module For_testing = struct
  let check = check
end
