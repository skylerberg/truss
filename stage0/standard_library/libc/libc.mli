(** The C library as the standard library calls it: its functions and the numbers its headers
    define, for each system stage0 builds for. How Truss calls a function is the same on every
    system; its symbol, its C types, and a number's value are the system's. *)

type os = Linux | Macos
type architecture = X86_64 | Arm64

type system = { os : os; architecture : architecture }
(** A system stage0 builds for. *)

val oses : os list
val architectures : architecture list
val system_name : system -> string

val host : system option
(** The system this compiler was built for, which is the one it runs on and builds programs for, or
    [None] where that is a system it knows no C library of. *)

(** A number that Truss and C both have. *)
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
  | Stat_size  (** How many bytes a [struct stat] takes *)
  | Stat_mode_offset  (** Where in a [struct stat] the file's mode is, and next how many bytes *)
  | Stat_mode_size
  | Stat_length_offset
  | Stat_accessed_offset
  | Stat_modified_offset
  | Stat_created_offset  (** 0 where the structure has no time of creation *)
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
  | Spawn_file_actions_size  (** How many bytes a [posix_spawn_file_actions_t] takes *)
  | Sigusr1
  | Sigusr2
  | O_directory
  | Dirent_length_offset
      (** Where in a [struct dirent64] its length is, then its kind, then its name. Linux's. *)
  | Dirent_kind_offset
  | Dirent_name_offset
  | Dt_unknown
  | Dt_dir
  | Dt_reg
  | Dt_lnk
  | Attr_bit_map_count  (** This and the six after it are macOS's, and 0 elsewhere *)
  | Attr_cmn_returned_attrs
  | Attr_cmn_name
  | Attr_cmn_objtype
  | Vreg
  | Vdir
  | Vlnk
  | Termios_size  (** How many bytes a [struct termios] takes, and where its flags are *)
  | Termios_iflag_offset
  | Termios_oflag_offset
  | Termios_cflag_offset
  | Termios_lflag_offset
  | Termios_flag_size  (** How many bytes one of its sets of flags takes *)
  | Termios_cc_offset  (** Where its control characters start, which [Vmin] and [Vtime] index *)
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
      (** Where the family of a socket's address is, and how many bytes it takes: two from the start
          on Linux; one, after a byte for the address's length, on macOS *)
  | Sockaddr_family_size
  | Af_unix
  | Ipproto_tcp
  | Tcp_nodelay
  | So_keepalive
  | Tcp_keepidle
  | So_reuseport
  | Sockaddr_un_path_size

(** How many elements a function reads or writes through an address it is given. The prover holds
    every call to it: a view has that many elements, and storage has room for that many. *)
type extent =
  | Counted of { by : string; each : int }
  | Exactly of int
  | Number of number  (** As many as a number of the system, such as [PATH_MAX] *)
  | Through_zero
      (** Up to the first element that is zero. The view's last element is zero, so the function
          reads no further than the view. *)

(** How an argument reaches the function. There is no pointer type in Truss, so memory is passed as
    a view or as storage, and the function is given an address into it. *)
type passes =
  | Value of scalar  (** A number, converted to the parameter's C type *)
  | Elements of scalar * extent
      (** A view: the address of its elements, which the function only reads *)
  | Room of scalar * extent
      (** Storage: the address after its last element, for a function that fills room the storage
          has beyond its length *)
  | Elements_to_change of scalar * extent
      (** Storage: the address of its first element, for a function that reads the elements the
          storage has and writes some of them *)
  | Written of scalar * string list
      (** The address of a structure of numbers that the function writes, one for each name: each is
          a [mut] argument of the Truss call, copied into the structure before the call and back
          after it, so that it keeps its value where the function writes nothing *)
  | Always of int
      (** A number that is no argument of the Truss call: the function always gets it *)
  | Fixed of number
      (** A number of the system that is no argument of the Truss call, such as the request that a
          row of [fcntl] is for *)

type result =
  | Returns of scalar
  | Points_at of scalar  (** The number at the address returned, which is how [errno] is reached *)
  | Text
      (** The bytes at the address returned, up to a zero byte, as a view, with a last [mut Bool]
          argument, [found], that says whether the function returned an address at all *)
  | Never  (** The function does not return *)

type signature = {
  parameters : (string * passes) list;
  result : result;
  at_most : string option;
      (** The parameter that bounds the result: a result that is not negative is at most the number
          passed for it, as [read] returns no more than the count it was given *)
}
(** A function as Truss calls it: how each parameter of the C function is given. *)

(** A C type as a declaration writes it: [char *const *] is
    [Pointer (Const (Pointer (Named "char")))]. *)
type c_type =
  | Void
  | Named of string  (** A type C or a header names with words: [int], [unsigned long], [mode_t] *)
  | Struct of string  (** [struct timespec] *)
  | Const of c_type
  | Pointer of c_type

val show_c_type : c_type -> string
(** As C writes it: [const char *]. *)

type declaration = {
  symbol : string;
  returns : c_type;
  never_returns : bool;  (** Declared [_Noreturn], as [_exit] is *)
  takes : c_type list;  (** The C type of each parameter *)
  variadic_from : int option;
      (** The first parameter that C passes through [...], which some systems pass differently from
          a named parameter *)
}
(** A function as one system's headers declare it. *)

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
  | Exit  (** [_exit], which ends the process at once *)
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
  | Proc_pidpath  (** Only macOS has it *)
  | Fcntl_dupfd_cloexec  (** [fcntl] with the request [F_DUPFD_CLOEXEC] *)
  | Fcntl_setfd_cloexec  (** [fcntl] with the request [F_SETFD] and the flag [FD_CLOEXEC] *)
  | Posix_spawn_file_actions_init
  | Posix_spawn_file_actions_destroy
  | Posix_spawn_file_actions_adddup2
  | Posix_spawn_file_actions_addopen
  | Posix_spawn_file_actions_addchdir  (** [posix_spawn_file_actions_addchdir_np] *)
  | Getdents64  (** Only Linux has it *)
  | Getattrlistbulk  (** Only macOS has it *)
  | Ioctl_tiocgwinsz  (** [ioctl] with the request [TIOCGWINSZ] *)
  | Tcgetattr
  | Tcsetattr  (** With [TCSAFLUSH] *)
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
  | Fcntl_getfl  (** [fcntl] with [F_GETFL], and then with [F_SETFL] *)
  | Fcntl_setfl
  | Addresses_of_host  (** The runtime's: a host's addresses, which it gets from [getaddrinfo] *)
  | Signals_wait
      (** The runtime's: blocks until one of the signals arrives and returns its number, or 0 if the
          calling task is cancelled first *)
  | Descriptor_watch
      (** The runtime's: returns a ticket for a descriptor and a direction, which is reading or
          writing, for a later [Descriptor_wait] *)
  | Descriptor_wait
      (** The runtime's: waits until the descriptor has become ready in the direction since the
          ticket was issued *)
  | Descriptors_watch
      (** The runtime's: returns a ticket for a later [Descriptors_wait] by the same task *)
  | Descriptors_wait
      (** The runtime's: waits until one of several descriptors has become readable since the ticket
          was issued *)
  | Sleep  (** The runtime's: waits for a time, or until the calling task is cancelled *)
  | Tasks_open
      (** The runtime's task functions, which the real [Tasks] implementation calls. This one
          creates a task group and returns its handle. *)
  | Tasks_join  (** Blocks until every task of the group has ended, then frees the group *)
  | Tasks_cancel
      (** Cancels the group's tasks. Returns 1 to the first caller for a group and 0 to later
          callers. *)
  | Tasks_cancelled  (** Whether the calling task has been cancelled *)
  | Tasks_watch  (** Returns a ticket for a key, for a later [Tasks_wait] *)
  | Tasks_wait  (** Blocks until the key has been woken after the ticket was issued *)
  | Tasks_wake  (** Wakes every task that is waiting on the key *)
  | Tasks_lock  (** Acquires a mutex, blocking while another task holds it *)
  | Tasks_unlock  (** Releases a mutex *)
  | Tasks_yield  (** Yields the thread to another task *)

val functions : function_ list

val function_name : function_ -> string
(** The name the standard library calls it by. *)

val is_runtime_function : function_ -> bool
(** Whether the function is the runtime's own, written in C beside the generated code, and not the C
    library's. The standard library calls it [runtime_] and its name. *)

val blocks : function_ -> bool
(** Whether a call of the function can block its thread for long: it waits for input, for a process,
    or for a storage device. Lowering brackets such a call with the runtime's blocking functions, so
    that a spare thread can run tasks in place of a thread whose call lasts, and so that the runtime
    can interrupt the call if its task is cancelled. Three kinds of function are not counted. A call
    on a socket does not block, because the standard library's sockets fail with [EAGAIN] where they
    would. A function that reads or mutates only a file's metadata, such as [stat], returns quickly
    on a local file system, and the standard library does not expect every such call to be
    interrupted. The runtime's own functions that wait park the calling task, or count its thread as
    blocked, themselves. *)

val available : system -> function_ -> bool
(** Whether the system's C library has the function. A program built for a system never calls one
    that the system lacks: the call is a failure, so the standard library asks first which system it
    is built for. *)

val signature : function_ -> signature
val declaration : system -> function_ -> declaration

val prototype : declaration -> string
(** The prototype a C file that includes no header writes before it calls the function. *)

val numbers : number list

val number_name : number -> string
(** Its name in C. *)

val number_type : number -> scalar
val value : system -> number -> int

module For_testing : sig
  val check : system -> string
  (** A C file that includes the system's own headers and compiles only if every number has the
      value given here, every prototype is the one the headers declare, and every structure a
      function takes is laid out as the storage passed for it. *)
end
