(** The C library as the standard library calls it: its functions and the numbers its headers
    define, for each system stage0 builds for. How Truss calls a function is the same on every
    system; its symbol, its C types, and a number's value are the system's. *)

type os = Linux | Macos
type architecture = X86_64 | Arm64

type system = { os : os; architecture : architecture }
(** A system stage0 builds for. *)

val oses : os list
val architectures : architecture list
val os_name : os -> string
val system_name : system -> string

val host : system option
(** The system this compiler was built for, which is the one it runs on and builds programs for, or
    [None] where that is a system it knows no C library of. *)

(** A number that Truss and C both have. *)
type scalar = UInt8 | Int32 | Int64 | UInt64 | USize | ISize | Float64

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

(** How many elements a function reads or writes through an address it is given. The prover holds
    every call to it: a view has that many elements, and storage has room for that many. *)
type extent =
  | Counted of { by : string; each : int }
      (** [each] elements for each one of the number passed for the parameter [by] *)
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
      (** A structure of numbers of one type that the function writes: the address of one, whose
          numbers then go to [mut] arguments of these names, one each *)
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

type declaration = {
  symbol : string;
  returns : string;  (** The C type it returns *)
  takes : string list;  (** The C type of each parameter *)
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
  | Nanosleep
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

val functions : function_ list

val function_name : function_ -> string
(** The name the standard library calls it by. *)

val available : system -> function_ -> bool
(** Whether the system's C library has the function. A program built for a system never calls one
    that the system lacks: the call is a failure, so the standard library asks first which system it
    is built for. *)

val signature : function_ -> signature
val declaration : system -> function_ -> declaration

val prototype : declaration -> string
(** What a C file that includes no header writes before it calls the function. *)

val numbers : number list

val number_name : number -> string
(** Its name in C. *)

val number_type : number -> scalar
val value : system -> number -> int

val check : system -> string
(** A C file that includes the system's own headers and compiles only if every number has the value
    given here, every prototype is the one the headers declare, and every structure a function takes
    is laid out as the storage passed for it. *)
