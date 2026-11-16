type os = Linux | Macos
type architecture = X86_64 | Arm64
type system = { os : os; architecture : architecture }

val oses : os list
val architectures : architecture list
val show_system : system -> string
val host : system option

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

val show_c_type : c_type -> string

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
  | Dup2
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

val functions : function_ list
val show_function : function_ -> string
val is_runtime_function : function_ -> bool
val is_blocking : function_ -> bool
val is_available : system -> function_ -> bool
val make_signature : function_ -> signature
val make_declaration : system -> function_ -> declaration
val render_prototype : declaration -> string
val numbers : number list
val show_number : number -> string
val classify_number : number -> scalar
val evaluate_number : system -> number -> int

module For_testing : sig
  val check : system -> string
end
