type os = Linux | Macos

let os_name = function Linux -> "Linux" | Macos -> "macOS"

let host =
  let system = Built_for.system in
  if system = "macosx" then Some Macos
  else if String.starts_with ~prefix:"linux" system then Some Linux
  else None

type scalar = UInt8 | Int32 | Int64 | UInt64 | USize | ISize | Float64

type passes =
  | Value of scalar
  | Elements of scalar
  | Room of scalar
  | Elements_to_change of scalar
  | Written of scalar * string list
  | Always of int
  | Environment

type result = Returns of scalar | Points_at of scalar | Text | Never
type signature = { parameters : (string * passes) list; result : result }

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

(* Everything about a function, written once: each parameter with how Truss
   passes it and its C type on each system. Only the check reads the rest:
   [headers] declare the function; [layout] is what must hold of a structure
   it takes for the storage passed to be that structure; and [named] gives a
   parameter the type the headers call it by, where that is a name only the
   headers have and the C that is emitted says [void]. *)
type row = {
  symbol : os -> string;
  returns : os -> string;
  result : result;
  parameters : (string * passes * (os -> string)) list;
  variadic_from : int option;
  headers : string list;
  layout : string list;
  named : (string * string) list;
}

let everywhere c (_ : os) = c
let size = everywhere "__SIZE_TYPE__"

(* [off_t], a position in a file. *)
let offset = function Linux -> "long" | Macos -> "long long"

let describe function_ =
  let row ?(symbol = everywhere (function_name function_)) ?variadic_from ?(layout = [])
      ?(named = []) returns result parameters ~headers =
    { symbol; returns; result; parameters; variadic_from; headers; layout; named }
  in
  match function_ with
  | Write ->
      row (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements UInt8, everywhere "const void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Read ->
      row (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room UInt8, everywhere "void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Open ->
      row (everywhere "int") (Returns Int32) ~variadic_from:2
        [
          ("path", Elements UInt8, everywhere "const char *");
          ("flags", Value Int32, everywhere "int");
          ("mode", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Close ->
      row (everywhere "int") (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int") ]
        ~headers:[ "unistd.h" ]
  | Errno ->
      row (everywhere "int *") (Points_at Int32) []
        ~symbol:(function Linux -> "__errno_location" | Macos -> "__error")
        ~headers:[ "errno.h" ]
  | Clock_gettime ->
      row (everywhere "int") (Returns Int32)
        [
          (* macOS makes [clockid_t] an enumeration with no negative member,
             which C gives the representation of this type. *)
          ("clock", Value Int32, function Linux -> "int" | Macos -> "unsigned int");
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
        [ ("name", Elements UInt8, everywhere "const char *") ]
        ~headers:[ "stdlib.h" ]
  | Posix_spawnp ->
      row (everywhere "int") (Returns Int32)
        [
          ("process", Written (Int32, [ "process" ]), everywhere "int *");
          ("program", Elements UInt8, everywhere "const char *");
          ("file_actions", Always 0, everywhere "const void *");
          ("attributes", Always 0, everywhere "const void *");
          ("arguments", Elements USize, everywhere "char *const *");
          ("environment", Environment, everywhere "char *const *");
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
          ("buffer", Room UInt8, everywhere "char *");
          ("size", Value USize, size);
          ("format", Elements UInt8, everywhere "const char *");
          ("precision", Value Int32, everywhere "int");
          ("value", Value Float64, everywhere "double");
        ]
        ~headers:[ "stdio.h" ]
  | Strtod ->
      row (everywhere "double") (Returns Float64)
        [
          ("text", Elements UInt8, everywhere "const char *");
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
      row (everywhere "int") (Returns Int32)
        [
          ("waited_for", Elements_to_change Int32, everywhere "struct pollfd *");
          ("count", Value USize, function Linux -> "unsigned long" | Macos -> "unsigned int");
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
      row (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room UInt8, everywhere "void *");
          ("count", Value USize, size);
          ("offset", Value Int64, offset);
        ]
        ~headers:[ "unistd.h" ]
  | Pwrite ->
      row (everywhere "long") (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements UInt8, everywhere "const void *");
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

let signature function_ =
  let row = describe function_ in
  {
    parameters = List.map (fun (name, passes, _) -> (name, passes)) row.parameters;
    result = row.result;
  }

let declaration os function_ : declaration =
  let row = describe function_ in
  {
    symbol = row.symbol os;
    returns = row.returns os;
    takes = List.map (fun (_, _, c) -> c os) row.parameters;
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

let number_type (_ : number) = Int32

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
  | Sigkill -> [ "signal.h" ]

let value os number =
  match (number, os) with
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

(* How many bytes a number the function reaches through an address takes,
   which the C type it is declared with must take too. [USize] has no one
   width: code run while compiling for a narrower target has the target's. *)
let bytes = function
  | UInt8 -> 1
  | Int32 -> 4
  | Int64 | UInt64 | Float64 -> 8
  | USize | ISize -> invalid_arg "a USize the C library reaches through an address"

let check os =
  let headers =
    List.fold_left
      (fun seen header -> if List.mem header seen then seen else seen @ [ header ])
      []
      (List.concat_map (fun function_ -> (describe function_).headers) functions
      @ List.concat_map number_headers numbers)
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
       "#undef _FORTIFY_SOURCE\n#define _FORTIFY_SOURCE 0\n#define _DEFAULT_SOURCE\n";
     ]
    @ List.map (fun header -> Printf.sprintf "#include <%s>\n" header) headers
    @ List.map
        (fun number ->
          holds (number_name number)
            (Printf.sprintf "%s == %d" (number_name number) (value os number)))
        numbers
    @ List.concat_map
        (fun function_ ->
          let row = describe function_ and declaration = declaration os function_ in
          let as_the_headers_name_it =
            {
              declaration with
              takes =
                List.map
                  (fun (name, _, c) ->
                    match List.assoc_opt name row.named with Some named -> named | None -> c os)
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
                | Written (scalar, names) when not (is_void (c os)) ->
                    Some (reached declaration.symbol (c os) (List.length names) scalar)
                | Written _ | Value _ | Elements _ | Room _ | Elements_to_change _ | Always _
                | Environment ->
                    None)
              row.parameters)
        functions)
