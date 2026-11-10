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
  | Written of scalar * string list
  | Always of int
  | Environment

type result = Returns of scalar | Points_at of scalar | Text
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

(* Everything about a function, written once: each parameter with how Truss
   passes it and its C type on each system. Only the check reads the rest:
   [headers] declare the function; [layout] is what must hold of a structure
   it takes for the storage passed to be that structure; and [named] gives a
   parameter the type the headers call it by, where that is a name only the
   headers have and the C that is emitted says [void]. *)
type row = {
  symbol : os -> string;
  returns : string;
  result : result;
  parameters : (string * passes * (os -> string)) list;
  variadic_from : int option;
  headers : string list;
  layout : string list;
  named : (string * string) list;
}

let everywhere c (_ : os) = c
let size = everywhere "__SIZE_TYPE__"

let describe function_ =
  let row ?(symbol = everywhere (function_name function_)) ?variadic_from ?(layout = [])
      ?(named = []) returns result parameters ~headers =
    { symbol; returns; result; parameters; variadic_from; headers; layout; named }
  in
  match function_ with
  | Write ->
      row "long" (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("bytes", Elements UInt8, everywhere "const void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Read ->
      row "long" (Returns ISize)
        [
          ("descriptor", Value Int32, everywhere "int");
          ("buffer", Room UInt8, everywhere "void *");
          ("count", Value USize, size);
        ]
        ~headers:[ "unistd.h" ]
  | Open ->
      row "int" (Returns Int32) ~variadic_from:2
        [
          ("path", Elements UInt8, everywhere "const char *");
          ("flags", Value Int32, everywhere "int");
          ("mode", Value Int32, everywhere "int");
        ]
        ~headers:[ "fcntl.h" ]
  | Close ->
      row "int" (Returns Int32)
        [ ("descriptor", Value Int32, everywhere "int") ]
        ~headers:[ "unistd.h" ]
  | Errno ->
      row "int *" (Points_at Int32) []
        ~symbol:(function Linux -> "__errno_location" | Macos -> "__error")
        ~headers:[ "errno.h" ]
  | Clock_gettime ->
      row "int" (Returns Int32)
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
      row "int" (Returns Int32)
        [
          ("buffer", Written (UInt64, [ "value" ]), everywhere "void *"); ("count", Always 8, size);
        ]
        ~headers:[ "sys/types.h"; "sys/random.h" ]
  | Getenv ->
      row "char *" Text
        [ ("name", Elements UInt8, everywhere "const char *") ]
        ~headers:[ "stdlib.h" ]
  | Posix_spawnp ->
      row "int" (Returns Int32)
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
      row "int" (Returns Int32)
        [
          ("process", Value Int32, everywhere "int");
          ("status", Written (Int32, [ "status" ]), everywhere "int *");
          ("options", Value Int32, everywhere "int");
        ]
        ~headers:[ "sys/wait.h" ]
  | Snprintf ->
      (* The one use: a float written with a number of digits, by a format
         that takes the two. *)
      row "int" (Returns Int32) ~variadic_from:3
        [
          ("buffer", Room UInt8, everywhere "char *");
          ("size", Value USize, size);
          ("format", Elements UInt8, everywhere "const char *");
          ("precision", Value Int32, everywhere "int");
          ("value", Value Float64, everywhere "double");
        ]
        ~headers:[ "stdio.h" ]
  | Strtod ->
      row "double" (Returns Float64)
        [
          ("text", Elements UInt8, everywhere "const char *");
          ("end", Always 0, everywhere "char **");
        ]
        ~headers:[ "stdlib.h" ]

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
    returns = row.returns;
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

let number_type (_ : number) = Int32

let number_headers = function
  | O_rdonly | O_wronly | O_creat | O_trunc | O_cloexec -> [ "fcntl.h" ]
  | Eintr | Enoent | Eacces | Eio | Einval -> [ "errno.h" ]
  | Clock_realtime -> [ "time.h" ]

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
  let reached symbol c count scalar =
    holds
      (symbol ^ " reaches numbers of another size")
      (Printf.sprintf "sizeof(*(%s)0) == %d" c (count * bytes scalar))
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
            | Returns _ | Text -> [])
          @ List.filter_map
              (fun (_, passes, c) ->
                match passes with
                | Written (scalar, names) when not (is_void (c os)) ->
                    Some (reached declaration.symbol (c os) (List.length names) scalar)
                | Written _ | Value _ | Elements _ | Room _ | Always _ | Environment -> None)
              row.parameters)
        functions)
