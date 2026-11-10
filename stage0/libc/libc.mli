(** The C library as the standard library calls it: its functions and the numbers its headers
    define, for each system stage0 builds for. How Truss calls a function is the same on every
    system; its symbol, its C types, and a number's value are the system's. *)

type os = Linux | Macos

val os_name : os -> string

val host : os option
(** The system this compiler was built for, which is the one it runs on and builds programs for, or
    [None] where that is a system it knows no C library of. *)

(** A number that Truss and C both have. *)
type scalar = UInt8 | Int32 | Int64 | USize | ISize

(** How an argument reaches the function. There is no pointer type in Truss, so memory is passed as
    a view or as storage, and the function is given an address into it. *)
type passes =
  | Value of scalar  (** A number, converted to the parameter's C type *)
  | Elements of scalar  (** A view: the address of its elements, which the function only reads *)
  | Room of scalar
      (** Storage: the address after its last element, for a function that fills room the storage
          has beyond its length *)

type result =
  | Returns of scalar
  | Points_at of scalar  (** The number at the address returned, which is how [errno] is reached *)

type signature = { parameters : (string * passes) list; result : result }
(** A function as Truss calls it. *)

type declaration = {
  symbol : string;
  returns : string;  (** The C type it returns *)
  takes : string list;  (** The C type of each parameter *)
  variadic_from : int option;
      (** The first parameter that C passes through [...], which some systems pass differently from
          a named parameter *)
}
(** A function as one system's headers declare it. *)

type function_ = Write | Read | Open | Close | Errno | Clock_gettime | Getentropy

val functions : function_ list

val function_name : function_ -> string
(** The name the standard library calls it by. *)

val signature : function_ -> signature
val declaration : os -> function_ -> declaration

val prototype : declaration -> string
(** What a C file that includes no header writes before it calls the function. *)

type number =
  | O_rdonly
  | O_wronly
  | O_creat
  | O_trunc
  | O_append
  | O_cloexec
  | Eintr
  | Enoent
  | Eacces
  | Clock_realtime

val numbers : number list

val number_name : number -> string
(** Its name in C. *)

val number_type : number -> scalar
val value : os -> number -> int

val check : os -> string
(** A C file that includes the system's own headers and compiles only if every number has the value
    given here, every prototype is the one the headers declare, and every structure a function takes
    is laid out as the storage passed for it. *)
