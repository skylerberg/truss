(* Finding the C compiler, knowing exactly which one it is, and running it. *)

type t = {
  compiler : string;  (** The path or name it is run by *)
  identity : string;
      (** Its [--version] output and path, which is part of every object file's key, so a new
          compiler rebuilds objects but invalidates no test result *)
}

(* The compiler named by [TRUSS_CC], or else [clang], or else [cc]. *)
val find : unit -> (t, string) result

(* [TRUSS_CFLAGS], whose flags, separated by spaces, are added to
   every command that compiles or links, such as a sanitizer's. *)
val added_flags_variable : string
val split_flags : string -> string list

(* The flags every Truss C file is compiled with, which keep generated code
   free of undefined behavior and floats exact. *)
val required_flags : string list

type optimization = O1 | O2

(* The flags for optimizing across object files when they are linked,
   given when compiling and when linking: ThinLTO for clang, LTO
   otherwise. *)
val link_time_optimization : t -> string list
val optimization_flag : optimization -> string

(* Compiles one C file to an object file. [extra] adds flags, such as the
   tests' [-Wall -Wextra -Werror]. *)
val compile :
  t ->
  optimization:optimization ->
  ?extra:string list ->
  source:string ->
  output:string ->
  unit ->
  (unit, string) result

(* Links object files into a program against the platform's libc, with
   [extra] flags, such as a sanitizer's, which the objects were compiled
   with too. *)
val link :
  t -> ?extra:string list -> objects:string list -> output:string -> unit -> (unit, string) result
