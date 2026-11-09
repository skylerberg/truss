(* Finding the C compiler, knowing exactly which one it is, and running it.
   See CODEGEN.md, "The C that is emitted" and "Building". *)

type t = {
  compiler : string;  (** The path or name it is run by *)
  identity : string;
      (** Its [--version] output and path, which is part of every object file's key, so a new
          compiler rebuilds objects but invalidates no test result *)
}

(* The compiler named by [TRUSS_CC], or else [clang], or else [cc]. *)
val find : unit -> (t, string) result

(* The flags every Truss C file is compiled with, which keep generated code
   free of undefined behavior and floats exact. *)
val required_flags : string list

type optimization = O1 | O2

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

(* Runs a program and returns its exit status, its standard output, and its
   standard error. A program ended by a signal has status [128 + signal].
   With [input], the program reads that as its standard input; without, it
   reads this process's. *)
val run : ?input:string -> string -> string list -> int * string * string

(* Runs a program on this process's standard input, output, and error, and
   returns its exit status, as [run] gives it. *)
val run_attached : string -> string list -> int
