(* The two ways the compiler fails that are not the program's fault: a bug
   in the compiler, and a valid program this compiler cannot build yet.

   Every stage raises these, through [bug] and [unsupported], and nothing
   else for a broken invariant, so a driver can tell them from a failure of
   the program or of the machine, and reports each in one place. *)

(* A broken invariant: the stage that found it, what it found, and what the
   compiler was doing, innermost first. *)
type t = { stage : string; message : string; doing : string list }

exception Bug of t

val bug : stage:string -> ('a, unit, string, 'b) format4 -> 'a

(* A position within a definition, which a driver turns into a file and
   line. *)
type site = { definition : Path.t; line : int; column : int }
type unsupported = { what : string; at : site option }

exception Unsupported of unsupported

val unsupported : ?at:site -> ('a, unit, string, 'b) format4 -> 'a

(* Runs [f]. A bug raised inside it is raised again with [doing] added to
   what the compiler was doing, and an exception the standard library
   raises for a broken invariant, such as [Not_found] or
   [Invalid_argument], becomes a bug of [stage]. *)
val within : stage:string -> string -> (unit -> 'a) -> 'a

(* A bug as a report: the stage and what it found, then each thing the
   compiler was doing, a line each. *)
val to_string : t -> string
