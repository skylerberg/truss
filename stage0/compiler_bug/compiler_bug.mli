(* A bug in the compiler: a broken invariant, which is never the program's
   fault. A stage of the compiler raises it through [bug], and nothing else
   for a broken invariant, so a driver can tell it from a failure of the
   program or of the machine, and reports it in one place. A general
   library, such as [Incremental], raises [Invalid_argument] for a broken
   precondition, which [while_doing] turns into a bug of the stage that called
   it. *)

(* The stage that found the broken invariant, what it found, and what the
   compiler was doing, innermost first. *)
type t = { stage : string; message : string; doing : string list }

exception Bug of t

val bug : stage:string -> ('a, unit, string, 'b) format4 -> 'a

(* Runs [f]. A bug raised inside it is raised again with [doing] added to
   what the compiler was doing, and an exception the standard library
   raises for a broken invariant, such as [Not_found], [Invalid_argument],
   or a failed [assert], becomes a bug of [stage]. *)
val while_doing : stage:string -> string -> (unit -> 'a) -> 'a

(* A bug as a report: the stage and what it found, then each thing the
   compiler was doing, a line each. *)
val to_string : t -> string
