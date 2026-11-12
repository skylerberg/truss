(* Running a program as a child process, with no shell. *)

(* Runs a program and returns its exit status, its standard output, and its
   standard error. A program ended by a signal has status [128 + signal].
   With [input], the program reads that as its standard input; without, it
   reads this process's. With [on_output], each piece of standard output is
   also handed to it as soon as it is read, for a driver that shows
   progress. With [time_limit], in milliseconds, a program still running
   then is killed, and its status is [128 + SIGKILL]. Each pair of
   [environment] sets one variable for the program over this process's
   environment. *)
val run :
  ?environment:(string * string) list ->
  ?input:string ->
  ?on_output:(string -> unit) ->
  ?time_limit:int ->
  string ->
  string list ->
  int * string * string

(* Runs a program on this process's standard input, output, and error, and
   returns its exit status, as [run] gives it. *)
val run_attached : string -> string list -> int
