(* Outlining: each region of a [parallel] statement becomes a nested
   function, and the statement a fork of them.

   It runs after drops are elaborated, while a region is still code of the
   function around it, run in place and in order. So what a region owns,
   takes, and drops is already known, and moving it out changes only
   how it reaches the locals it shares with the code around it: through an
   environment that holds the address of each. *)

(* An instance with no region left in it. Each region is a nested function,
   added after the ones the instance had. *)
val instance : Memory_layout.env -> Lir.t -> Lir.t
