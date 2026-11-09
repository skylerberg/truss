(* What a build compiles, and what keys a test's result. See CODEGEN.md,
   "Instances" and "Test results".

   A build starts from roots and compiles only what they reach: each
   instance that an instance calls, takes as a function value, reads as a
   constant, or drops. The walk takes references in the order they appear
   in the LIR, so the result is the same on every run. *)

(* The instances an instance refers to, in the order they first appear. *)
val references : Memory_layout.env -> Lir.t -> Instance.key list

(* Every instance reachable from the roots, roots first, each once, in the
   order it is first reached. [lookup] gives what an instance compiles to. *)
val reachable :
  Memory_layout.env ->
  lookup:(Instance.key -> Lir.compiled) ->
  Instance.key list ->
  Lir.compiled list

(* The same instances in the same order, each with the first way the walk
   reached it: the keys from a root to the instance, both included. *)
val reached :
  Memory_layout.env ->
  lookup:(Instance.key -> Lir.compiled) ->
  Instance.key list ->
  (Lir.compiled * Instance.key list) list

(* The key of a test's result: the hash of the LIR of everything the test
   can reach, with every instance and every path replaced by a number given
   in the order it is first reached, and the version of code generation.
   Two programs that differ only in the names of definitions give the same
   key, so renaming or moving a definition finds its tests' results already
   done, and any change to what the test can run changes the key. *)
val test_key : Memory_layout.env -> lookup:(Instance.key -> Lir.compiled) -> Instance.key -> string
