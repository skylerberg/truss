(* The instances a build compiles, and the key of a test's result.

   A build starts from roots and compiles only the instances they reach: each
   instance that an instance calls, takes as a function value, reads as a
   constant, or drops. The walk takes references in the order they appear
   in the LIR, so the result is the same on every run. *)

(* The instances an instance refers to, in the order they first appear. *)
val references : Memory_layout.env -> Lir.t -> Instance.key list

(* Every instance reachable from the roots, roots first, each once, in the
   order it is first reached. [lookup] gives an instance's compiled form. *)
val reachable :
  Memory_layout.env ->
  lookup:(Instance.key -> Lir.compiled) ->
  Instance.key list ->
  Lir.compiled list

(* Every instance that running the roots can reach, each with the first way
   to it. It walks as [reachable] does, but for the entries of a capability's
   table: a build compiles them all, and running reaches one only where code
   that runs calls that method of the capability, whose way it is given. *)
val running :
  Memory_layout.env ->
  lookup:(Instance.key -> Lir.compiled) ->
  Instance.key list ->
  (Lir.compiled * Instance.key list) list

(* A unit's references, and its key. *)
val compiled_key : Lir.compiled -> Instance.key
val compiled_references : Memory_layout.env -> Lir.compiled -> Instance.key list

(* The hash of an instance's compiled form, by itself: its encoding with
   each instance it refers to written as that instance's place among
   [references], itself as a mark, and each path as a number given in the
   order paths are first met. It holds no name, so renaming or moving a
   definition changes no hash. *)
val own_hash : references:Instance.key list -> Lir.compiled -> string

module Keys : Map.S with type key = Instance.key

(* The groups of instances that reach each other, among everything the
   roots reach through [edges]: for each instance of such a group, the
   group's instances, in order. An instance that reaches itself only
   directly is in no group. *)
val groups :
  edges:(Instance.key -> Instance.key list) -> Instance.key list -> Instance.key list Keys.t

(* The key of everything an instance that is in no group can reach: its own
   hash, and the key of each instance it refers to, in order. *)
val unit_key : own:string -> string list -> string

(* The key of everything an instance of a group can reach: the group's
   instances in the order a walk from the instance first reaches them, each
   as its own hash and its references, a number for an instance of the
   group and the key of everything it can reach for any other. [link] gives
   an instance's own hash and its references. *)
val group_key :
  link:(Instance.key -> string * Instance.key list) ->
  deep:(Instance.key -> string) ->
  members:Instance.key list ->
  Instance.key ->
  string
