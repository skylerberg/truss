(* Instances: one copy of a definition's code, for one set of type arguments
   and capability sets. *)

(** A named function used as a function value: it takes the environment and ignores it *)
type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list }
      (** A function, a method, or a method of an [impl], whether written, derived, or provided by
          the trait, which the checked form says. Its generic arguments, capability sets included,
          are in the order of its generic parameters: a method's are its type's, then its own, and
          an [impl] method's are the [impl]'s, then the method's own. *)
  | Constant of Path.t  (** A constant's static data *)
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty  (** The built-in debug output *)
  | Any_drop of Ground.ty
      (** Slot 0 of an [any] table: drops the value its untyped pointer points at, with exactly the
          signature the slot is called through *)
  | Encode of Ground.ty
      (** A value's binary form, which code run while compiling writes its result in *)
  | Evaluator of Path.t
      (** Code run while compiling: works out a constant's value and writes its binary form *)
  | Template_check of { from_template : Path.t; texts : string list }
      (** Code run while compiling: a tag's [from_template] clauses that can run, worked out for a
          template of these literal texts and no parts, each written out as a [Bool] *)
  | Cursor_next of Ground.yielding
      (** The state machine of a pulled yielding method. Its drop is the [Drop] of its cursor type.
      *)
  | Adapter of { function_ : key; ty : Ground.function_type }
  | Entry of key
      (** The entry for an [impl]'s method of a capability: takes the evidence, then calls the
          method on its implementation with the evidence that implementation captured *)
  | Table of { impl : Path.t; type_arguments : Ground.argument list }
      (** A capability [impl]'s table of entries, one for each of the capability's methods *)
  | Real_evidence of Path.t
      (** The evidence for the real implementation of a standard capability, which a program's
          [main] is given *)
  | Program_main of Path.t  (** The C [main]'s Truss side: it calls the program's [main] *)
  | Any_entry of key
      (** The entry for an [impl]'s method in an [any] table: takes a pointer to the value *)
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
      (** The table of an [any] value of a type and trait: the type's drop, then an entry for each
          of the trait's methods *)

val compare : key -> key -> int
val equal : key -> key -> bool

(* The canonical encoding, in deterministic CBOR, with each path written by
   [path], as in [Ground.encode]. *)
val encode : ?path:(Path.t -> Cbor.t) -> key -> Cbor.t

(* The C symbol of an instance: [t_], then its path and type arguments, with
   markers between them that no Truss name can contain. A name longer than
   200 bytes keeps its first 180 bytes and adds a hash of the whole name.
   Two different keys never give one symbol. *)
val symbol : key -> string

(* A path as part of a C name, such as [standard__list__List]. *)
val path_symbol : Path.t -> string

(* The C name of a type's [struct] or [typedef], made the same way. *)
val type_symbol : Ground.ty -> string

(* A readable form, for tests and messages. *)
val to_string : key -> string
