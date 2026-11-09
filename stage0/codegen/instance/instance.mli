(* Instances: one copy of a definition's code, for one set of type arguments
   and capability sets. See CODEGEN.md, "Instances". *)

type capabilities = Path.t list list
(** The capability set bound to each capability parameter, in order, each sorted *)

type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list; capabilities : capabilities }
      (** A function, a method, or a method of an [impl], whether written, derived, or provided by
          the trait, which the checked form says. A method's type arguments are its type's, then its
          own; an [impl] method's are the [impl]'s, then the method's own. *)
  | Constant of Path.t  (** A constant's static data *)
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty  (** The built-in debug output *)
  | Cursor_next of Ground.yielding  (** The state machine of a pulled yielding method *)
  | Cursor_drop of Ground.yielding
  | Adapter of key
      (** A named function used as a function value: it takes the environment and ignores it *)

val compare : key -> key -> int
val equal : key -> key -> bool

(* The canonical encoding, in deterministic CBOR. *)
val encode : key -> Cbor.t

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
