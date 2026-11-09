(* Instances: one copy of a definition's code, for one set of type arguments
   and capability sets. See CODEGEN.md, "Instances". *)

type capabilities = Ground.definition list list
(** The capability set bound to each capability parameter, in order, each sorted by path *)

type key =
  | Function of {
      definition : Ground.definition;
      type_arguments : Ground.argument list;
      capabilities : capabilities;
    }  (** A top-level function *)
  | Method of {
      owner : Ground.definition;  (** The type the method belongs to *)
      name : string;
      receiver : Ground.mode option;  (** [None] for a method without [self] *)
      type_arguments : Ground.argument list;  (** The type's arguments, then the method's own *)
      capabilities : capabilities;
    }
  | Impl_method of {
      trait : Ground.definition;
      trait_arguments : Ground.argument list;
      self : Ground.ty;
      name : string;
      receiver : Ground.mode option;
      type_arguments : Ground.argument list;  (** The method's own *)
      capabilities : capabilities;
    }
      (** A method of an [impl], written, derived, or provided by the trait, which one the checked
          form says *)
  | Constant of Ground.definition  (** A constant's static data *)
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty  (** The built-in debug output *)
  | Cursor_next of Ground.yielding  (** The state machine of a pulled yielding method *)
  | Cursor_drop of Ground.yielding
  | Adapter of key
      (** A named function used as a function value: it takes the environment and ignores it *)

val compare : key -> key -> int

(* The canonical encoding, in deterministic CBOR. *)
val encode : key -> Cbor.t
val equal : key -> key -> bool

(* The definition whose position anchor an instance's sites are relative to,
   or [None] for generated code with no source. *)
val definition : key -> Ground.definition option

(* The C symbol of an instance: [t_], then its path and type arguments, with
   every character C does not allow in a name replaced. A name longer than
   200 bytes keeps its first 180 bytes and adds a hash of the whole key.
   Two different keys never give one symbol. *)
val symbol : key -> string

(* A definition's path as part of a C name, such as [standard__list__List]. *)
val path_symbol : Ground.definition -> string

(* The C name of a type's [struct] or [typedef], made the same way. *)
val type_symbol : Ground.ty -> string

(* A readable form, for tests and messages. *)
val to_string : key -> string
