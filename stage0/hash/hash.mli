(** Content hashes of resolved definitions, in parts. See TYPECHECKER.md, "Hashing", and DESIGN.md,
    "The hash format".

    A definition's hash comes from its resolved structure: names are replaced by what they refer to,
    and spans, node ids, parentheses, blank lines, and how a literal was written are left out.
    Clauses are hashed in groups by kind, keeping the order within each kind, and a record's field
    order counts only when it derives [Ordered]. Each part is hashed on its own, so a result that
    reads one part depends only on that part. *)

type digest = string
(** The format version, the algorithm, and the 32-byte BLAKE3 digest of the part's deterministic
    CBOR encoding. *)

val format_version : int
val show : digest -> string

type part =
  | Interface  (** A function's or method's interface; a trait's or [impl]'s interface. *)
  | Contract  (** [requires], [ensures], [decreases], and [cost]. *)
  | Default of string  (** The default of the named parameter. *)
  | Body
  | Proof of int  (** The [proof] blocks of a body, in order. *)
  | Shape  (** A type's generic parameters, fields or variants, marks, and [derives]. *)
  | Invariant of int
  | Potential
  | Value  (** A constant's value. *)
  | Member of string * part  (** A part of a trait's or [impl]'s member, by name. *)
  | Law of string

val show_part : part -> string

val parts : (Resolve.Names.key, (part * digest) list option) Query.query
(** The parts of a definition and their hashes, or [None] if there is no such definition. *)
