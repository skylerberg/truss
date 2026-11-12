(** The facts about a definition that are available from its syntax alone: its location, its generic
    parameters, and the names of its associated types. Lowering a type reads these instead of whole
    interfaces, so a recursive type, whose fields name the type itself, never causes a query cycle.
*)

val key : (Path.t, Resolve.Names.key option) Query.query
(** The definition a path names, with ordinal 0. A method or a member constant is found among its
    owner's members, since it may be written in any file of its package. *)

val definition : Query.context -> Path.t -> (Resolve.Names.key * Syntax.definition) option

type generic_kind = Type_kind | Value_kind | Capability_kind

val generics_of : (Path.t, (string * generic_kind) list option) Query.query
(** The generic parameters a type, trait, or capability takes, which naming it with arguments needs.
    [None] for a definition whose header did not parse, which accepts any arguments. *)

type trait_header = {
  associated : string list;
  capabilities : string list;
  required : Path.t list;
  laws : string list;
}

val trait_header : (Path.t, trait_header option) Query.query
(** The names of a trait's associated types, of its associated capability sets, and of its laws, and
    the traits it requires, as resolution named them. *)

val trait_closure : Query.context -> ?seen:Path.t list -> Path.t -> Path.t list
(** The traits a trait requires, directly or not, with itself first. Stops at a cycle. *)

val kind_of : Query.context -> Path.t -> Resolve.Names.named option
