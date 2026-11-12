(** The interfaces of definitions, as queries.

    [lowered_interface] lowers a definition's outward-facing part and keeps what lowering reported.
    The other queries project one interface out of it by path, so a definition's diagnostics
    changing never re-checks a definition that reads its interface. *)

type interface =
  | Function_interface of Types.signature
  | Type_interface of Types.type_interface
  | Trait_interface of Types.trait_interface
  | Impl_interface of Types.impl_interface
  | Constant_interface of Types.constant_interface
  | Test_interface of Types.capability list
  | Theorem_interface of Types.signature
  | Law_proof_interface of {
      generics : Types.generic list;
      trait : Types.trait_reference;
      law : string;
      for_type : Types.ty;
    }  (** The subject of a law's proof: a law of a trait, for a type's [impl]. *)
  | Error_interface of Diagnostic.reported
      (** A definition whose header did not parse: everything is accepted of it. *)

type lowered_interface = {
  interface : interface;
  diagnostics : Syntax.diagnostic list;
  named : (Syntax.span * Types.ty) list;  (** Each named type written, for checking its bounds. *)
  bounds : (Types.parameter * Types.trait_reference list) list;
      (** The generic parameters' bounds. *)
}

val lower :
  Query.context ->
  Resolve.Names.key ->
  Syntax.definition ->
  Resolve.resolved ->
  lowered_interface * Lower.context

val lowered_interface : (Resolve.Names.key, lowered_interface option) Query.query

val interface : (Path.t, interface option) Query.query
(** The interface a path names, from its definition with ordinal 0. *)

val in_declared_order :
  Query.context -> Path.t -> variant:string option -> name:('a -> string) -> 'a list -> 'a list
(** The fields of a variant of a type, or of a record, in declaration order. [name] gives the name
    of a field. *)

val type_interface : (Path.t, Types.type_interface option) Query.query
(** A type's interface, a built-in's included. [None] for a path that is not a type, and the [Error]
    shape for a type whose definition did not parse. *)

val signature : (Path.t, Types.signature option) Query.query
(** The signature of a function or a method, wherever it is written. *)

val signature_or_report :
  Query.context -> Path.t -> (Types.signature, Diagnostic.reported) result option
(** A function's signature for checking a use of it, or, when its header or its member of a trait
    did not parse, the report of that, since everything is accepted of it. *)

val trait_interface : (Path.t, Types.trait_interface option) Query.query
val impl_interface : (Path.t, Types.impl_interface option) Query.query
val constant_type : (Path.t, Types.ty option) Query.query
