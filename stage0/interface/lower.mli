(** Lowering written types to [Types.ty], from a definition's resolved form. Lowering reports the
    errors that a type position alone determines: a name that is not a type, a wrong number of
    arguments, an associated type that no bound declares. It does not check bounds. *)

type context = {
  database : Query.context;
  resolved : Resolve.resolved;
  bounds : (Types.parameter, Types.trait_reference list) Hashtbl.t;
  self_type : Types.ty option;  (** What [Self] means here. *)
  self_trait : Types.trait_reference option;  (** In a trait, the trait [Self] implements. *)
  self_associated : (string * Types.ty) list;  (** In an [impl], its associated types. *)
  self_capabilities : (string * Types.capability_set) list;
      (** In an [impl], each associated capability set that its trait declares. *)
  diagnostics : Syntax.diagnostic list ref;  (** Shared by every copy of the context. *)
  named : (Syntax.span * Types.ty) list ref;
      (** Each named type lowered, for checking its bounds. *)
}

val create : Query.context -> Resolve.resolved -> context
val report : context -> Diagnostic.Code.types -> Syntax.span -> string -> unit
val error : context -> Diagnostic.Code.types -> Syntax.span -> string -> Types.ty

val bug : ('a, unit, string, 'b) format4 -> 'a
(** Resolution and lowering must agree. A disagreement is a compiler bug, and stopping is better
    than accepting the code. *)

val target : context -> Syntax.name -> Resolve.target option
val type_ : context -> Syntax.type_expression -> Types.ty

val trait_reference :
  ?capability:bool ->
  context ->
  Syntax.path_type ->
  (Types.trait_reference, Diagnostic.reported) result
(** A bound, an [impl]'s trait, or the trait after [any]. An [impl] may implement a capability too.
*)

val trait_bounds : context -> Syntax.path_type list -> Types.trait_reference list
val capabilities : context -> Syntax.capability_reference list -> Types.capability_set

val generics : context -> Path.t -> Syntax.generic_parameter list -> Types.generic list
(** Generic parameters, each named by its owner and its own name, as resolution names them. *)

val terminates : Syntax.clause list -> bool
(** Whether a signature promises termination: it has a [time] clause. *)

val signature :
  context ->
  owner:Path.t ->
  head:Types.generic list ->
  self_type:Types.ty option ->
  Syntax.signature ->
  Types.signature
