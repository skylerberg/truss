(** What every definition is named by, across stages: its package, module, and name. Results name
    other definitions by path, never by a hash. Code generation's instance keys use the same paths.
*)

type module_ = { package : string; modules : string list }
(** [weather::forecast::hourly] is the package [weather] and the modules [forecast; hourly]. A
    package's root module has no modules. A package from the registry has an owner in its name, so
    [acme::geometry::vector] is the package [acme::geometry] and the module [vector]. *)

val package_parts : string -> string list
(** A package's name as the names a path writes it with: [acme::geometry] is [acme] and [geometry].
*)

val module_parts : module_ -> string list
(** The names a module's full path is written with: its package's, then its modules'. *)

val show_module : module_ -> string

type receiver =
  | Static
  | Read
  | Mut
  | Own
      (** How a method takes [self]: [Static] for a method without [self], such as
          [List.with_capacity]. One name can have a version for each receiver. *)

val show_receiver : receiver -> string
(** How a method takes [self], as a message says it: [`mut self`], or [no `self`]. *)

type t =
  | Top of { module_ : module_; name : string }
      (** A function, type, trait, capability, constant, or theorem. *)
  | Method of { owner : t; name : string; receiver : receiver }
      (** A method of a type, of a trait, of a capability, or of an [impl]. *)
  | Member_constant of { owner : t; name : string }  (** [UInt8.maximum] *)
  | Impl of { module_ : module_; name : string }
      (** An [impl], named by its trait and type as written, such as ["From[Int32] for Int64"],
          since a type can implement one trait for several sets of arguments. *)
  | Derived of { type_ : t; trait : t }  (** The [impl] a [derives] clause stands for. *)
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; name : string }  (** ["Monoid.associative for Int64"] *)

val standard_package : string
(** The package of the standard library. *)

val standard_module : string list -> module_
(** A module of the standard library: [standard_module [ "list" ]] is [standard::list]. *)

val standard : string list -> string -> t
(** A top-level definition of the standard library: [standard [ "list" ] "List"] is
    [standard::list::List]. *)

val package : t -> string
(** The package a definition is in. A method or member constant is in its type's package, as every
    method must be, though it may be written in any file of it, so a path does not say which module
    holds a method. *)

val show : t -> string
(** As in messages: [standard::list::List.push], with [(mut self)] after a method's name for a
    version that takes [mut self] or [own self]. *)

val compare : t -> t -> int
val equal : t -> t -> bool

module Map : Map.S with type key = t
module Set : Set.S with type elt = t
