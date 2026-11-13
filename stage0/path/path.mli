(** A definition's name across stages: its package, module, and name. Results name other definitions
    by path, never by a hash. Code generation's instance keys use the same paths. *)

type package = { owner : string option; name : string }
(** A package's name: [weather] has no owner, and [acme::geometry], a package from the registry, has
    the owner [acme]. *)

val package_parts : package -> string list
(** The names a path writes a package with: [acme::geometry] is [acme] and [geometry]. *)

val show_package : package -> string
(** As a manifest writes it: [acme::geometry]. *)

val compare_package : package -> package -> int
(** In the order of their text, which is the order a lock file lists packages in. *)

val parse_names : string -> string list option
(** The names a text joins with [::]: [a::b::Name] is [a], [b], and [Name]; [None] where a name is
    empty or a [:] is not part of a [::]. *)

val parse_package : string -> package option
(** A package from its text, one name or two joined by [::]; [None] for any other text. It does not
    check that the names are [lower_snake_case]. *)

type module_ = { package : package; modules : string list }
(** [weather::forecast::hourly] is the package [weather] and the modules [forecast; hourly]: the
    directory [forecast/hourly] of the package. A package's root module, its top directory, has no
    modules. [acme::geometry::vector] is the package [acme::geometry] and the module [vector]. *)

val split_module : is_package:(package -> bool) -> string list -> module_ option
(** The module a full path's names start with: the package of the first two names, where
    [is_package] holds for it, or else of the first, with the rest as modules. [None] where neither
    is a package. *)

val module_parts : module_ -> string list
(** The names a module's full path is written with: its package's, then its modules'. *)

val show_module : module_ -> string

type file = { module_ : module_; name : string }
(** A file of a module, by its name without [.truss]: [weather/forecast/hourly.truss] is the file
    [hourly] of the module [weather::forecast]. A module is a directory, and all its files share one
    namespace. *)

val file_names : file -> string list
(** The file's path under its package's directory, by name: [forecast] and [hourly.truss]. *)

val show_file : file -> string
(** As in messages: [weather/forecast/hourly.truss]. *)

type type_head = { type_name : string; generics : string list }
(** A type as an [impl] or a law's proof writes it after [for]: [List[T]] is the name [List], as
    written, and the generic [T]. *)

val show_type_head : type_head -> string

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
  | Impl of { module_ : module_; trait : string; for_type : type_head }
      (** An [impl], named by its trait as written, such as ["From[Int32]"], and its type's head,
          since a type can implement one trait for several sets of arguments. *)
  | Derived of { type_ : t; trait : t }  (** The [impl] a [derives] clause stands for. *)
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : string; law : string; for_type : type_head }
      (** [proof Monoid.associative for Int64]: the trait as written, the law, and the type's head.
      *)

val standard_package : package
(** The package of the standard library. *)

val standard_module : string list -> module_
(** A module of the standard library: [standard_module [ "list" ]] is [standard::list]. *)

val standard : string list -> string -> t
(** A top-level definition of the standard library: [standard [ "list" ] "List"] is
    [standard::list::List]. *)

val package : t -> package
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
