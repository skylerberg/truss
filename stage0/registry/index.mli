(** A registry as a directory of files: for each package, [owner/name/versions], a line for each
    version with its hash, the oldest first, and [owner/name/VERSION/], the files published as that
    version. A registry is only ever added to. *)

type t

val variable : string
(** [TRUSS_REGISTRY], which names the registry's directory. *)

val current : unit -> t option
(** The registry in use: the one {!configure} was last told, or else the one the environment names.
*)

val configure : string option -> unit
(** Tells the process which registry to use, in place of what its own environment names. The
    background process is told each client's. *)

val versions : t -> Path.package -> (Version.t * string) list
(** A package's versions, each with its hash, in the order they were published. A package the
    registry does not hold has none. *)

val newest : t -> Path.package -> (Version.t * string) option
val hash_of : t -> Path.package -> Version.t -> string option

val add : t -> Path.package -> Version.t -> (string * string) list -> unit
(** Adds a version of a package with these files, each a path and its bytes. *)

val fetch : t -> into:string -> Path.package -> Version.t -> hash:string -> (string, string) result
(** The directory, under [into], that holds a version's files, named by their hash, copying them
    from the registry if it is not there yet. The files are kept only if they have that hash. An
    error says why they could not be had, as the end of a sentence. *)
