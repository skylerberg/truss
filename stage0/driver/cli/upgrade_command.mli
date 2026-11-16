val parse_wanted : string -> Path.package * Registry.Version.t option

type change =
  | Entered of Registry.Lock.entry
  | Left of Registry.Lock.entry
  | Moved of { name : Path.package; from : Registry.Version.t; to_ : Registry.Version.t }
  | Holds of { name : Path.package; gained : string list }

val lock_changes : before:Registry.Lock.t -> after:Registry.Lock.t -> change list

type signature

val report : lock:change list -> signatures:signature list -> broken:string list -> unit
val lock_file : Workspace.snapshot -> string
val run : names:string list -> int
