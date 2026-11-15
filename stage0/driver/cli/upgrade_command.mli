module Lock = Registry.Lock
module Version = Registry.Version

val wanted : string -> Path.package * Version.t option

type change =
  | Entered of Lock.entry
  | Left of Lock.entry
  | Moved of { name : Path.package; from : Version.t; to_ : Version.t }
  | Holds of { name : Path.package; gained : string list }

val lock_changes : before:Lock.t -> after:Lock.t -> change list

type signature

val report : lock:change list -> signatures:signature list -> broken:string list -> unit
val lock_file : Database.snapshot -> string
val run : names:string list -> int
