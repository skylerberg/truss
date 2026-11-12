(** Choosing the versions of a build: for each registry package, the highest version that the
    project's lock file or the record of any package of the build names. *)

type package = {
  name : Path.package;
  version : Version.t;
  hash : string;
  manifest : Manifest.package;
  record : Lock.t;  (** What the package was published with *)
}
(** A registry package of a build. *)

type problem =
  | No_version of { name : Path.package; wanted_by : Path.package }
      (** A dependency that no lock file or record gives a version *)
  | Cannot_load of { name : Path.package; version : Version.t; reason : string }
  | Two_contents of { name : Path.package; version : Version.t; recorded_by : Path.package }
      (** A record that names one version with another hash than the build's *)

val sentence : problem -> string

val choose :
  lock:Lock.t ->
  roots:(Path.package * Path.package) list ->
  local:(Path.package -> bool) ->
  load:(Path.package -> Version.t -> hash:string -> (Manifest.package * Lock.t, string) result) ->
  package list * problem list
(** The registry packages of a build, in order of name. [roots] are the dependencies of the
    project's packages, each with the package that names it, [local] says whether a name is a
    package of the project, which is then used whatever the registry has by that name, and [load]
    gives a published package's manifest and record. A build takes on the dependencies of a
    published package that its record names, and not one that only its tests use, which the record
    leaves out. *)

val holds : project:Manifest.dependency list -> package list -> (Path.package * string list) list
(** The capabilities each package of a build holds: those its users in the build grant it, of the
    ones each user holds itself. A project's own packages, whose entries [project] is, hold
    everything. *)

val lock : project:Manifest.dependency list -> package list -> Lock.t
(** The lock file of a build: a line for each of its registry packages. *)

val differences : written:Lock.t -> current:Lock.t -> string list
(** Where a lock file as it is written differs from the one a build gives, each as a sentence. *)
