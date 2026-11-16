type package = {
  name : Path.package;
  version : Version.t;
  hash : string;
  manifest : Manifest.package;
  record : Lock.t;
}

type problem =
  | No_version of { name : Path.package; wanted_by : Path.package }
  | Cannot_load of { name : Path.package; version : Version.t; reason : string }
  | Two_contents of { name : Path.package; version : Version.t; recorded_by : Path.package }

val describe_problem : problem -> string

val read_manifest_and_record :
  read:(string -> string option) -> Path.package -> (Manifest.package * Lock.t, string) result

val choose :
  lock:Lock.t ->
  roots:(Path.package * Path.package) list ->
  local:(Path.package -> bool) ->
  load:(Path.package -> Version.t -> hash:string -> (Manifest.package * Lock.t, string) result) ->
  package list * problem list

val lock : project:Manifest.dependency list -> package list -> Lock.t
val list_differences : written:Lock.t -> current:Lock.t -> string list

module For_testing : sig
  val holds : project:Manifest.dependency list -> package list -> (Path.package * string list) list
end
