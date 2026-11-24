type package = {
  name : Path.package;
  version : Version.t;
  hash : string;
  manifest : Manifest.package;
  record : Lock.t;
}

type problem = Project_catalog.selection_problem =
  | No_version of { name : Path.package; wanted_by : Path.package }
  | Cannot_load of {
      name : Path.package;
      version : Version.t;
      failure : Project_catalog.load_failure;
    }
  | Two_contents of { name : Path.package; version : Version.t; recorded_by : Path.package }

val read_manifest_and_record :
  read:(string -> string option) ->
  Path.package ->
  (Manifest.package * Lock.t, Project_catalog.load_failure) result

val choose :
  lock:Lock.t ->
  roots:(Path.package * Path.package) list ->
  is_local:(Path.package -> bool) ->
  load:
    (Path.package ->
    Version.t ->
    hash:string ->
    (Manifest.package * Lock.t, Project_catalog.load_failure) result) ->
  package list * problem list

val lock : project:Manifest.dependency list -> package list -> Lock.t
val list_differences : written:Lock.t -> current:Lock.t -> Project_catalog.difference list

module For_testing : sig
  val list_holds :
    project:Manifest.dependency list -> package list -> (Path.package * Grant.capability list) list
end
