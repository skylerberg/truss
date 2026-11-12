module Names = Resolve.Names
module Version = Registry.Version
module Lock = Registry.Lock

type outcome =
  | Published of {
      version : Version.t;
      files : (string * string) list;
      grows : (Path.t * string) list;
    }
  | Unchanged of Version.t
  | Refused of string list

val run : directory:string -> json:bool -> int
