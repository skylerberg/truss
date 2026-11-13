val common_directory : string -> string option
val prefix : string -> string option
val resolve : directory:string -> string -> string option
val head : directory:string -> string option
val default_branch : directory:string -> string option
val merge_base : directory:string -> string -> string -> string option
val files : directory:string -> string -> (string * string) list option
val merged_files : directory:string -> string -> string -> (string * string) list option
val snapshot : directory:string -> string option
