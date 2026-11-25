val encode : 'value -> string
val of_package : Path.package -> int
val of_module : Path.module_ -> int
val of_file : Path.file -> int
val of_key : Resolve.Names.key -> int
val of_path : Path.t -> int
val of_dependency : Path.package -> Path.package -> int
val of_law_proofs : package:string -> trait:int -> law:string -> type_:int -> int
val of_item : Lowered.Item.t -> int
