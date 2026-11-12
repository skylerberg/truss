module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

val visible_packages : Query.context -> Path.package -> Path.package list
val own_methods : Query.context -> Path.t -> string -> (Path.receiver * Path.t) list
val own_constant : Query.context -> Path.t -> string -> Path.t option
val trait_methods : Query.context -> Path.t -> string -> T.trait_method list
val trait_method : Query.context -> Path.t -> string -> Path.receiver -> T.trait_method option
val fields : Query.context -> Path.t -> T.argument list -> T.field list option
val variants : Query.context -> Path.t -> T.argument list -> T.variant list option
val shape : Query.context -> Path.t -> Types.shape option
val broken : Query.context -> Path.t -> Diagnostic.reported option
val fields_visible : Query.context -> package:Path.package -> Path.t -> bool
