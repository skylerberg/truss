module Problem = Problem

val describe_manifest_problem : Problem.manifest -> string
val describe_lock_problem : Problem.lock -> string
val describe_selection_problem : Problem.selection -> string
val describe_difference : Problem.difference -> string
val describe : Problem.t -> string
