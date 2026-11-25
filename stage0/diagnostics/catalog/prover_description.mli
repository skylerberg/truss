val find_code : Prover.obligation -> Diagnostic.Code.prover
val describe : Prover.t -> Nodes.description
val find_cited : Prover.t -> Prover.quoted option
val describe_cited : Prover.t -> Prover.citation -> Nodes.description
