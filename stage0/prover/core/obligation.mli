type evaluation = Logic.evaluation =
  | Constant_value of Path.t
  | Assertion of { definition : Path.t; condition : int }

type value =
  | Boolean of bool
  | Integer of Z.t
  | Float of float
  | Constructed of { variant : string option; fields : (string * value) list }
  | Elements of value list

type run =
  | Evaluated of value
  | Unfinished of Catalog.Codegen.stop
  | Failed of Catalog.Codegen.stop

type location = Catalog.Prover.location = Node of Core.origin | Whole_definition

type t = {
  obligation : Catalog.Prover.obligation;
  instance : Catalog.Prover.instance;
  location : location;
  cited : (Resolve.Names.key * Core.origin) option;
  fixes : Catalog.Prover.fix list;
  query : Logic.query;
  has_untriggered_written_fact : bool;
  refutation : Logic.term option;
}

type outcome = {
  obligations : t list;
  holes : (Resolve.Names.key * location) list;
  evaluation : evaluation option;
}
