type evaluation = Logic.evaluation =
  | Constant_value of Path.t
  | Assertion of { definition : Path.t; condition : int }

type value =
  | Boolean of bool
  | Integer of Z.t
  | Float of float
  | Constructed of { variant : string option; fields : (string * value) list }
  | Elements of value list

type run = Evaluated of value | Unfinished of string | Failed of string
type location = Catalog.Prover.location = Node of Core.origin | Whole_definition

type t = {
  obligation : Catalog.Prover.obligation;
  instance : Catalog.Prover.instance;
  location : location;
  cited : (Resolve.Names.key * Core.origin) option;
  fixes : Catalog.Prover.fix list;
  query : Logic.query;
  values : (Logic.symbol * string) list;
  locals : (Logic.term * string) list;
  path_notes : (Catalog.Prover.path_note * Logic.term) list;
  has_untriggered_written_fact : bool;
  is_rejection : bool;
}

type outcome = {
  obligations : t list;
  holes : (Resolve.Names.key * location) list;
  evaluated_constants : Path.t list;
}
