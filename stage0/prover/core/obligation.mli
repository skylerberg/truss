type evaluation =
  | Template_check of { function_ : Path.t; literals : string list }
  | Constant_value of Path.t

type value = Boolean of bool | Integer of Z.t
type run = Evaluated of value option | Unfinished of string | Failed of string

type piece =
  | Text of string
  | Quote of Resolve.Names.key * Core.origin
  | Substituted of {
      key : Resolve.Names.key;
      clause : Core.origin;
      replacements : (Core.origin * string) list;
      type_names : (string * string) list;
    }

type message = piece list
type location = Node of Core.origin | Whole_definition
type edit = { at : Source.Definition_span.t; replacement : message }
type fix = { title : message; edits : edit list }

type t = {
  code : Diagnostic.Code.prover;
  location : location;
  message : message;
  cited : (Resolve.Names.key * Core.origin) option;
  fixes : fix list;
  query : Logic.query;
  values : (Logic.symbol * string) list;
  locals : (Logic.term * string) list;
  path_notes : (string * Logic.term) list;
  has_untriggered_written_fact : bool;
  is_rejection : bool;
}

type outcome = {
  obligations : t list;
  holes : (Resolve.Names.key * location) list;
  warnings : Source.Definition_span.t Diagnostic.diagnostic list;
  evaluation : evaluation option;
}
