type template_check = { from_template : Path.t; literals : string list; clauses : int list }
type template_clause = { check : template_check; clause : int }

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
  template_clause : template_clause option;
  decisions : (string * Logic.term) list;
}

type outcome = { obligations : t list; holes : (Resolve.Names.key * location) list }
