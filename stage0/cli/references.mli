module Names = Resolve.Names

type target = Definition of Path.t | Module of Path.module_

type occurrence = {
  module_ : Path.module_;
  span : Source.span;
  target : target;
  in_definition : Names.key;
  declares : bool;
}

val all : Project.t -> occurrence list
val uses : Project.t -> Path.module_ -> (Path.module_ * Source.span) list
val names_definition : Path.t -> occurrence -> bool
