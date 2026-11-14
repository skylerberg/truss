module Names = Resolve.Names

type target = Definition of Path.t | Module of Path.module_

type occurrence = {
  file : Path.file;
  span : Source.span;
  target : target;
  in_definition : Names.key;
  declares : bool;
}

val declared_name : Syntax.definition -> Syntax.name option
val all : Database.session -> Path.package list -> occurrence list
val uses : Database.session -> Path.package list -> Path.module_ -> (Path.file * Source.span) list
val names_definition : Path.t -> occurrence -> bool
