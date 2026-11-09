(* The table from definitions to files and lines. See CODEGEN.md,
   "Positions".

   Generated code reports a position as its definition's anchor and a line
   and column within the definition, so a definition's C never changes when
   it moves in its file. The anchors are defined in one C file, generated at
   link time, which is the only C that moving a definition changes. *)

type anchor = {
  definition : Ground.definition;
  path : string;  (** The file, as the user sees it *)
  first_line : int;  (** The definition's first line, counting from 1 *)
}

(* The C file defining every anchor, in the order given. *)
val anchors_file : Memory_layout.target -> anchor list -> string
