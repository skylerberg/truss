(* An instance's C as a builder writes it: its printing context, which holds
   what its code names, the header and body of each function, by its
   number among the nested functions, [None] for the instance's own, and
   its own function's size: each statement, and each block twice. *)
type t = {
  key : Instance.key;
  context : C_types.context;
  mutable functions : (int option * (string * string)) list;
  mutable weight : int;
}
