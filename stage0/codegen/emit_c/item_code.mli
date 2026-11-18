type t = {
  item : Lowered.Item.t;
  context : C_types.context;
  enclosing : string * string;
  nested : (int * (string * string)) list;
  weight : int;
}
