type t = {
  key : Instance.key;
  context : C_types.context;
  own : string * string;
  nested : (int * (string * string)) list;
  weight : int;
}
