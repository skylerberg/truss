type t = {
  key : Instance.key;
  context : C_types.context;
  main : string * string;
  nested : (int * (string * string)) list;
  weight : int;
}
