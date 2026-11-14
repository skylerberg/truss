type t = {
  key : Instance.key;
  context : C_types.context;
  mutable functions : (int option * (string * string)) list;
  mutable weight : int;
}
