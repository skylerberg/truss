type argument = Context.argument = Place of Lowered.place | Value of Lowered.operand
type types = Context.types = { uint64 : Ground.ty; string : Ground.ty }

let list_consumed_places : Intrinsic.operation -> int list = function
  | Buffer Array_from_storage -> [ 0 ]
  | _ -> []

let lower ?(value_arguments = []) ?reported env builder types operation ~type_arguments arguments
    ~destination ~site ~trace =
  let context : Context.t =
    {
      env;
      builder;
      types;
      operation;
      type_arguments;
      value_arguments;
      arguments;
      destination;
      site;
      reported;
      trace;
    }
  in
  match (operation : Intrinsic.operation) with
  | Lend lend -> Some (Buffers.lower_lend context lend)
  | Scalar scalar ->
      Scalar.lower context scalar;
      None
  | Buffer buffer ->
      Buffers.lower context buffer;
      None
  | Runtime runtime ->
      Runtime.lower context runtime;
      None
