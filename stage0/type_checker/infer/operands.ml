let build (mode : Language.Mode.t) (node : Core.expression) : Core.operand =
  match (mode, node.kind) with
  | (Read | Mut), Use place -> Place place
  | Read, Literal _ -> Place (Temporary node)
  | _ -> Value node

let build_argument mode node : Core.argument = { mode; value = build mode node }

let build_default ~make (mode : Language.Mode.t) (default : Core.place) : Core.operand =
  let copy () = make (Core_walk.compute_place_type default) (Core.Copy (Place default)) in
  match mode with
  | Read -> Place default
  | Own -> Value (copy ())
  | Mut -> Place (Temporary (copy ()))

let make_field_default lookups ~origin ~(type_ : Path.t) ~type_arguments ~variant
    (field : Types.field) : Core.place =
  let interface = Interface.Definition.read_type_interface lookups type_ in
  Constant
    {
      path = Default { owner = type_; variant; name = field.field_name };
      substitution = Types.make_substitution interface.type_generics type_arguments;
      type_ = field.field_type;
      origin;
    }
