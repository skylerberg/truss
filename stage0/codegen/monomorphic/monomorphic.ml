let bug format = Compiler_bug.bug ~stage:"Monomorphic" format

type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  capabilities : Types.parameter -> Path.t list;
  cursor_fields : Ground.yielding -> (string * Memory_layout.member) list;
}

let mode : Types.mode -> Ground.mode = function Read -> Read | Mut -> Mut | Own -> Own
let builtin builtin = Ground.Named { path = Intrinsic.builtin_path builtin; arguments = [] }

let rec ground context substitution (ty : Types.ty) : Ground.ty =
  match context.normalize (Types.substitute substitution ty) with
  | Named { path; arguments } ->
      Named { path; arguments = List.map (ground_argument context []) arguments }
  | Function f -> Function (ground_function context [] f)
  | Any { trait; trait_arguments; associated } ->
      Any
        {
          trait;
          arguments = List.map (ground_argument context []) trait_arguments;
          associated = List.map (fun (name, ty) -> (name, ground context [] ty)) associated;
        }
  | Cursor { method_; arguments } ->
      Cursor { method_; type_arguments = List.map (ground_argument context []) arguments }
  | Never -> Never
  | Parameter p ->
      bug "the generic parameter %s of %s is not substituted" p.name (Path.show p.owner)
  | Projection { name; _ } -> bug "the associated type %s is not normalized" name
  | Integer -> bug "Integer exists only in specifications"
  | (Variable _ | Literal _ | Hole) as ty ->
      bug "a type the checker left undecided: %s" (Types.show ty)
  | Error _ -> bug "a type with an error, which no build reaches"

and ground_argument context substitution (argument : Types.argument) : Ground.argument =
  match Types.substitute_argument substitution argument with
  | Type ty -> Type (ground context [] ty)
  | Value (Known value) -> Value value
  | Value (Value_parameter p) -> bug "the value parameter %s is not substituted" p.name
  | Value (Value_variable _) -> bug "a value the checker left undecided"
  | Capabilities set ->
      Capabilities
        (List.sort_uniq Path.compare
           (List.concat_map
              (function
                | Types.Capability path -> [ path ]
                | Capability_parameter p -> context.capabilities p
                | Capability_variable _ -> bug "a set of capabilities the checker left unsolved")
              set))

and ground_function context substitution (f : Types.function_type) : Ground.function_type =
  let f = Types.substitute_function substitution f in
  let ground_result : Types.result -> Ground.result = function
    | Returns ty -> Returns (ground context [] ty)
    | Yields (m, ty) -> Yields (mode m, ground context [] ty)
    | Lends (m, ty) -> Lends (mode m, ground context [] ty)
  in
  {
    parameters = List.map (fun (m, ty) -> (mode m, ground context [] ty)) f.inputs;
    result = ground_result f.output;
    uses =
      List.sort_uniq Path.compare
        (List.concat_map
           (function
             | Types.Capability path -> [ path ]
             | Capability_parameter p -> context.capabilities p
             | Capability_variable _ -> bug "a set of capabilities the checker left unsolved")
           f.uses);
  }

let usize = builtin USize
let types_mode : Ground.mode -> Types.mode = function Read -> Read | Mut -> Mut | Own -> Own

(* A ground type, written back as the checker's, so that the checker's own
   substitution and its lookups apply to it. *)
let rec back : Ground.ty -> Types.ty = function
  | Named { path; arguments } -> Named { path; arguments = List.map back_argument arguments }
  | Never -> Never
  | Function f ->
      Function
        {
          inputs = List.map (fun (m, ty) -> (types_mode m, back ty)) f.parameters;
          output =
            (match f.result with
            | Returns ty -> Returns (back ty)
            | Yields (m, ty) -> Yields (types_mode m, back ty)
            | Lends (m, ty) -> Lends (types_mode m, back ty));
          uses = List.map (fun path -> Types.Capability path) f.uses;
          costs = [];
        }
  | Any { trait; arguments; associated } ->
      Any
        {
          trait;
          trait_arguments = List.map back_argument arguments;
          associated = List.map (fun (name, ty) -> (name, back ty)) associated;
        }
  | Cursor { method_; type_arguments } ->
      Cursor { method_; arguments = List.map back_argument type_arguments }

and back_argument : Ground.argument -> Types.argument = function
  | Type ty -> Type (back ty)
  | Value v -> Value (Known v)
  | Capabilities set -> Capabilities (List.map (fun path -> Types.Capability path) set)

(* The substitution of generic parameters by their arguments, which are
   ground. *)
let substitution (generics : Types.generic list) arguments =
  if List.length generics <> List.length arguments then
    bug "%d generic parameters for %d arguments" (List.length generics) (List.length arguments);
  List.map2
    (fun (generic : Types.generic) argument -> (generic.generic, back_argument argument))
    generics arguments

let fields context substitution (fields : Types.field list) =
  List.map
    (fun (field : Types.field) ->
      (field.field_name, Memory_layout.Typed (ground context substitution field.field_type)))
    fields

let shape context (ty : Ground.ty) : Memory_layout.shape =
  match ty with
  | Never -> Sum []
  | Function f -> Convention.function_value_shape f
  | Any _ -> Record [ ("value", Raw (Pointer Opaque)); ("vtable", Raw (Pointer Opaque)) ]
  | Cursor yielding -> Record (context.cursor_fields yielding)
  | Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, arguments) with
      | Some Int8, [] -> Scalar (Integer Int8)
      | Some Int16, [] -> Scalar (Integer Int16)
      | Some Int32, [] -> Scalar (Integer Int32)
      | Some Int64, [] -> Scalar (Integer Int64)
      | Some UInt8, [] -> Scalar (Integer UInt8)
      | Some UInt16, [] -> Scalar (Integer UInt16)
      | Some UInt32, [] -> Scalar (Integer UInt32)
      | Some UInt64, [] -> Scalar (Integer UInt64)
      | Some USize, [] -> Scalar (Integer USize)
      | Some ISize, [] -> Scalar (Integer ISize)
      | Some Float32, [] -> Scalar Float32
      | Some Float64, [] -> Scalar Float64
      | Some Bool, [] -> Scalar Bool
      | Some Character, [] -> Scalar Character
      | Some Unit, [] -> Record []
      | Some Never, [] -> Sum []
      | Some Array, [ Type element; Value count ] -> Array (element, Z.to_int count)
      | Some Storage, [ Type element ] -> Storage.shape ~usize element
      | Some View, [ Type element ] -> Storage.view_shape ~usize element
      | Some Handle, [] -> Record [ ("descriptor", Raw (Integer Int32)) ]
      | Some Shared, [ Type _ ] -> Record [ ("value", Raw (Pointer Opaque)) ]
      | Some Integer, _ -> bug "Integer exists only in specifications"
      | Some _, _ -> bug "a built-in type with the wrong arguments: %s" (Ground.to_string ty)
      | None, _ -> (
          match context.type_interface path with
          | None -> bug "%s is not a type" (Path.show path)
          | Some interface -> (
              let substitution = substitution interface.type_generics arguments in
              match interface.shape with
              | Record record -> Record (fields context substitution record)
              | Sum variants ->
                  Sum
                    (List.map
                       (fun (v : Types.variant) ->
                         {
                           Memory_layout.name = v.variant_name;
                           indirect = v.indirect;
                           fields = fields context substitution (Option.value v.fields ~default:[]);
                         })
                       variants)
              | Builtin_type _ -> bug "a built-in type under a path that is not built in"
              | Todo_type -> bug "%s is a todo, which no build reaches" (Path.show path)
              | Error_shape _ -> bug "%s did not parse, which no build reaches" (Path.show path))))

let kind context ty : Glue.kind =
  match (Storage.elements_of ty, ty) with
  | Some element, _ -> Storage element
  | None, Ground.Named { path; arguments = [] } when Intrinsic.builtin_of_path path = Some Handle ->
      Handle
  | None, Ground.Named { path; arguments = [ Type value ] }
    when Intrinsic.builtin_of_path path = Some Shared ->
      Shared value
  | None, _ -> Shape (shape context ty)

let debug_form : Ground.ty -> Glue.debug_form = function
  | Named
      {
        path =
          Top
            {
              module_ = { package = "standard"; modules = [ "text" ] };
              name = "String" | "StringSlice";
            };
        _;
      } ->
      Text
  | Named
      {
        path =
          Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" | "Slice" };
        _;
      } ->
      Sequence
  | _ -> Structure
