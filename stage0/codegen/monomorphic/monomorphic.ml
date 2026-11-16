let bug format = Compiler_bug.bug ~stage:"Monomorphic" format

exception Todo_type of Ground.ty

type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
}

let ground_mode : Types.mode -> Ground.mode = function Read -> Read | Mut -> Mut | Own -> Own
let panic_capability = Well_known.path Panic

let list_capabilities context substitution (set : Types.capability_set) : Path.t list =
  List.sort_uniq Path.compare
    (List.map
       (function
         | Types.Capability path -> path
         | Capability_parameter parameter ->
             bug "the capability parameter %s of %s is not substituted" parameter.name
               (Path.show parameter.owner)
         | Capability_projection { name; _ } ->
             bug "the associated capability set %s is not normalized" name
         | Capability_variable _ -> bug "a set of capabilities the checker left unsolved"
         | Capability_error _ -> bug "a capability with an error reached code generation")
       (context.normalize_capabilities (Types.substitute_capabilities substitution set)
         :> Types.capability list))

let list_evidence context substitution uses =
  List.filter
    (fun path -> not (Path.equal path panic_capability))
    (list_capabilities context substitution uses)

let rec ground context substitution (ty : Types.ty) : Ground.ty =
  match context.normalize (Types.substitute substitution ty) with
  | Named { path; arguments } ->
      Named { path; arguments = List.map (ground_argument context []) arguments }
  | Function function_type -> Function (ground_function context [] function_type)
  | Any { trait; trait_arguments; associated } ->
      Any
        {
          trait;
          arguments = List.map (ground_argument context []) trait_arguments;
          associated = List.map (fun (name, ty) -> (name, ground context [] ty)) associated;
        }
  | Never -> Never
  | Parameter parameter ->
      bug "the generic parameter %s of %s is not substituted" parameter.name
        (Path.show parameter.owner)
  | Projection { name; _ } -> bug "the associated type %s is not normalized" name
  | Integer -> bug "Integer exists only in specifications"
  | (Variable _ | Literal _ | Hole) as ty ->
      bug "a type the checker left undecided: %s" (Types.show ty)
  | Error _ -> bug "a type with an error, which no build reaches"

and ground_argument context substitution (argument : Types.argument) : Ground.argument =
  match Types.substitute_argument substitution argument with
  | Type ty -> Type (ground context [] ty)
  | Value (Known value) -> Value value
  | Value (Value_parameter parameter) ->
      bug "the value parameter %s is not substituted" parameter.name
  | Value (Value_variable _) -> bug "a value the checker left undecided"
  | Capabilities set -> Capabilities (list_capabilities context [] set)

and ground_function context substitution (function_type : Types.function_type) :
    Ground.function_type =
  let function_type = Types.substitute_function substitution function_type in
  {
    parameters =
      List.map
        (fun (yield_mode, ty) -> (ground_mode yield_mode, ground context [] ty))
        function_type.inputs;
    result = ground context [] function_type.output;
    uses = list_evidence context [] function_type.uses;
  }

let uint64 = Ground.make_builtin UInt64
let mode_of_ground : Ground.mode -> Types.mode = function Read -> Read | Mut -> Mut | Own -> Own

let rec ty_of_ground : Ground.ty -> Types.ty = function
  | Named { path; arguments } -> Named { path; arguments = List.map argument_of_ground arguments }
  | Never -> Never
  | Function function_type ->
      Function
        {
          inputs =
            List.map
              (fun (yield_mode, ty) -> (mode_of_ground yield_mode, ty_of_ground ty))
              function_type.parameters;
          output = ty_of_ground function_type.result;
          uses =
            Types.make_capability_set
              (List.map (fun path -> Types.Capability path) function_type.uses);
          costs = [];
        }
  | Any { trait; arguments; associated } ->
      Any
        {
          trait;
          trait_arguments = List.map argument_of_ground arguments;
          associated = List.map (fun (name, ty) -> (name, ty_of_ground ty)) associated;
        }

and argument_of_ground : Ground.argument -> Types.argument = function
  | Type ty -> Type (ty_of_ground ty)
  | Value value -> Value (Known value)
  | Capabilities set ->
      Capabilities (Types.make_capability_set (List.map (fun path -> Types.Capability path) set))

let make_substitution (generics : Types.generic list) arguments =
  if List.length generics <> List.length arguments then
    bug "%d generic parameters for %d arguments" (List.length generics) (List.length arguments);
  List.map2
    (fun (generic : Types.generic) argument -> (generic.generic, argument_of_ground argument))
    generics arguments

let ground_fields context substitution (fields : Types.field list) =
  List.map
    (fun (field : Types.field) ->
      (field.field_name, Memory_layout.Typed (ground context substitution field.field_type)))
    fields

let compute_shape context (ty : Ground.ty) : Memory_layout.shape =
  match ty with
  | Never -> Sum []
  | Function function_type -> Convention.make_function_value_shape function_type
  | Any _ -> Record [ ("value", Raw (Pointer Opaque)); ("vtable", Raw (Pointer Opaque)) ]
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
      | Some Float32, [] -> Scalar Float32
      | Some Float64, [] -> Scalar Float64
      | Some Bool, [] -> Scalar Bool
      | Some Character, [] -> Scalar Character
      | Some Unit, [] -> Record []
      | Some Never, [] -> Sum []
      | Some Array, [ Type element; Value count ] -> Array (element, Z.to_int count)
      | Some Storage, [ Type element ] -> Storage.make_storage_shape ~uint64 element
      | Some View, [ Type element ] -> Storage.make_view_shape ~uint64 element
      | Some Handle, [] -> Record [ ("descriptor", Raw (Integer Int32)) ]
      | Some Shared, [ Type _ ] -> Record [ ("value", Raw (Pointer Opaque)) ]
      | Some Integer, _ -> bug "Integer exists only in specifications"
      | Some _, _ -> bug "a built-in type with the wrong arguments: %s" (Ground.to_string ty)
      | None, _ -> (
          match context.type_interface path with
          | None -> bug "%s is not a type" (Path.show path)
          | Some interface -> (
              let substitution = make_substitution interface.type_generics arguments in
              match interface.shape with
              | Record record -> Record (ground_fields context substitution record)
              | Sum variants ->
                  Sum
                    (List.map
                       (fun (value : Types.variant) ->
                         {
                           Memory_layout.name = value.variant_name;
                           indirect = value.indirect;
                           fields =
                             ground_fields context substitution
                               (Option.value value.fields ~default:[]);
                         })
                       variants)
              | Builtin_type _ -> bug "a built-in type under a path that is not built in"
              | Types.Todo_type -> raise (Todo_type ty))))
