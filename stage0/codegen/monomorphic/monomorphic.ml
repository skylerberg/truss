let raise_bug format = Compiler_bug.raise_bug ~stage:"Monomorphic" format

exception Todo_type of Ground.ty

type context = {
  find_type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
}

let list_capabilities context substitution (set : Types.capability_set) : Path.t list =
  List.sort_uniq Path.compare
    (List.filter_map
       (function
         | Types.Capability path when Well_known.is Run_forever path || Well_known.is System path ->
             None
         | Types.Capability path -> Some path
         | Capability_parameter parameter ->
             raise_bug "the capability parameter %s of %s is not substituted" parameter.name
               (Path.show parameter.owner)
         | Capability_projection { name; _ } ->
             raise_bug "the associated capability set %s is not normalized" name
         | Capability_variable _ -> raise_bug "a set of capabilities the checker left unsolved"
         | Capability_error _ -> raise_bug "a capability with an error reached code generation")
       (Types.list_capabilities
          (context.normalize_capabilities (Types.substitute_capabilities substitution set))))

let rec ground context substitution (ty : Types.ty) : Ground.ty =
  match context.normalize (Types.substitute substitution ty) with
  | Named { path; arguments } ->
      Named { path; arguments = List.map (ground_argument context Types.no_substitution) arguments }
  | Function function_type -> Function (ground_function context Types.no_substitution function_type)
  | Any { trait; trait_arguments; associated } ->
      Any
        {
          trait;
          arguments = List.map (ground_argument context Types.no_substitution) trait_arguments;
          associated =
            List.map (fun (name, ty) -> (name, ground context Types.no_substitution ty)) associated;
        }
  | Never -> Never
  | Parameter parameter ->
      raise_bug "the generic parameter %s of %s is not substituted" parameter.name
        (Path.show parameter.owner)
  | Projection { name; _ } -> raise_bug "the associated type %s is not normalized" name
  | Integer -> raise_bug "Integer exists only in specifications"
  | (Variable _ | Literal _ | Hole) as ty ->
      raise_bug "a type the checker left undecided: %s" (Types.show ty)
  | Error _ -> raise_bug "a type with an error, which no build reaches"

and ground_argument context substitution (argument : Types.argument) : Ground.argument =
  match Types.substitute_argument substitution argument with
  | Type ty -> Type (ground context Types.no_substitution ty)
  | Value (Known value) -> Value value
  | Value (Value_parameter parameter) ->
      raise_bug "the value parameter %s is not substituted" parameter.name
  | Value (Value_variable _) -> raise_bug "a value the checker left undecided"

and ground_function context substitution (function_type : Types.function_type) :
    Ground.function_type =
  let function_type = Types.substitute_function substitution function_type in
  {
    parameters =
      List.map
        (fun (yield_mode, ty) -> (yield_mode, ground context Types.no_substitution ty))
        function_type.inputs;
    result = ground context Types.no_substitution function_type.output;
    uses = list_capabilities context Types.no_substitution function_type.uses;
  }

let rec convert_ty : Ground.ty -> Types.ty = function
  | Named { path; arguments } -> Named { path; arguments = List.map convert_argument arguments }
  | Never -> Never
  | Function function_type ->
      Function
        {
          inputs =
            List.map (fun (yield_mode, ty) -> (yield_mode, convert_ty ty)) function_type.parameters;
          output = convert_ty function_type.result;
          uses =
            Types.make_capability_set
              (List.map (fun path -> Types.Capability path) function_type.uses);
          costs = [];
        }
  | Any { trait; arguments; associated } ->
      Any
        {
          trait;
          trait_arguments = List.map convert_argument arguments;
          associated = List.map (fun (name, ty) -> (name, convert_ty ty)) associated;
        }

and convert_argument : Ground.argument -> Types.argument = function
  | Type ty -> Type (convert_ty ty)
  | Value value -> Value (Known value)

let convert_capabilities set =
  Types.make_capability_set (List.map (fun path -> Types.Capability path) set)

let make_substitution (generics : Types.generic list) arguments =
  if List.length generics <> List.length arguments then
    raise_bug "%d generic parameters for %d arguments" (List.length generics)
      (List.length arguments);
  Types.make_substitution generics (List.map convert_argument arguments)

let convert_capability_arguments (instantiation : Ground.instantiation) =
  List.map (fun (name, set) -> (name, convert_capabilities set)) instantiation.capability_arguments

let make_signature_substitution (signature : Types.signature) (instantiation : Ground.instantiation)
    =
  Types.combine_substitutions
    (make_substitution signature.generics instantiation.type_arguments)
    (Types.make_capability_substitution signature.capability_parameters
       (convert_capability_arguments instantiation))

let ground_instantiation context substitution (instantiation : Types.instantiation) :
    Ground.instantiation =
  {
    type_arguments = List.map (ground_argument context substitution) instantiation.type_arguments;
    capability_arguments =
      List.sort compare
        (List.map
           (fun (name, set) -> (name, list_capabilities context substitution set))
           instantiation.capability_arguments);
  }

let ground_fields context substitution (fields : Types.field list) =
  List.map
    (fun (field : Types.field) ->
      (field.field_name, Memory_layout.Typed (ground context substitution field.field_type)))
    fields

let compute_named_builtin_shape ty (builtin : Language.Builtin_type.t)
    (arguments : Ground.argument list) : Memory_layout.shape =
  match (builtin, arguments) with
  | Int8, [] -> Scalar (Integer Int8)
  | Int16, [] -> Scalar (Integer Int16)
  | Int32, [] -> Scalar (Integer Int32)
  | Int64, [] -> Scalar (Integer Int64)
  | UInt8, [] -> Scalar (Integer UInt8)
  | UInt16, [] -> Scalar (Integer UInt16)
  | UInt32, [] -> Scalar (Integer UInt32)
  | UInt64, [] -> Scalar (Integer UInt64)
  | Float32, [] -> Scalar Float32
  | Float64, [] -> Scalar Float64
  | Bool, [] -> Scalar Bool
  | Character, [] -> Scalar Character
  | Unit, [] -> Record []
  | Never, [] -> Sum []
  | Array, [ Type element; Value count ] -> Array (element, Z.to_int count)
  | Storage, [ Type element ] -> Storage.make_storage_shape element
  | View, [ Type element ] -> Storage.make_view_shape element
  | Handle, [] -> Builtin_records.Handle.shape
  | Shared, [ Type _ ] -> Builtin_records.Shared.shape
  | Integer, _ -> raise_bug "Integer exists only in specifications"
  | _, _ -> raise_bug "a built-in type with the wrong arguments: %s" (Ground.to_string ty)

let find_builtin_shape (ty : Ground.ty) : Memory_layout.shape option =
  match ty with
  | Never -> Some (Sum [])
  | Function function_type -> Some (Builtin_records.Function_value.make_shape function_type)
  | Any _ -> Some Builtin_records.Any.shape
  | Named { path; arguments } ->
      Option.map
        (fun builtin -> compute_named_builtin_shape ty builtin arguments)
        (Well_known.find_builtin_type path)

let compute_defined_shape context ty path arguments : Memory_layout.shape =
  match context.find_type_interface path with
  | None -> raise_bug "%s is not a type" (Path.show path)
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
                     ground_fields context substitution (Option.value value.fields ~default:[]);
                 })
               variants)
      | Builtin_type _ -> raise_bug "a built-in type under a path that is not built in"
      | Types.Todo_type -> raise (Todo_type ty))

let compute_shape context (ty : Ground.ty) =
  match (find_builtin_shape ty, ty) with
  | Some shape, _ -> shape
  | None, Named { path; arguments } -> compute_defined_shape context ty path arguments
  | None, (Never | Function _ | Any _) ->
      raise_bug "the unnamed type %s has no built-in shape" (Ground.to_string ty)
