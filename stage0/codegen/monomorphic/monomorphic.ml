let bug format = Compiler_bug.bug ~stage:"Monomorphic" format

exception Todo_type of Ground.ty

type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
}

let mode : Types.mode -> Ground.mode = function Read -> Read | Mut -> Mut | Own -> Own
let panic_capability = Well_known.path Panic

let capabilities context substitution (set : Types.capability_set) : Path.t list =
  List.sort_uniq Path.compare
    (List.map
       (function
         | Types.Capability path -> path
         | Capability_parameter parameter ->
             bug "the capability parameter %s of %s is not substituted" parameter.name
               (Path.show parameter.owner)
         | Capability_projection { name; _ } ->
             bug "the associated capability set %s is not normalized" name
         | Capability_variable _ -> bug "a set of capabilities the checker left unsolved")
       (context.normalize_capabilities (Types.substitute_capabilities substitution set)
         :> Types.capability list))

let evidence_for context substitution uses =
  List.filter
    (fun path -> not (Path.equal path panic_capability))
    (capabilities context substitution uses)

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
  | Capabilities set -> Capabilities (capabilities context [] set)

and ground_function context substitution (function_type : Types.function_type) :
    Ground.function_type =
  let function_type = Types.substitute_function substitution function_type in
  let ground_result : Types.result -> Ground.result = function
    | Returns ty -> Returns (ground context [] ty)
    | Lends (yield_mode, ty) -> Lends (mode yield_mode, ground context [] ty)
  in
  {
    parameters =
      List.map
        (fun (yield_mode, ty) -> (mode yield_mode, ground context [] ty))
        function_type.inputs;
    result = ground_result function_type.output;
    uses = evidence_for context [] function_type.uses;
  }

let types_mode : Ground.mode -> Types.mode = function Read -> Read | Mut -> Mut | Own -> Own

let rec back : Ground.ty -> Types.ty = function
  | Named { path; arguments } -> Named { path; arguments = List.map back_argument arguments }
  | Never -> Never
  | Function function_type ->
      Function
        {
          inputs =
            List.map
              (fun (yield_mode, ty) -> (types_mode yield_mode, back ty))
              function_type.parameters;
          output =
            (match function_type.result with
            | Returns ty -> Returns (back ty)
            | Lends (yield_mode, ty) -> Lends (types_mode yield_mode, back ty));
          uses =
            Types.capability_set (List.map (fun path -> Types.Capability path) function_type.uses);
          costs = [];
        }
  | Any { trait; arguments; associated } ->
      Any
        {
          trait;
          trait_arguments = List.map back_argument arguments;
          associated = List.map (fun (name, ty) -> (name, back ty)) associated;
        }

and back_argument : Ground.argument -> Types.argument = function
  | Type ty -> Type (back ty)
  | Value value -> Value (Known value)
  | Capabilities set ->
      Capabilities (Types.capability_set (List.map (fun path -> Types.Capability path) set))

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

let find_builtin_shape (ty : Ground.ty) : Memory_layout.shape option =
  match ty with
  | Never -> Some (Sum [])
  | Function function_type -> Some (Convention.function_value_shape function_type)
  | Any _ -> Some (Record [ ("value", Raw (Pointer Opaque)); ("vtable", Raw (Pointer Opaque)) ])
  | Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, arguments) with
      | None, _ -> None
      | Some Int8, [] -> Some (Scalar (Integer Int8))
      | Some Int16, [] -> Some (Scalar (Integer Int16))
      | Some Int32, [] -> Some (Scalar (Integer Int32))
      | Some Int64, [] -> Some (Scalar (Integer Int64))
      | Some UInt8, [] -> Some (Scalar (Integer UInt8))
      | Some UInt16, [] -> Some (Scalar (Integer UInt16))
      | Some UInt32, [] -> Some (Scalar (Integer UInt32))
      | Some UInt64, [] -> Some (Scalar (Integer UInt64))
      | Some Float32, [] -> Some (Scalar Float32)
      | Some Float64, [] -> Some (Scalar Float64)
      | Some Bool, [] -> Some (Scalar Bool)
      | Some Character, [] -> Some (Scalar Character)
      | Some Unit, [] -> Some (Record [])
      | Some Never, [] -> Some (Sum [])
      | Some Array, [ Type element; Value count ] -> Some (Array (element, Z.to_int count))
      | Some Storage, [ Type element ] -> Some (Storage.make_shape element)
      | Some View, [ Type element ] -> Some (Storage.make_view_shape element)
      | Some Handle, [] -> Some (Record [ ("descriptor", Raw (Integer Int32)) ])
      | Some Shared, [ Type _ ] -> Some (Record [ ("value", Raw (Pointer Opaque)) ])
      | Some Integer, _ -> bug "Integer exists only in specifications"
      | Some _, _ -> bug "a built-in type with the wrong arguments: %s" (Ground.to_string ty))

exception Defined_layout

let rec compute_fixed_layout ty =
  match find_builtin_shape ty with
  | None -> None
  | Some shape -> (
      let layout_of stored =
        match compute_fixed_layout stored with
        | Some layout -> layout
        | None -> raise Defined_layout
      in
      match Memory_layout.layout ~layout_of ty shape with
      | layout -> Some layout
      | exception Defined_layout -> None)

let read_defined_shape context (ty : Ground.ty) : Memory_layout.shape =
  match ty with
  | Named { path; arguments } -> (
      match context.type_interface path with
      | None -> bug "%s is not a type" (Path.show path)
      | Some interface -> (
          let substitution = substitution interface.type_generics arguments in
          match interface.shape with
          | Record record -> Record (fields context substitution record)
          | Sum variants ->
              Sum
                (List.map
                   (fun (value : Types.variant) ->
                     {
                       Memory_layout.name = value.variant_name;
                       indirect = value.indirect;
                       fields = fields context substitution (Option.value value.fields ~default:[]);
                     })
                   variants)
          | Builtin_type _ -> bug "a built-in type under a path that is not built in"
          | Types.Todo_type -> raise (Todo_type ty)))
  | Never | Function _ | Any _ -> bug "%s is built in" (Ground.to_string ty)

let shape context ty =
  match find_builtin_shape ty with Some shape -> shape | None -> read_defined_shape context ty
