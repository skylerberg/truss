type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }

let site_of (node : Core.expression) = { id = node.id; origin = node.origin; type_ = node.type_ }

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : Core.evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Indirect

type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }

let of_core_callee : Core.callee -> callee = function
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Indirect _ -> Indirect

let of_core (call : Core.call) =
  { callee = of_core_callee call.callee; lends = call.lends; uses = call.uses }

let of_mir_callee : Mir.callee -> callee = function
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Indirect _ -> Indirect

let of_mir (call : Mir.call) ~lends =
  { callee = of_mir_callee call.callee; lends; uses = call.uses }

let core_callee : callee -> Core.callee option = function
  | Function { path; type_arguments } -> Some (Function { path; type_arguments })
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Some (Trait_method { trait; name; receiver; self_type; type_arguments; evidence })
  | Capability_method { capability; name } -> Some (Capability_method { capability; name })
  | Intrinsic { operation; type_arguments } -> Some (Intrinsic { operation; type_arguments })
  | Indirect -> None

type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Other
