(* Inference variables and unification, within one statement. *)
type t = {
  mutable next : int;
  types : (int, Types.ty) Hashtbl.t;  (** The solution of each solved type variable or literal. *)
  values : (int, Types.value) Hashtbl.t;  (** The solution of each solved value variable. *)
  mutable capability_variable_count : int;  (** The number of capability variables created. *)
  mutable deferred_capability_equalities : (Types.capability list * Types.capability list) list;
      (** Pairs of capability sets that unification found in the same position of two types, where
          at least one has a capability variable. They must be equal once the variables are solved.
      *)
}

let create () =
  {
    next = 0;
    types = Hashtbl.create 16;
    values = Hashtbl.create 4;
    capability_variable_count = 0;
    deferred_capability_equalities = [];
  }

let fresh unifier =
  unifier.next <- unifier.next + 1;
  Types.Variable unifier.next

let fresh_literal unifier kind =
  unifier.next <- unifier.next + 1;
  Types.Literal (kind, unifier.next)

let fresh_value unifier =
  unifier.next <- unifier.next + 1;
  Types.Value_variable unifier.next

(* A fresh capability variable, as a one-element capability set. It is the
   instantiation of a capability parameter at one use of a generic function
   or type. It is solved after the whole definition is checked, not per
   statement: its solution is the smallest set that satisfies every subset
   constraint on it. *)
let fresh_capability_variable unifier =
  unifier.capability_variable_count <- unifier.capability_variable_count + 1;
  [ Types.Capability_variable unifier.capability_variable_count ]

(* Unifies two capability sets. Two sets that are both known unify only if
   they are equal. If either set has a capability variable, or an associated
   capability set of a type that is not inferred yet, the equality is
   deferred until the definition is checked, and unification succeeds for
   now. *)
let unify_capabilities unifier left right =
  let left = List.sort_uniq compare left and right = List.sort_uniq compare right in
  left = right
  || (Types.capabilities_unsolved left || Types.capabilities_unsolved right)
     && begin
       unifier.deferred_capability_equalities <-
         (left, right) :: unifier.deferred_capability_equalities;
       true
     end

(* Follows the solutions of inference variables until the type is not a
   solved variable. Only the top of the type is resolved. *)
let rec resolve unifier (type_ : Types.ty) =
  match type_ with
  | Variable index | Literal (_, index) -> (
      match Hashtbl.find_opt unifier.types index with
      | Some bound -> resolve unifier bound
      | None -> type_)
  | _ -> type_

let rec resolve_value unifier (value : Types.value) =
  match value with
  | Value_variable index -> (
      match Hashtbl.find_opt unifier.values index with
      | Some bound -> resolve_value unifier bound
      | None -> value)
  | _ -> value

(* Replaces every solved inference variable in a type, at any depth. *)
let rec zonk unifier (type_ : Types.ty) : Types.ty =
  let zonk = zonk unifier in
  match resolve unifier type_ with
  | Named { path; arguments } ->
      Named { path; arguments = List.map (zonk_argument unifier) arguments }
  | Projection { base; trait; name } ->
      Projection { base = zonk base; trait = zonk_trait unifier trait; name }
  | Function function_type -> Function (zonk_function unifier function_type)
  | Any trait -> Any (zonk_trait unifier trait)
  | Cursor { method_; arguments } ->
      Cursor { method_; arguments = List.map (zonk_argument unifier) arguments }
  | type_ -> type_

and zonk_argument unifier = function
  | Types.Type type_ -> Types.Type (zonk unifier type_)
  | Types.Value value -> Types.Value (resolve_value unifier value)
  | Types.Capabilities capabilities -> Types.Capabilities (zonk_capabilities unifier capabilities)

and zonk_capabilities unifier capabilities =
  List.map
    (function
      | Types.Capability_projection { base; trait; name } ->
          Types.Capability_projection
            { base = zonk unifier base; trait = zonk_trait unifier trait; name }
      | capability -> capability)
    capabilities

and zonk_trait unifier (trait : Types.trait_reference) =
  {
    trait with
    trait_arguments = List.map (zonk_argument unifier) trait.trait_arguments;
    associated = List.map (fun (name, type_) -> (name, zonk unifier type_)) trait.associated;
  }

and zonk_function unifier (function_type : Types.function_type) =
  {
    function_type with
    inputs = List.map (fun (mode, type_) -> (mode, zonk unifier type_)) function_type.inputs;
    output =
      (match function_type.output with
      | Returns type_ -> Returns (zonk unifier type_)
      | Yields (mode, type_) -> Yields (mode, zonk unifier type_)
      | Lends (mode, type_) -> Lends (mode, zonk unifier type_));
    uses = zonk_capabilities unifier function_type.uses;
  }

let occurs unifier index =
  Types.exists ~resolve:(resolve unifier) (function
    | Variable other | Literal (_, other) -> other = index
    | _ -> false)

let literal_fits (kind : Types.literal_kind) (type_ : Types.ty) =
  match kind with
  | Integer_literal -> Types.is_integer_type type_ || type_ = Types.Integer
  | Float_literal -> Types.is_float_type type_

let bind unifier index type_ =
  if occurs unifier index type_ then false
  else begin
    Hashtbl.replace unifier.types index type_;
    true
  end

type unknown =
  | Unknown_type of int
  | Unknown_literal of Types.literal_kind * int
  | Unknown_value of int

(* Every unsolved variable in a type, at any depth: type variables, literal
   variables, and [USize] value variables. The end of a statement's
   inference uses only this function to find them. *)
let unknowns unifier (type_ : Types.ty) =
  let unknowns = ref [] in
  let rec collect (type_ : Types.ty) =
    match resolve unifier type_ with
    | Variable index -> unknowns := Unknown_type index :: !unknowns
    | Literal (kind, index) -> unknowns := Unknown_literal (kind, index) :: !unknowns
    | Named { arguments; _ } | Cursor { arguments; _ } -> List.iter argument arguments
    | Projection { base; trait = reference; _ } ->
        collect base;
        trait reference
    | Function { inputs; output; _ } ->
        List.iter (fun (_, type_) -> collect type_) inputs;
        collect (Types.result_type output)
    | Any reference -> trait reference
    | Parameter _ | Never | Integer | Hole | Error _ -> ()
  and argument = function
    | Types.Type type_ -> collect type_
    | Types.Value value -> (
        match resolve_value unifier value with
        | Value_variable index -> unknowns := Unknown_value index :: !unknowns
        | _ -> ())
    | Types.Capabilities _ -> ()
  and trait (reference : Types.trait_reference) =
    List.iter argument reference.trait_arguments;
    List.iter (fun (_, type_) -> collect type_) reference.associated
  in
  collect type_;
  List.sort_uniq compare !unknowns

let argument_unknowns unifier = function
  | Types.Type type_ -> unknowns unifier type_
  | Types.Value value -> (
      match resolve_value unifier value with
      | Value_variable index -> [ Unknown_value index ]
      | _ -> [])
  | Types.Capabilities _ -> []

(* Unifies two types, solving inference variables in either. An error or a
   hole unifies with any type, so one mistake is reported once. Unification
   is equality: function types with different [uses] or costs do not unify.
   Implicit conversions are applied where a value is checked against an
   expected type, not here. *)
let rec unify unifier (left : Types.ty) (right : Types.ty) =
  let left = resolve unifier left and right = resolve unifier right in
  match (left, right) with
  (* A variable that is unified with an error or a hole is solved as that
     error or hole, so the mistake is not reported again as a type that
     cannot be inferred. *)
  | (Types.Variable index | Types.Literal (_, index)), ((Types.Error _ | Types.Hole) as unknown)
  | ((Types.Error _ | Types.Hole) as unknown), (Types.Variable index | Types.Literal (_, index)) ->
      Hashtbl.replace unifier.types index unknown;
      true
  | ((Types.Error _ | Types.Hole) as unknown), other
  | other, ((Types.Error _ | Types.Hole) as unknown) ->
      (* Every variable inside a type that is unified with an error is
         solved as that error too, so none of them is reported as unsolved. *)
      List.iter
        (function
          | Unknown_type index | Unknown_literal (_, index) ->
              Hashtbl.replace unifier.types index unknown
          | Unknown_value _ -> ())
        (unknowns unifier other);
      true
  | Variable left_index, Variable right_index when left_index = right_index -> true
  | Variable index, other | other, Variable index -> bind unifier index other
  | Literal (left_kind, left_index), Literal (right_kind, right_index) ->
      left_kind = right_kind && (left_index = right_index || bind unifier left_index right)
  | Literal (kind, index), other | other, Literal (kind, index) ->
      literal_fits kind other && bind unifier index other
  | Named left, Named right ->
      Path.equal left.path right.path && unify_arguments unifier left.arguments right.arguments
  | Parameter left, Parameter right -> left = right
  | Function left, Function right ->
      List.sort_uniq compare left.costs = List.sort_uniq compare right.costs
      && List.length left.inputs = List.length right.inputs
      && List.for_all2
           (fun (left_mode, left) (right_mode, right) ->
             left_mode = right_mode && unify unifier left right)
           left.inputs right.inputs
      && unify_result unifier left.output right.output
      && unify_capabilities unifier left.uses right.uses
  | Any left, Any right -> unify_trait unifier left right
  | Projection left, Projection right ->
      left.name = right.name
      && Path.equal left.trait.trait right.trait.trait
      && unify_arguments unifier left.trait.trait_arguments right.trait.trait_arguments
      && unify unifier left.base right.base
  | Cursor left, Cursor right ->
      Path.equal left.method_ right.method_
      && unify_arguments unifier left.arguments right.arguments
  | Never, Never | Integer, Integer -> true
  | _ -> false

and unify_result unifier (left : Types.result) (right : Types.result) =
  match (left, right) with
  | Returns left, Returns right -> unify unifier left right
  | Yields (left_mode, left), Yields (right_mode, right)
  | Lends (left_mode, left), Lends (right_mode, right) ->
      left_mode = right_mode && unify unifier left right
  | _ -> false

and unify_arguments unifier left right =
  List.length left = List.length right
  && List.for_all2
       (fun left right ->
         match (left, right) with
         | Types.Type left, Types.Type right -> unify unifier left right
         | Types.Value left, Types.Value right -> unify_value unifier left right
         | Types.Type (Types.Error _), _ | _, Types.Type (Types.Error _) -> true
         | Types.Capabilities left, Types.Capabilities right ->
             unify_capabilities unifier left right
         | _ -> false)
       left right

and unify_value unifier left right =
  let left = resolve_value unifier left and right = resolve_value unifier right in
  match (left, right) with
  | Value_variable index, other | other, Value_variable index ->
      (match other with
      | Value_variable other_index when other_index = index -> ()
      | _ -> Hashtbl.replace unifier.values index other);
      true
  | left, right -> left = right

and unify_trait unifier (left : Types.trait_reference) (right : Types.trait_reference) =
  Path.equal left.trait right.trait
  && unify_arguments unifier left.trait_arguments right.trait_arguments
  && List.length left.associated = List.length right.associated
  && List.for_all2
       (fun (left_name, left) (right_name, right) ->
         left_name = right_name && unify unifier left right)
       left.associated right.associated
