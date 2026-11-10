(* Inference variables and unification, within one statement. *)

module T = Types

type t = {
  mutable next : int;
  types : (int, T.ty) Hashtbl.t;  (** What each solved type variable or literal is. *)
  values : (int, T.value) Hashtbl.t;  (** What each solved value variable is. *)
  mutable unknown_sets : int;  (** How many unknown sets of capabilities were made. *)
  mutable agreements : (T.capability list * T.capability list) list;
      (** Sets of capabilities that two types unified hold in the same place, of which one is not
          known yet: they must turn out the same. *)
}

let create () =
  {
    next = 0;
    types = Hashtbl.create 16;
    values = Hashtbl.create 4;
    unknown_sets = 0;
    agreements = [];
  }

let fresh unifier =
  unifier.next <- unifier.next + 1;
  T.Variable unifier.next

let fresh_literal unifier kind =
  unifier.next <- unifier.next + 1;
  T.Literal (kind, unifier.next)

let fresh_value unifier =
  unifier.next <- unifier.next + 1;
  T.Value_variable unifier.next

(* An unknown set of capabilities: what a capability parameter stands for
   where its function or type is used, which is the least set that what is
   passed for it uses. No statement works it out: it is known once the
   whole definition is checked. *)
let fresh_capabilities unifier =
  unifier.unknown_sets <- unifier.unknown_sets + 1;
  [ T.Capability_variable unifier.unknown_sets ]

(* Whether two sets of capabilities are one. Where either holds an unknown,
   that is noted, to be held once the unknowns are solved. *)
let same_capabilities unifier left right =
  let left = List.sort_uniq compare left and right = List.sort_uniq compare right in
  left = right
  || (T.unknown_capabilities left || T.unknown_capabilities right)
     && begin
       unifier.agreements <- (left, right) :: unifier.agreements;
       true
     end

(* The type a variable stands for, one step at a time, until it is not a
   solved variable. *)
let rec resolve unifier (type_ : T.ty) =
  match type_ with
  | Variable index | Literal (_, index) -> (
      match Hashtbl.find_opt unifier.types index with
      | Some bound -> resolve unifier bound
      | None -> type_)
  | _ -> type_

let rec resolve_value unifier (value : T.value) =
  match value with
  | Value_variable index -> (
      match Hashtbl.find_opt unifier.values index with
      | Some bound -> resolve_value unifier bound
      | None -> value)
  | _ -> value

(* Replaces every solved variable, at any depth. *)
let rec zonk unifier (type_ : T.ty) : T.ty =
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
  | T.Type type_ -> T.Type (zonk unifier type_)
  | T.Value value -> T.Value (resolve_value unifier value)
  | T.Capabilities _ as capabilities -> capabilities

and zonk_trait unifier (trait : T.trait_reference) =
  {
    trait with
    trait_arguments = List.map (zonk_argument unifier) trait.trait_arguments;
    associated = List.map (fun (name, type_) -> (name, zonk unifier type_)) trait.associated;
  }

and zonk_function unifier (function_type : T.function_type) =
  {
    function_type with
    inputs = List.map (fun (mode, type_) -> (mode, zonk unifier type_)) function_type.inputs;
    output =
      (match function_type.output with
      | Returns type_ -> Returns (zonk unifier type_)
      | Yields (mode, type_) -> Yields (mode, zonk unifier type_)
      | Lends (mode, type_) -> Lends (mode, zonk unifier type_));
  }

let rec occurs unifier index (type_ : T.ty) =
  match resolve unifier type_ with
  | Variable other | Literal (_, other) -> other = index
  | Named { arguments; _ } | Cursor { arguments; _ } ->
      List.exists
        (function
          | T.Type type_ -> occurs unifier index type_ | T.Value _ | T.Capabilities _ -> false)
        arguments
  | Function { inputs; output; _ } -> (
      List.exists (fun (_, type_) -> occurs unifier index type_) inputs
      ||
      match output with
      | Returns type_ | Yields (_, type_) | Lends (_, type_) -> occurs unifier index type_)
  | Projection { base; _ } -> occurs unifier index base
  | _ -> false

let literal_fits (kind : T.literal_kind) (type_ : T.ty) =
  match kind with
  | Integer_literal -> T.is_integer_type type_ || type_ = T.Integer
  | Float_literal -> T.is_float_type type_

let bind unifier index type_ =
  if occurs unifier index type_ then false
  else begin
    Hashtbl.replace unifier.types index type_;
    true
  end

type unknown =
  | Unknown_type of int
  | Unknown_literal of T.literal_kind * int
  | Unknown_value of int

(* Every unknown a type still holds, at any depth: type variables,
   undecided literals, and unknown [USize] values. The one walk that
   settling a statement uses, so every part of a type is seen alike. *)
let unknowns unifier (type_ : T.ty) =
  let found = ref [] in
  let rec go (type_ : T.ty) =
    match resolve unifier type_ with
    | Variable index -> found := Unknown_type index :: !found
    | Literal (kind, index) -> found := Unknown_literal (kind, index) :: !found
    | Named { arguments; _ } | Cursor { arguments; _ } -> List.iter argument arguments
    | Projection { base; trait = reference; _ } ->
        go base;
        trait reference
    | Function { inputs; output; _ } -> (
        List.iter (fun (_, type_) -> go type_) inputs;
        match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> go type_)
    | Any reference -> trait reference
    | Parameter _ | Never | Integer | Hole | Error _ -> ()
  and argument = function
    | T.Type type_ -> go type_
    | T.Value value -> (
        match resolve_value unifier value with
        | Value_variable index -> found := Unknown_value index :: !found
        | _ -> ())
    | T.Capabilities _ -> ()
  and trait (reference : T.trait_reference) =
    List.iter argument reference.trait_arguments;
    List.iter (fun (_, type_) -> go type_) reference.associated
  in
  go type_;
  List.sort_uniq compare !found

let argument_unknowns unifier = function
  | T.Type type_ -> unknowns unifier type_
  | T.Value value -> (
      match resolve_value unifier value with
      | Value_variable index -> [ Unknown_value index ]
      | _ -> [])
  | T.Capabilities _ -> []

(* Unifies two types, solving variables in either. Errors and holes agree
   with anything, so one mistake is reported once. Types are equal or they
   are not: function types with other [uses] or costs are other types, and
   only a value that meets an expected type converts, which is not done
   here. *)
let rec unify unifier (left : T.ty) (right : T.ty) =
  let left = resolve unifier left and right = resolve unifier right in
  match (left, right) with
  (* An error, or a hole, solves a variable it meets, so that one mistake is
     not reported again as a type that cannot be worked out. *)
  | (T.Variable index | T.Literal (_, index)), ((T.Error _ | T.Hole) as unknown)
  | ((T.Error _ | T.Hole) as unknown), (T.Variable index | T.Literal (_, index)) ->
      Hashtbl.replace unifier.types index unknown;
      true
  | ((T.Error _ | T.Hole) as unknown), other | other, ((T.Error _ | T.Hole) as unknown) ->
      (* Every variable inside what an error meets is solved as an error
         too, so nothing it held is reported as unknown. *)
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
      && same_capabilities unifier left.uses right.uses
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

and unify_result unifier (left : T.result) (right : T.result) =
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
         | T.Type left, T.Type right -> unify unifier left right
         | T.Value left, T.Value right -> unify_value unifier left right
         | T.Type (T.Error _), _ | _, T.Type (T.Error _) -> true
         | T.Capabilities left, T.Capabilities right -> same_capabilities unifier left right
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

and unify_trait unifier (left : T.trait_reference) (right : T.trait_reference) =
  Path.equal left.trait right.trait
  && unify_arguments unifier left.trait_arguments right.trait_arguments
  && List.length left.associated = List.length right.associated
  && List.for_all2
       (fun (left_name, left) (right_name, right) ->
         left_name = right_name && unify unifier left right)
       left.associated right.associated
