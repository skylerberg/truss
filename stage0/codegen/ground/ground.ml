type mode = Read | Mut | Own

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
  | Lent of lent
  | Never

and lent = { base : ty; writable : bool; fields : lent_field list }
and lent_field = { variant : string option; field : string; holds : holds }
and holds = Address | Nested of lent
and argument = Type of ty | Value of Z.t | Capabilities of Path.t list
and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
and result = Returns of ty | Lends of mode * ty

let ( >>= ) order next = if order <> 0 then order else next ()

let rec compare left right =
  match (left, right) with
  | Named left, Named right ->
      Path.compare left.path right.path >>= fun () ->
      compare_arguments left.arguments right.arguments
  | Function left, Function right -> compare_function left right
  | Any left, Any right ->
      Path.compare left.trait right.trait >>= fun () ->
      compare_arguments left.arguments right.arguments >>= fun () ->
      List.compare
        (fun (left_name, left_type) (right_name, right_type) ->
          String.compare left_name right_name >>= fun () -> compare left_type right_type)
        left.associated right.associated
  | Lent left, Lent right -> compare_lent left right
  | Never, Never -> 0
  | _ -> Int.compare (rank left) (rank right)

and rank = function Named _ -> 0 | Function _ -> 1 | Any _ -> 2 | Lent _ -> 3 | Never -> 4

and compare_lent left right =
  compare left.base right.base >>= fun () ->
  Bool.compare left.writable right.writable >>= fun () ->
  List.compare
    (fun left_field right_field ->
      Option.compare String.compare left_field.variant right_field.variant >>= fun () ->
      String.compare left_field.field right_field.field >>= fun () ->
      match (left_field.holds, right_field.holds) with
      | Address, Address -> 0
      | Nested left_field, Nested right_field -> compare_lent left_field right_field
      | Address, Nested _ -> -1
      | Nested _, Address -> 1)
    left.fields right.fields

(* [Z.t] is compared by [Z.compare], since the polymorphic comparison does
   not accept it. Every other part is a string, a list, or a constructor. *)
and compare_argument left right =
  match (left, right) with
  | Type left, Type right -> compare left right
  | Value left, Value right -> Z.compare left right
  | Capabilities left, Capabilities right -> List.compare Path.compare left right
  | _ ->
      let rank = function Type _ -> 0 | Value _ -> 1 | Capabilities _ -> 2 in
      Int.compare (rank left) (rank right)

and compare_arguments left right = List.compare compare_argument left right

and compare_function left right =
  List.compare
    (fun (right_name, left_type) (left_name, right_type) ->
      Stdlib.compare right_name left_name >>= fun () -> compare left_type right_type)
    left.parameters right.parameters
  >>= fun () ->
  compare_result left.result right.result >>= fun () ->
  List.compare Path.compare left.uses right.uses

and compare_result left right =
  match (left, right) with
  | Returns left, Returns right -> compare left right
  | Lends (right_name, left), Lends (left_name, right) ->
      Stdlib.compare right_name left_name >>= fun () -> compare left right
  | _ ->
      let rank = function Returns _ -> 0 | Lends _ -> 1 in
      Int.compare (rank left) (rank right)

let rec path_name : Path.t -> string = function
  | Top { name; _ } | Test { name; _ } -> name
  | Impl { trait; for_type; _ } -> trait ^ " for " ^ Path.show_type_head for_type
  | Law_proof { trait; law; for_type; _ } ->
      trait ^ "." ^ law ^ " for " ^ Path.show_type_head for_type
  | Method { name; _ } | Member_constant { name; _ } -> name
  | Derived { trait; _ } -> path_name trait

let mode_prefix = function Read -> "" | Mut -> "mut " | Own -> "own "

let rec to_string = function
  | Named { path; arguments = [] } -> path_name path
  | Named { path; arguments } -> path_name path ^ arguments_to_string arguments
  | Function function_type ->
      let parameters =
        List.map (fun (mode, ty) -> mode_prefix mode ^ to_string ty) function_type.parameters
      in
      let result =
        match function_type.result with
        | Returns (Named { path; arguments = [] }) when path_name path = "Unit" -> ""
        | Returns ty -> " -> " ^ to_string ty
        | Lends (mode, ty) -> " lends " ^ mode_prefix mode ^ to_string ty
      in
      let text = "fn(" ^ String.concat ", " parameters ^ ")" ^ result in
      if function_type.uses = [] then text
      else "(" ^ text ^ " uses " ^ String.concat ", " (List.map path_name function_type.uses) ^ ")"
  | Any { trait; arguments; associated } ->
      let items =
        List.map argument_to_string arguments
        @ List.map (fun (name, ty) -> name ^ " = " ^ to_string ty) associated
      in
      "any " ^ path_name trait ^ if items = [] then "" else "[" ^ String.concat ", " items ^ "]"
  | Lent lent -> lent_to_string lent
  | Never -> "Never"

and lent_to_string { base; writable; fields } =
  let field { variant; field; holds } =
    Option.fold ~none:"" ~some:(fun variant -> variant ^ ".") variant
    ^ field
    ^ match holds with Address -> " by address" | Nested lent -> ": " ^ lent_to_string lent
  in
  "lent "
  ^ (if writable then "mut " else "")
  ^ to_string base ^ "("
  ^ String.concat ", " (List.map field fields)
  ^ ")"

and argument_to_string = function
  | Type ty -> to_string ty
  | Value value -> Z.to_string value
  | Capabilities set -> "{" ^ String.concat ", " (List.map path_name set) ^ "}"

and arguments_to_string arguments =
  "[" ^ String.concat ", " (List.map argument_to_string arguments) ^ "]"
