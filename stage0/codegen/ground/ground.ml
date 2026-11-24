type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Never

and argument = Type of ty | Value of Z.t
and function_type = { parameters : (Language.Mode.t * ty) list; result : ty; uses : Path.t list }

type instantiation = {
  type_arguments : argument list;
  capability_arguments : (string * Path.t list) list;
}

let no_instantiation = { type_arguments = []; capability_arguments = [] }
let compare = Stdlib.compare

let make_builtin ?(arguments = []) builtin =
  Named { path = Well_known.make_builtin_type_path builtin; arguments }

let rec to_string = function
  | Named { path; arguments = [] } -> Path.show_name path
  | Named { path; arguments } -> Path.show_name path ^ show_arguments arguments
  | Function function_type ->
      let parameters =
        List.map
          (fun (mode, ty) -> Language.Mode.show_prefix mode ^ to_string ty)
          function_type.parameters
      in
      let result =
        match function_type.result with
        | Named { path; arguments = [] } when Well_known.find_builtin_type path = Some Unit -> ""
        | ty -> " -> " ^ to_string ty
      in
      let text = "fn(" ^ String.concat ", " parameters ^ ")" ^ result in
      if function_type.uses = [] then text
      else
        "(" ^ text ^ " uses "
        ^ String.concat ", " (List.map Path.show_name function_type.uses)
        ^ ")"
  | Never -> "Never"

and show_argument = function Type ty -> to_string ty | Value value -> Z.to_string value
and show_arguments arguments = "[" ^ String.concat ", " (List.map show_argument arguments) ^ "]"
