type mode = Read | Mut | Own

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
  | Never

and argument = Type of ty | Value of Z.t | Capabilities of Path.t list
and function_type = { parameters : (mode * ty) list; result : ty; uses : Path.t list }

let compare = Stdlib.compare
let builtin builtin = Named { path = Intrinsic.builtin_path builtin; arguments = [] }

let rec path_name : Path.t -> string = function
  | Top { name; _ } | Test { name; _ } -> name
  | Impl { trait; for_type; _ } -> path_name trait.path ^ " for " ^ path_name for_type
  | Law_proof { trait; law; for_type; _ } ->
      path_name trait.path ^ "." ^ law ^ " for " ^ path_name for_type
  | Unresolved { names; _ } -> String.concat "::" names
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
        | Named { path; arguments = [] } when path_name path = "Unit" -> ""
        | ty -> " -> " ^ to_string ty
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
  | Never -> "Never"

and argument_to_string = function
  | Type ty -> to_string ty
  | Value value -> Z.to_string value
  | Capabilities set -> "{" ^ String.concat ", " (List.map path_name set) ^ "}"

and arguments_to_string arguments =
  "[" ^ String.concat ", " (List.map argument_to_string arguments) ^ "]"
