type mode = Read | Mut | Own

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
  | Cursor of yielding
  | Never

and argument = Type of ty | Value of Z.t | Capabilities of Path.t list
and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
and result = Returns of ty | Yields of mode * ty | Lends of mode * ty
and yielding = { method_ : Path.t; type_arguments : argument list }

let ( >>= ) c next = if c <> 0 then c else next ()

let rec compare a b =
  match (a, b) with
  | Named a, Named b ->
      Path.compare a.path b.path >>= fun () -> compare_arguments a.arguments b.arguments
  | Function a, Function b -> compare_function a b
  | Any a, Any b ->
      Path.compare a.trait b.trait >>= fun () ->
      compare_arguments a.arguments b.arguments >>= fun () ->
      List.compare
        (fun (n, t) (m, u) -> String.compare n m >>= fun () -> compare t u)
        a.associated b.associated
  | Cursor a, Cursor b -> compare_yielding a b
  | Never, Never -> 0
  | _ -> Int.compare (rank a) (rank b)

and rank = function Named _ -> 0 | Function _ -> 1 | Any _ -> 2 | Cursor _ -> 3 | Never -> 4

(* [Z.t] is compared by [Z.compare], since the polymorphic comparison does
   not accept it. Every other part is a string, a list, or a constructor. *)
and compare_argument a b =
  match (a, b) with
  | Type a, Type b -> compare a b
  | Value a, Value b -> Z.compare a b
  | Capabilities a, Capabilities b -> List.compare Path.compare a b
  | _ ->
      let rank = function Type _ -> 0 | Value _ -> 1 | Capabilities _ -> 2 in
      Int.compare (rank a) (rank b)

and compare_arguments a b = List.compare compare_argument a b

and compare_function a b =
  List.compare
    (fun (m, t) (n, u) -> Stdlib.compare m n >>= fun () -> compare t u)
    a.parameters b.parameters
  >>= fun () ->
  compare_result a.result b.result >>= fun () -> List.compare Path.compare a.uses b.uses

and compare_result a b =
  match (a, b) with
  | Returns a, Returns b -> compare a b
  | Yields (m, a), Yields (n, b) | Lends (m, a), Lends (n, b) ->
      Stdlib.compare m n >>= fun () -> compare a b
  | _ ->
      let rank = function Returns _ -> 0 | Yields _ -> 1 | Lends _ -> 2 in
      Int.compare (rank a) (rank b)

and compare_yielding a b =
  Path.compare a.method_ b.method_ >>= fun () -> compare_arguments a.type_arguments b.type_arguments

let equal a b = compare a b = 0

let rec path_name : Path.t -> string = function
  | Top { name; _ } | Impl { name; _ } | Test { name; _ } | Law_proof { name; _ } -> name
  | Method { name; _ } | Member_constant { name; _ } -> name
  | Derived { trait; _ } -> path_name trait

let mode_prefix = function Read -> "" | Mut -> "mut " | Own -> "own "

let rec to_string = function
  | Named { path; arguments = [] } -> path_name path
  | Named { path; arguments } -> path_name path ^ arguments_to_string arguments
  | Function f ->
      let parameters = List.map (fun (mode, ty) -> mode_prefix mode ^ to_string ty) f.parameters in
      let result =
        match f.result with
        | Returns (Named { path; arguments = [] }) when path_name path = "Unit" -> ""
        | Returns ty -> " -> " ^ to_string ty
        | Yields (mode, ty) -> " yields " ^ mode_prefix mode ^ to_string ty
        | Lends (mode, ty) -> " lends " ^ mode_prefix mode ^ to_string ty
      in
      let text = "fn(" ^ String.concat ", " parameters ^ ")" ^ result in
      if f.uses = [] then text
      else "(" ^ text ^ " uses " ^ String.concat ", " (List.map path_name f.uses) ^ ")"
  | Any { trait; arguments; associated } ->
      let items =
        List.map argument_to_string arguments
        @ List.map (fun (name, ty) -> name ^ " = " ^ to_string ty) associated
      in
      "any " ^ path_name trait ^ if items = [] then "" else "[" ^ String.concat ", " items ^ "]"
  | Cursor y -> "cursor of " ^ path_name y.method_
  | Never -> "Never"

and argument_to_string = function
  | Type ty -> to_string ty
  | Value v -> Z.to_string v
  | Capabilities set -> "{" ^ String.concat ", " (List.map path_name set) ^ "}"

and arguments_to_string arguments =
  "[" ^ String.concat ", " (List.map argument_to_string arguments) ^ "]"

(* Encoding: each constructor is an array whose first item numbers it. *)

let tagged n items = Cbor.Array (Cbor.int n :: items)

let encode_module (m : Path.module_) =
  Cbor.Array (List.map (fun s -> Cbor.Text s) (m.package :: m.modules))

let encode_receiver : Path.receiver -> Cbor.t = function
  | Static -> Cbor.int 0
  | Read -> Cbor.int 1
  | Mut -> Cbor.int 2
  | Own -> Cbor.int 3

let rec encode_path : Path.t -> Cbor.t = function
  | Top { module_; name } -> tagged 0 [ encode_module module_; Text name ]
  | Method { owner; name; receiver } ->
      tagged 1 [ encode_path owner; Text name; encode_receiver receiver ]
  | Member_constant { owner; name } -> tagged 2 [ encode_path owner; Text name ]
  | Impl { module_; name } -> tagged 3 [ encode_module module_; Text name ]
  | Derived { type_; trait } -> tagged 4 [ encode_path type_; encode_path trait ]
  | Test { module_; name } -> tagged 5 [ encode_module module_; Text name ]
  | Law_proof { module_; name } -> tagged 6 [ encode_module module_; Text name ]

let encode_mode = function Read -> Cbor.int 0 | Mut -> Cbor.int 1 | Own -> Cbor.int 2

let rec encode ?(path = encode_path) ty =
  let encode = encode ~path and argument = encode_argument ~path in
  match ty with
  | Named { path = p; arguments } -> tagged 0 [ path p; Cbor.Array (List.map argument arguments) ]
  | Function f -> tagged 1 [ encode_function ~path f ]
  | Any { trait; arguments; associated } ->
      tagged 2
        [
          path trait;
          Cbor.Array (List.map argument arguments);
          Cbor.Array (List.map (fun (name, ty) -> Cbor.Array [ Text name; encode ty ]) associated);
        ]
  | Cursor yielding -> tagged 3 [ encode_yielding ~path yielding ]
  | Never -> tagged 4 []

and encode_argument ?(path = encode_path) = function
  | Type ty -> tagged 0 [ encode ~path ty ]
  | Value v -> tagged 1 [ Cbor.Integer v ]
  | Capabilities set -> tagged 2 [ Cbor.Array (List.map path set) ]

and encode_function ~path f =
  Cbor.Array
    [
      Cbor.Array
        (List.map (fun (mode, ty) -> Cbor.Array [ encode_mode mode; encode ~path ty ]) f.parameters);
      (match f.result with
      | Returns ty -> tagged 0 [ encode ~path ty ]
      | Yields (mode, ty) -> tagged 1 [ encode_mode mode; encode ~path ty ]
      | Lends (mode, ty) -> tagged 2 [ encode_mode mode; encode ~path ty ]);
      Cbor.Array (List.map path f.uses);
    ]

and encode_yielding ~path y =
  Cbor.Array [ path y.method_; Cbor.Array (List.map (encode_argument ~path) y.type_arguments) ]
