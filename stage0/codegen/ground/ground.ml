type definition = { package : string; modules : string list; name : string }
type mode = Read | Mut | Own

type ty =
  | Named of { definition : definition; arguments : argument list }
  | Function of function_type
  | Any of { trait : definition; arguments : argument list; associated : (string * ty) list }
  | Cursor of yielding
  | Never

and argument = Type of ty | Value of Z.t
and function_type = { parameters : (mode * ty) list; result : result; uses : definition list }
and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

and yielding = {
  method_ : definition;
  receiver : mode;
  type_arguments : argument list;
  capabilities : definition list list;
}

(* Every field is a string, a list, a [Z.t], or a constructor of these, so
   the polymorphic comparison is a total order that does not depend on how
   values are stored. [Z.t] is compared by [Z.compare] because the
   polymorphic comparison does not accept it. *)
let compare_definition (a : definition) (b : definition) = Stdlib.compare a b

let rec compare a b =
  match (a, b) with
  | Named a, Named b ->
      let c = compare_definition a.definition b.definition in
      if c <> 0 then c else compare_arguments a.arguments b.arguments
  | Function a, Function b -> compare_function a b
  | Any a, Any b ->
      let c = compare_definition a.trait b.trait in
      if c <> 0 then c
      else
        let c = compare_arguments a.arguments b.arguments in
        if c <> 0 then c
        else
          List.compare
            (fun (n, t) (m, u) ->
              let c = String.compare n m in
              if c <> 0 then c else compare t u)
            a.associated b.associated
  | Cursor a, Cursor b -> compare_yielding a b
  | Never, Never -> 0
  | _ -> Int.compare (rank a) (rank b)

and rank = function Named _ -> 0 | Function _ -> 1 | Any _ -> 2 | Cursor _ -> 3 | Never -> 4

and compare_argument a b =
  match (a, b) with
  | Type a, Type b -> compare a b
  | Value a, Value b -> Z.compare a b
  | Type _, Value _ -> -1
  | Value _, Type _ -> 1

and compare_arguments a b = List.compare compare_argument a b

and compare_function a b =
  let c =
    List.compare
      (fun (m, t) (n, u) ->
        let c = Stdlib.compare m n in
        if c <> 0 then c else compare t u)
      a.parameters b.parameters
  in
  if c <> 0 then c
  else
    let c = compare_result a.result b.result in
    if c <> 0 then c else List.compare compare_definition a.uses b.uses

and compare_result a b =
  match (a, b) with
  | Returns a, Returns b -> compare a b
  | Yields (m, a), Yields (n, b) | Lends (m, a), Lends (n, b) ->
      let c = Stdlib.compare m n in
      if c <> 0 then c else compare a b
  | _ ->
      let rank = function Returns _ -> 0 | Yields _ -> 1 | Lends _ -> 2 in
      Int.compare (rank a) (rank b)

and compare_yielding a b =
  let c = compare_definition a.method_ b.method_ in
  if c <> 0 then c
  else
    let c = Stdlib.compare a.receiver b.receiver in
    if c <> 0 then c
    else
      let c = compare_arguments a.type_arguments b.type_arguments in
      if c <> 0 then c
      else List.compare (List.compare compare_definition) a.capabilities b.capabilities

let equal a b = compare a b = 0
let definition_to_string d = String.concat "::" ((d.package :: d.modules) @ [ d.name ])
let mode_prefix = function Read -> "" | Mut -> "mut " | Own -> "own "

let rec to_string = function
  | Named { definition; arguments = [] } -> definition.name
  | Named { definition; arguments } -> definition.name ^ arguments_to_string arguments
  | Function f ->
      let parameters = List.map (fun (mode, ty) -> mode_prefix mode ^ to_string ty) f.parameters in
      let result =
        match f.result with
        | Returns (Named { definition = { name = "Unit"; _ }; arguments = [] }) -> ""
        | Returns ty -> " -> " ^ to_string ty
        | Yields (mode, ty) -> " yields " ^ mode_prefix mode ^ to_string ty
        | Lends (mode, ty) -> " lends " ^ mode_prefix mode ^ to_string ty
      in
      let text = "fn(" ^ String.concat ", " parameters ^ ")" ^ result in
      if f.uses = [] then text
      else
        "(" ^ text ^ " uses "
        ^ String.concat ", " (List.map (fun (d : definition) -> d.name) f.uses)
        ^ ")"
  | Any { trait; arguments; associated } ->
      let items =
        List.map argument_to_string arguments
        @ List.map (fun (name, ty) -> name ^ " = " ^ to_string ty) associated
      in
      "any " ^ trait.name ^ if items = [] then "" else "[" ^ String.concat ", " items ^ "]"
  | Cursor y -> "cursor of " ^ y.method_.name
  | Never -> "Never"

and argument_to_string = function Type ty -> to_string ty | Value v -> Z.to_string v

and arguments_to_string arguments =
  "[" ^ String.concat ", " (List.map argument_to_string arguments) ^ "]"

(* Each constructor is an array whose first item numbers it. *)
let tagged n items = Cbor.Array (Cbor.int n :: items)

let encode_definition d =
  Cbor.Array (List.map (fun s -> Cbor.Text s) ((d.package :: d.modules) @ [ d.name ]))

let encode_mode = function Read -> Cbor.int 0 | Mut -> Cbor.int 1 | Own -> Cbor.int 2

let rec encode = function
  | Named { definition; arguments } ->
      tagged 0 [ encode_definition definition; Cbor.Array (List.map encode_argument arguments) ]
  | Function f -> tagged 1 [ encode_function f ]
  | Any { trait; arguments; associated } ->
      tagged 2
        [
          encode_definition trait;
          Cbor.Array (List.map encode_argument arguments);
          Cbor.Array (List.map (fun (name, ty) -> Cbor.Array [ Text name; encode ty ]) associated);
        ]
  | Cursor yielding -> tagged 3 [ encode_yielding yielding ]
  | Never -> tagged 4 []

and encode_argument = function
  | Type ty -> tagged 0 [ encode ty ]
  | Value v -> tagged 1 [ Cbor.Integer v ]

and encode_function f =
  Cbor.Array
    [
      Cbor.Array
        (List.map (fun (mode, ty) -> Cbor.Array [ encode_mode mode; encode ty ]) f.parameters);
      (match f.result with
      | Returns ty -> tagged 0 [ encode ty ]
      | Yields (mode, ty) -> tagged 1 [ encode_mode mode; encode ty ]
      | Lends (mode, ty) -> tagged 2 [ encode_mode mode; encode ty ]);
      Cbor.Array (List.map encode_definition f.uses);
    ]

and encode_yielding y =
  Cbor.Array
    [
      encode_definition y.method_;
      encode_mode y.receiver;
      Cbor.Array (List.map encode_argument y.type_arguments);
      Cbor.Array (List.map (fun set -> Cbor.Array (List.map encode_definition set)) y.capabilities);
    ]
