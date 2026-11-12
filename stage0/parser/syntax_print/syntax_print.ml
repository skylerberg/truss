open Syntax

let form head parts = "(" ^ String.concat " " (List.filter (( <> ) "") (head :: parts)) ^ ")"
let optional print = function Some value -> print value | None -> ""
let list print values = List.map print values

let path (path : path) =
  String.concat "::" (List.map (fun (name : name) -> name.text) (path.modules @ [ path.last ]))

let mode = function Mut -> "mut" | Own -> "own"

let binary = function
  | Multiply -> "*"
  | Divide -> "/"
  | Remainder -> "%"
  | Add -> "+"
  | Subtract -> "-"
  | Shift_left -> "<<"
  | Shift_right -> ">>"
  | Bit_and -> "&"
  | Bit_xor -> "^"
  | Bit_or -> "|"
  | Equal -> "=="
  | Not_equal -> "!="
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="
  | And -> "&&"
  | Or -> "||"
  | Implies -> "==>"

let assignment = function
  | Assign -> "="
  | Add_assign -> "+="
  | Subtract_assign -> "-="
  | Multiply_assign -> "*="
  | Divide_assign -> "/="
  | Remainder_assign -> "%="
  | Bit_and_assign -> "&="
  | Bit_or_assign -> "|="
  | Bit_xor_assign -> "^="
  | Shift_left_assign -> "<<="
  | Shift_right_assign -> ">>="

let escape value =
  let buffer = Buffer.create (String.length value + 2) in
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | character -> Buffer.add_char buffer character)
    value;
  Buffer.contents buffer

let rec type_expression (type_ : type_expression) =
  match type_.kind with
  | Path_type path_type -> path_type_text path_type
  | Self_type None -> "Self"
  | Self_type (Some name) -> "Self." ^ name.text
  | Associated (parameter, name) -> parameter.text ^ "." ^ name.text
  | Any_type path_type -> form "any" [ path_type_text path_type ]
  | Function_type function_type_ -> function_type function_type_
  | Type_error -> "error"

and path_type_text (path_type : path_type) =
  path path_type.path
  ^
  match path_type.arguments with
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (list type_argument arguments) ^ "]"

and type_argument = function
  | Type_argument type_ -> type_expression type_
  | Count (value, _) -> Z.to_string value
  | Count_name name -> name.text
  | Constraint (name, type_) -> name.text ^ " = " ^ type_expression type_

and function_type { inputs; input_names; output; clauses } =
  let named index =
    match List.nth_opt input_names index with Some name -> name.text ^ ": " | None -> ""
  in
  form "fn"
    ([
       form ""
         (List.mapi
            (fun index (input_mode, input) ->
              named index
              ^ (match input_mode with Some input -> mode input ^ " " | None -> "")
              ^ type_expression input)
            inputs);
     ]
    @ [ optional (fun output -> "-> " ^ type_expression output) output ]
    @ list clause clauses)

and generic (parameter : generic_parameter) =
  match parameter.kind with
  | Type_parameter (name, []) -> name.text
  | Type_parameter (name, bounds) ->
      name.text ^ ": " ^ String.concat " + " (list path_type_text bounds)
  | Value_parameter (name, type_) -> name.text ^ ": " ^ type_expression type_
  | Capability_parameter name -> "capability " ^ name.text
  | Generic_error -> "error"

and generics = function
  | [] -> ""
  | parameters -> "[" ^ String.concat ", " (list generic parameters) ^ "]"

and capability_reference (reference : capability_reference) =
  match reference.kind with
  | Capability_path path_type -> path_type_text path_type
  | Self_capabilities name -> "Self." ^ name.text
  | Associated_capabilities (parameter, name) -> parameter.text ^ "." ^ name.text

and clause (clause : clause) =
  match clause.kind with
  | Uses capabilities -> form "uses" (list capability_reference capabilities)
  | Requires value -> form "requires" [ expression value ]
  | Ensures value -> form "ensures" [ expression value ]
  | Decreases measures -> form "decreases" (list expression measures)
  | Cost cost_ -> cost cost_
  | Clause_error -> "error"

and cost { amortized; resource; bound } =
  let resource =
    match resource with
    | Time -> "time"
    | Allocations -> "allocations"
    | Allocated_bytes -> "allocated_bytes"
    | Calls (Call_parameter name) -> form "calls" [ name.text ]
    | Calls (Call_capability capability) -> form "calls" [ path_type_text capability ]
    | Calls (Call_method (capability, name)) ->
        form "calls" [ path_type_text capability ^ "." ^ name.text ]
  in
  let bound =
    match bound with
    | Big_o value -> form "O" [ expression value ]
    | Finite -> "finite"
    | At_most value -> form "<=" [ expression value ]
    | Exactly value -> form "==" [ expression value ]
  in
  form "cost" [ (if amortized then "amortized" else ""); resource; bound ]

and string_literal (literal : string_literal) =
  optional path literal.tag ^ "\"" ^ escape literal.first.value
  ^ String.concat ""
      (List.map
         (fun (value, (text : text)) -> "${" ^ expression value ^ "}" ^ escape text.value)
         literal.rest)
  ^ "\""

and expression (value : expression) =
  match value.kind with
  | Integer value -> Z.to_string value
  | Float { significand; exponent } ->
      Printf.sprintf "%se%s" (Z.to_string significand) (Z.to_string exponent)
  | String literal -> string_literal literal
  | True -> "true"
  | False -> "false"
  | Todo -> "todo"
  | Unreachable -> "unreachable"
  | Break -> "break"
  | Continue -> "continue"
  | Self_value -> "self"
  | Self_type_value -> "Self"
  | Name name -> path name
  | Member (inner, name) -> form "." [ expression inner; name.text ]
  | Bracket (inner, items) -> form "[]" (expression inner :: list bracket_item items)
  | Call (callee, arguments) -> form "call" (expression callee :: list argument arguments)
  | Try inner -> form "?" [ expression inner ]
  | With (base, updates) -> form "with" (expression base :: list update updates)
  | Prefix (operator, inner) ->
      form
        (match operator with Negate -> "-" | Not -> "!" | Complement -> "~")
        [ expression inner ]
  | Mode (written, inner) -> form (mode written) [ expression inner ]
  | Any inner -> form "any" [ expression inner ]
  | Binary { operator; left; right; _ } ->
      form (binary operator) [ expression left; expression right ]
  | Is { value = inner; pattern = tested; _ } -> form "is" [ expression inner; pattern tested ]
  | Range { start; stop; inclusive; _ } ->
      let bound = function Some value -> expression value | None -> "_" in
      form (if inclusive then "..=" else "..") [ bound start; bound stop ]
  | Quantified { quantifier; binder; body } ->
      let binder =
        match binder with
        | Binder_in (bound, collection) -> form "in" [ pattern bound; expression collection ]
        | Binder_type (name, type_) -> name.text ^ ": " ^ type_expression type_
      in
      form
        (match quantifier with Forall -> "forall" | Exists -> "exists")
        [ binder; expression body ]
  | Echo inner -> form "echo" [ expression inner ]
  | Return inner -> form "return" [ optional expression inner ]
  | Parenthesized inner -> form "paren" [ expression inner ]
  | List items -> form "list" (list expression items)
  | Map entries ->
      form "map" (list (fun (key, value) -> form "" [ expression key; expression value ]) entries)
  | Lambda { parameters; body } -> form "fn" [ form "" (list pattern parameters); block body ]
  | If { condition; then_; else_ } ->
      let else_ =
        match else_ with
        | Some (Else body) -> block body
        | Some (Else_if value) -> expression value
        | None -> ""
      in
      form "if" [ expression condition; block then_; else_ ]
  | Match { scrutinees; arms } ->
      form "match" (form "" (list expression scrutinees) :: list arm arms)
  | Provide { implementations; body } ->
      form "provide" [ form "" (list expression implementations); block body ]
  | Block body -> block body
  | Expression_error -> "error"

and bracket_item = function
  | Item value -> expression value
  | Item_constraint (name, type_) -> name.text ^ " = " ^ type_expression type_

and argument (argument : argument) =
  match argument.label with
  | Some label -> form (label.text ^ ":") [ expression argument.value ]
  | None -> expression argument.value

and update (update : update) =
  match update.kind with
  | Update { field; path; value } -> (
      let fields = String.concat "." (List.map (fun (name : name) -> name.text) (field :: path)) in
      match value with Some value -> form (fields ^ ":") [ expression value ] | None -> fields)
  | Update_error -> "error"

and arm (arm : arm) =
  form "=>"
    (list pattern arm.patterns
    @ [ optional (fun guard -> form "if" [ expression guard ]) arm.guard; statement arm.body ])

and block (block : block) = form "block" (list statement block.statements)

and loop_clause (clause : loop_clause) =
  match clause.kind with
  | Invariant value -> form "invariant" [ expression value ]
  | Loop_decreases measures -> form "decreases" (list expression measures)
  | Loop_cost cost_ -> cost cost_

and statement (statement : statement) =
  match statement.kind with
  | Let { is_var; pattern = bound; annotation; value; else_ } ->
      form
        (if is_var then "var" else "let")
        [
          pattern bound;
          optional (fun type_ -> ": " ^ type_expression type_) annotation;
          expression value;
          optional (fun body -> form "else" [ block body ]) else_;
        ]
  | Expression value -> expression value
  | Assignment { target; operator; value } ->
      form (assignment operator) [ expression target; expression value ]
  | For { mode; pattern = bound; iterable; clauses; body } ->
      form
        (match mode with
        | Sequential -> "for"
        | Parallel_loop -> "parallel-for"
        | Concurrent_loop -> "concurrent-for")
        ([ pattern bound; expression iterable ] @ list loop_clause clauses @ [ block body ])
  | While { condition; clauses; body } ->
      form "while" ((expression condition :: list loop_clause clauses) @ [ block body ])
  | Parallel body -> form "parallel" [ block body ]
  | Concurrent body -> form "concurrent" [ block body ]
  | Proof body -> form "proof" [ block body ]
  | Assert value -> form "assert" [ expression value ]
  | Yield value -> form "yield" [ expression value ]
  | Statement_error -> "error"

and constant = function
  | Module_constant constant -> path constant
  | Type_constant (owner, name) -> path owner ^ "." ^ name.text

and literal = function
  | Literal_integer value -> Z.to_string value
  | Literal_true -> "true"
  | Literal_false -> "false"
  | Literal_string literal -> string_literal literal

and pattern (written : pattern) =
  match written.kind with
  | Wildcard -> "_"
  | Binding_or_constant name -> name.text
  | Qualified_constant written -> constant written
  | Literal written -> literal written
  | Pattern_range { start; stop; inclusive } ->
      let range_end (written : range_end) =
        match written.kind with
        | End_literal value -> literal value
        | End_constant value -> constant value
        | End_name name -> name.text
      in
      form (if inclusive then "..=" else "..") [ range_end start; range_end stop ]
  | Variant { name; fields = None } -> path name
  | Variant { name; fields = Some fields } -> form (path name) (list pattern_field fields)
  | Record fields -> form "record" (list pattern_field fields)
  | Alternatives alternatives -> form "|" (list pattern alternatives)
  | Pattern_error -> "error"

and pattern_field (field : pattern_field) =
  match field.kind with
  | Named_field (name, inner) -> form (name.text ^ ":") [ pattern inner ]
  | Field inner -> pattern inner
  | Rest -> ".."

let visibility = function
  | Private -> ""
  | Internal -> "internal"
  | Public -> "public"
  | Public_opaque -> "public opaque"
  | Public_transparent -> "public transparent"

let type_head (head : type_head) = path head.path ^ generics head.generics

let definition_name = function
  | Plain_name name -> name.text
  | Member_name (head, name) -> type_head head ^ "." ^ name.text

let parameter (parameter : parameter) =
  match parameter.kind with
  | Self_parameter None -> "self"
  | Self_parameter (Some written) -> mode written ^ " self"
  | Named_parameter { name; mode = written; type_; default } ->
      form (name.text ^ ":")
        [
          (match written with Some written -> mode written | None -> "");
          type_expression type_;
          optional (fun value -> form "=" [ expression value ]) default;
        ]
  | Parameter_error -> "error"

let moded written type_ =
  (match written with Some written -> mode written ^ " " | None -> "") ^ type_expression type_

let signature (signature : signature) =
  [
    definition_name signature.name ^ generics signature.generics;
    form "" (list parameter signature.parameters);
    (match signature.result with
    | Some (Returns type_) -> "-> " ^ type_expression type_
    | Some (Yields (written, type_)) -> "yields " ^ moded written type_
    | Some (Lends (written, type_)) -> "lends " ^ moded written type_
    | None -> "");
  ]
  @ list clause signature.clauses

let function_ written body = form "fn" (signature written @ [ optional block body ])

let law ({ name; parameters; requires; body } : law) =
  form "law"
    ([ name.text; form "" (list parameter parameters) ]
    @ list (fun value -> form "requires" [ expression value ]) requires
    @ [ block body ])

let function_definition (definition : function_definition) =
  function_ definition.signature (Some definition.body)

let field (field : field) =
  match field.kind with
  | Field_declaration { name; type_; default } ->
      form (name.text ^ ":")
        [ type_expression type_; optional (fun value -> form "=" [ expression value ]) default ]
  | Field_error -> "error"

let fields list_ = form "" (list field list_)

let members print (members : _ line list) =
  list (fun (member : _ line) -> print member.kind) members

(* [methods] are the methods written inside a trait, an [impl], or a
   capability, already printed, which come after its own members. *)
let definition ?(methods = []) (definition : definition) =
  let body =
    match definition.kind with
    | Function function_ -> function_definition function_
    | Method_declaration declared -> form "fn" (signature declared)
    | Type_definition { name; generics = parameters; body; clauses } ->
        let body =
          match body with
          | Fields list_ -> fields list_
          | Variants variants ->
              form "="
                (list
                   (fun (variant : variant) ->
                     let name =
                       (if variant.indirect then "indirect " else "") ^ variant.name.text
                     in
                     match variant.fields with
                     | Some list_ -> form name [ fields list_ ]
                     | None -> name)
                   variants)
          | Type_todo -> "= todo"
        in
        let clauses =
          list
            (fun (clause : type_clause) ->
              match clause.kind with
              | Type_invariant value -> form "invariant" [ expression value ]
              | Derives traits -> form "derives" (list path_type_text traits)
              | Potential value -> form "cost potential" [ expression value ])
            clauses
        in
        form "type" ([ name.text ^ generics parameters; body ] @ clauses)
    | Trait { name; generics = parameters; requires; members = trait_members } ->
        form "trait"
          ([
             name.text ^ generics parameters;
             (match requires with
             | [] -> ""
             | _ -> ": " ^ String.concat " + " (list path_type_text requires));
           ]
          @ members
              (function
                | Associated_type (name, []) -> form "type" [ name.text ]
                | Associated_type (name, bounds) ->
                    form "type"
                      [ name.text ^ ": " ^ String.concat " + " (list path_type_text bounds) ]
                | Associated_capability name -> form "capability" [ name.text ]
                | Law written -> law written
                | Trait_member_error -> "error")
              trait_members
          @ methods)
    | Impl { trait_; type_; uses; members = impl_members } ->
        form "impl"
          ([
             path_type_text trait_;
             "for";
             type_head type_;
             (match uses with [] -> "" | _ -> form "uses" (list capability_reference uses));
           ]
          @ members
              (function
                | Associated_definition (name, type_) ->
                    form "type" [ name.text; "="; type_expression type_ ]
                | Capability_definition (name, capabilities) ->
                    form "capability" (name.text :: "=" :: list capability_reference capabilities)
                | Impl_member_error -> "error")
              impl_members
          @ methods)
    | Capability { name; members = capability_members } ->
        form "capability"
          ((name.text :: members (function Capability_member_error -> "error") capability_members)
          @ methods)
    | Constant { name; type_; value } ->
        form "let" [ definition_name name; ": " ^ type_expression type_; expression value ]
    | Test { name; uses; body } ->
        form "test"
          [
            string_literal name;
            (match uses with [] -> "" | _ -> form "uses" (list capability_reference uses));
            block body;
          ]
    | Theorem { name; generics = parameters; parameters = theorem_parameters; clauses; body } ->
        form "theorem"
          ([ name.text ^ generics parameters; form "" (list parameter theorem_parameters) ]
          @ list clause clauses
          @ [ block body ])
    | Law_proof { trait_; law; type_; body } ->
        form "proof" [ path_type_text trait_ ^ "." ^ law.text; "for"; type_head type_; block body ]
    | Definition_error { keyword; name } ->
        form "error" [ optional Token.keyword_spelling keyword; optional definition_name name ]
  in
  match visibility definition.visibility with "" -> body | written -> form written [ body ]

(* A file's definitions, with each method inside the trait, the [impl], or
   the capability it is written inside. *)
let definitions (items : definition item list) =
  let inside index =
    List.filter_map
      (fun (item : definition item) ->
        if item.container = Some index then Some (definition item.value) else None)
      items
  in
  List.concat
    (List.mapi
       (fun index (item : definition item) ->
         match item.container with
         | Some _ -> []
         | None -> [ definition ~methods:(inside index) item.value ])
       items)

let file (file : file) =
  String.concat "\n"
    (List.map (fun (item : path item) -> form "use" [ path item.value ]) file.uses
    @ definitions file.definitions)

module For_testing = struct
  let definition = definition
  let definitions = definitions
end
