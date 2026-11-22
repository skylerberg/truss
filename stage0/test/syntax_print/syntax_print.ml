let make_form head parts = "(" ^ String.concat " " (List.filter (( <> ) "") (head :: parts)) ^ ")"
let show_optional print = function Some value -> print value | None -> ""
let list print values = List.map print values

let show_path (path : Syntax.path) =
  String.concat "."
    (List.map (fun (name : Syntax.name) -> name.text) (path.modules @ [ path.last ]))

let show_mode = function Syntax.Mut -> "mut" | Own -> "own"

let show_intended_keyword = function
  | Syntax.Intended_function -> "fn"
  | Intended_constant -> "let"
  | Intended_type -> "type"
  | Intended_trait -> "trait"
  | Intended_capability -> "capability"
  | Intended_theorem -> "theorem"

let show_operation = function
  | Syntax.Arithmetic Multiply -> "*"
  | Arithmetic Divide -> "/"
  | Arithmetic Remainder -> "%"
  | Arithmetic Add -> "+"
  | Arithmetic Subtract -> "-"
  | Shift Shift_left -> "<<"
  | Shift Shift_right -> ">>"
  | Bitwise Bit_and -> "&"
  | Bitwise Bit_xor -> "^"
  | Bitwise Bit_or -> "|"

let show_binary = function
  | Syntax.Operation written -> show_operation written
  | Comparison Equal -> "=="
  | Comparison Not_equal -> "!="
  | Comparison Less -> "<"
  | Comparison Less_equal -> "<="
  | Comparison Greater -> ">"
  | Comparison Greater_equal -> ">="
  | Connective And -> "&&"
  | Connective Or -> "||"
  | Connective Implies -> "==>"

let show_assignment = function
  | Syntax.Assign -> "="
  | Compound written -> show_operation written ^ "="

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

let rec show_type_expression (type_ : Syntax.type_expression) =
  match type_.kind with
  | Path_type path_type -> show_path_type path_type
  | Self_type None -> "Self"
  | Self_type (Some name) -> "Self." ^ name.text
  | Associated (parameter, name) -> parameter.text ^ "." ^ name.text
  | Any_type path_type -> make_form "any" [ show_path_type path_type ]
  | Function_type function_type_ -> show_function_type function_type_
  | Type_error -> "error"

and show_path_type (path_type : Syntax.path_type) =
  show_path path_type.path
  ^
  match path_type.arguments with
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (list show_type_argument arguments) ^ "]"

and show_type_argument = function
  | Type_argument type_ -> show_type_expression type_
  | Count (value, _) -> Z.to_string value
  | Count_name name -> name.text
  | Constraint (name, type_) -> name.text ^ " = " ^ show_type_expression type_

and show_function_type { inputs; output; clauses } =
  make_form "fn"
    ([
       make_form ""
         (List.map
            (fun (input : Syntax.function_input) ->
              (match input.name with Some name -> name.text ^ ": " | None -> "")
              ^ (match input.mode with Some input_mode -> show_mode input_mode ^ " " | None -> "")
              ^ show_type_expression input.type_)
            inputs);
     ]
    @ [ show_optional (fun output -> "-> " ^ show_type_expression output) output ]
    @ list show_clause clauses)

and show_generic (parameter : Syntax.generic_parameter) =
  match parameter.kind with
  | Type_parameter (name, []) -> name.text
  | Type_parameter (name, bounds) ->
      name.text ^ ": " ^ String.concat " + " (list show_path_type bounds)
  | Value_parameter (name, type_) -> name.text ^ ": " ^ show_type_expression type_
  | Generic_error -> "error"

and show_generics = function
  | [] -> ""
  | parameters -> "[" ^ String.concat ", " (list show_generic parameters) ^ "]"

and show_capability_reference (reference : Syntax.capability_reference) =
  match reference.kind with
  | Capability_path path_type -> show_path_type path_type
  | Self_capabilities name -> "Self." ^ name.text
  | Associated_capabilities (parameter, name) -> parameter.text ^ "." ^ name.text
  | Generic_capability name -> "generic " ^ name.text

and show_condition (condition : Syntax.condition) =
  String.concat " && "
    (list
       (fun (bound : Syntax.bound_condition) ->
         show_type_expression bound.subject
         ^ ": "
         ^ String.concat " + " (list show_path_type bound.bounds))
       condition)

and show_conditional shown = function
  | Some condition -> make_form "when" [ shown; show_condition condition ]
  | None -> shown

and show_capability_use (use : Syntax.capability_use) =
  match (use.unless, use.unless_values) with
  | None, [] -> show_capability_reference use.capability
  | unless, values ->
      make_form "unless"
        (show_capability_reference use.capability
         :: Option.to_list (Option.map show_condition unless)
        @ List.map show_expression values)

and show_clause (clause : Syntax.clause) =
  show_conditional
    (match clause.kind with
    | Uses uses -> make_form "uses" (list show_capability_use uses)
    | Requires value -> make_form "requires" [ show_expression value ]
    | Ensures value -> make_form "ensures" [ show_expression value ]
    | Decreases measures -> make_form "decreases" (list show_expression measures)
    | Cost cost_ -> show_cost cost_
    | Clause_error -> "error")
    clause.condition

and show_cost { amortized; resource; bound } =
  let resource =
    match resource with
    | Metric metric -> Language.Metric.show metric
    | Calls (Call_parameter name) -> make_form "calls" [ name.text ]
    | Calls (Call_capability capability) -> make_form "calls" [ show_path_type capability ]
    | Calls (Call_method (capability, name)) ->
        make_form "calls" [ show_path_type capability ^ "." ^ name.text ]
  in
  let bound =
    match bound with
    | Big_o value -> make_form "O" [ show_expression value ]
    | At_most value -> make_form "<=" [ show_expression value ]
    | Exactly value -> make_form "==" [ show_expression value ]
  in
  make_form "cost" [ (if amortized then "amortized" else ""); resource; bound ]

and show_string_literal (literal : Syntax.string_literal) =
  show_optional show_path literal.tag
  ^ "\"" ^ escape literal.first.value
  ^ String.concat ""
      (List.map
         (fun (value, (text : Syntax.text)) ->
           "${" ^ show_expression value ^ "}" ^ escape text.value)
         literal.rest)
  ^ "\""

and show_expression (value : Syntax.expression) =
  match value.kind with
  | Integer value -> Z.to_string value
  | Float { significand; exponent } ->
      Printf.sprintf "%se%s" (Z.to_string significand) (Z.to_string exponent)
  | String literal -> show_string_literal literal
  | True -> "true"
  | False -> "false"
  | Todo -> "todo"
  | Unreachable -> "unreachable"
  | Break -> "break"
  | Continue -> "continue"
  | Self_value -> "self"
  | Self_type_value -> "Self"
  | Name name -> name.text
  | Member (inner, name) -> make_form "." [ show_expression inner; name.text ]
  | Bracket (inner, items) -> make_form "[]" (show_expression inner :: list show_bracket_item items)
  | Call (callee, arguments) ->
      make_form "call" (show_expression callee :: list show_argument arguments)
  | Try inner -> make_form "?" [ show_expression inner ]
  | With (base, updates) -> make_form "with" (show_expression base :: list update updates)
  | Prefix (operator, inner) ->
      make_form
        (match operator with Negate -> "-" | Not -> "!" | Complement -> "~")
        [ show_expression inner ]
  | Mode (written, inner) -> make_form (show_mode written) [ show_expression inner ]
  | Any inner -> make_form "any" [ show_expression inner ]
  | Binary { operator; left; right; _ } ->
      make_form (show_binary operator) [ show_expression left; show_expression right ]
  | Is { value = inner; pattern = tested; _ } ->
      make_form "is" [ show_expression inner; show_pattern tested ]
  | Range { start; stop; inclusive; _ } ->
      let show_bound = function Some value -> show_expression value | None -> "_" in
      make_form (if inclusive then "..=" else "..") [ show_bound start; show_bound stop ]
  | Quantified { quantifier; binder; body } ->
      let binder =
        match binder with
        | Binder_in (bound, collection) ->
            make_form "in" [ show_pattern bound; show_expression collection ]
        | Binder_type (name, type_) -> name.text ^ ": " ^ show_type_expression type_
      in
      make_form
        (match quantifier with Forall -> "forall" | Exists -> "exists")
        [ binder; show_expression body ]
  | Echo inner -> make_form "echo" [ show_expression inner ]
  | Return inner -> make_form "return" [ show_optional show_expression inner ]
  | Parenthesized inner -> make_form "paren" [ show_expression inner ]
  | List items -> make_form "list" (list show_expression items)
  | Map entries ->
      make_form "map"
        (list
           (fun (key, value) -> make_form "" [ show_expression key; show_expression value ])
           entries)
  | Lambda { parameters; body } ->
      make_form "fn" [ make_form "" (list show_pattern parameters); show_block body ]
  | If { condition; then_; else_ } ->
      let else_ =
        match else_ with
        | Some (Else body) -> show_block body
        | Some (Else_if value) -> show_expression value
        | None -> ""
      in
      make_form "if" [ show_expression condition; show_block then_; else_ ]
  | Match { scrutinees; arms } ->
      make_form "match" (make_form "" (list show_expression scrutinees) :: list show_arm arms)
  | Provide { implementations; body } ->
      make_form "provide" [ make_form "" (list show_expression implementations); show_block body ]
  | Block body -> show_block body
  | Expression_error -> "error"

and show_bracket_item = function
  | Item value -> show_expression value
  | Item_constraint (name, type_) -> name.text ^ " = " ^ show_type_expression type_

and show_argument (argument : Syntax.argument) =
  match argument.label with
  | Some label -> make_form (label.text ^ ":") [ show_expression argument.value ]
  | None -> show_expression argument.value

and update (update : Syntax.update) =
  match update.kind with
  | Update { path = []; value } -> show_expression value
  | Update { path; value } ->
      make_form
        (String.concat "." (List.map (fun (name : Syntax.name) -> name.text) path) ^ ":")
        [ show_expression value ]
  | Update_error -> "error"

and show_arm (arm : Syntax.arm) =
  make_form "=>"
    (list show_pattern arm.patterns
    @ [
        show_optional (fun guard -> make_form "if" [ show_expression guard ]) arm.guard;
        show_statement arm.body;
      ])

and show_block (block : Syntax.block) = make_form "block" (list show_statement block.statements)

and show_loop_clause (clause : Syntax.loop_clause) =
  show_conditional
    (match clause.kind with
    | Invariant value -> make_form "invariant" [ show_expression value ]
    | Loop_decreases measures -> make_form "decreases" (list show_expression measures)
    | Loop_cost cost_ -> show_cost cost_)
    clause.condition

and show_statement (statement : Syntax.statement) =
  match statement.kind with
  | Let { is_var; pattern = bound; annotation; value; else_ } ->
      make_form
        (if is_var then "var" else "let")
        [
          show_pattern bound;
          show_optional (fun type_ -> ": " ^ show_type_expression type_) annotation;
          show_expression value;
          show_optional (fun body -> make_form "else" [ show_block body ]) else_;
        ]
  | Expression value -> show_expression value
  | Assignment { target; operator; value } ->
      make_form (show_assignment operator) [ show_expression target; show_expression value ]
  | For { mode; pattern = bound; annotation; iterable; clauses; body } ->
      make_form
        (match mode with
        | Sequential -> "for"
        | Parallel -> "parallel-for"
        | Concurrent -> "concurrent-for")
        ([
           show_pattern bound;
           show_optional (fun type_ -> ": " ^ show_type_expression type_) annotation;
           show_expression iterable;
         ]
        @ list show_loop_clause clauses
        @ [ show_block body ])
  | While { condition; clauses; body } ->
      make_form "while"
        ((show_expression condition :: list show_loop_clause clauses) @ [ show_block body ])
  | Parallel body -> make_form "parallel" [ show_block body ]
  | Concurrent body -> make_form "concurrent" [ show_block body ]
  | Proof body -> make_form "proof" [ show_block body ]
  | Assert { value; by } ->
      make_form "assert"
        (show_expression value
        ::
        (match by with
        | Some Bit_vector -> [ "by"; "bit_vector" ]
        | Some Evaluation -> [ "by"; "evaluation" ]
        | None -> []))
  | Statement_error -> "error"

and show_constant = function
  | Syntax.Module_constant constant -> show_path constant
  | Type_constant (owner, name) -> show_path owner ^ "." ^ name.text

and show_literal = function
  | Syntax.Literal_integer value -> Z.to_string value
  | Literal_true -> "true"
  | Literal_false -> "false"
  | Literal_string literal -> show_string_literal literal

and show_pattern (written : Syntax.pattern) =
  match written.kind with
  | Wildcard -> "_"
  | Binding name -> name.text
  | Qualified_constant written -> show_constant written
  | Literal written -> show_literal written
  | Pattern_range { start; stop; inclusive } ->
      let show_range_end (written : Syntax.range_end) =
        match written.kind with
        | End_literal value -> show_literal value
        | End_constant value -> show_constant value
      in
      make_form (if inclusive then "..=" else "..") [ show_range_end start; show_range_end stop ]
  | Variant { name; fields = None } -> name.text
  | Variant { name; fields = Some fields } -> make_form name.text (list show_pattern_field fields)
  | Record fields -> make_form "record" (list show_pattern_field fields)
  | Tuple patterns -> make_form "tuple" (list show_pattern patterns)
  | Alternatives alternatives -> make_form "|" (list show_pattern alternatives)
  | Pattern_error -> "error"

and show_pattern_field (field : Syntax.pattern_field) =
  match field.kind with
  | Named_field (name, inner) -> make_form (name.text ^ ":") [ show_pattern inner ]
  | Field inner -> show_pattern inner
  | Rest -> ".."

let show_visibility : Syntax.visibility option -> string = function
  | None -> ""
  | Some Internal -> "internal"
  | Some Public -> "public"
  | Some Public_opaque -> "public opaque"

let show_type_head (head : Syntax.type_head) = show_path head.path ^ show_generics head.generics

let show_definition_name = function
  | Syntax.Plain_name name -> name.text
  | Member_name (head, name) -> show_type_head head ^ "." ^ name.text

let show_parameter (parameter : Syntax.parameter) =
  match parameter.kind with
  | Self_parameter None -> "self"
  | Self_parameter (Some written) -> show_mode written ^ " self"
  | Named_parameter { name; mode = written; type_; default } ->
      make_form (name.text ^ ":")
        [
          (match written with Some written -> show_mode written | None -> "");
          show_type_expression type_;
          show_optional (fun value -> make_form "=" [ show_expression value ]) default;
        ]
  | Parameter_error -> "error"

let show_moded written type_ =
  (match written with Some written -> show_mode written ^ " " | None -> "")
  ^ show_type_expression type_

let show_signature (signature : Syntax.signature) =
  [
    show_definition_name signature.name ^ show_generics signature.generics;
    make_form "" (list show_parameter signature.parameters);
    (match signature.result with
    | Some (Returns type_) -> "-> " ^ show_type_expression type_
    | Some (Lends (written, type_)) -> "lends " ^ show_moded written type_
    | None -> "");
  ]
  @ list show_clause signature.clauses

let show_law ({ name; parameters; requires; body } : Syntax.law) =
  make_form "law"
    ([ name.text; make_form "" (list show_parameter parameters) ]
    @ list (fun value -> make_form "requires" [ show_expression value ]) requires
    @ [ show_block body ])

let show_function_definition (definition : Syntax.function_definition) =
  make_form "fn" (show_signature definition.signature @ [ show_block definition.body ])

let show_field (field : Syntax.field) =
  match field.kind with
  | Field_declaration { name; type_; default } ->
      make_form (name.text ^ ":")
        [
          show_type_expression type_;
          show_optional (fun value -> make_form "=" [ show_expression value ]) default;
        ]
  | Field_error -> "error"

let show_fields list_ = make_form "" (list show_field list_)

let show_members print (members : _ Syntax.node list) =
  list (fun (member : _ Syntax.node) -> print member.kind) members

let show_definition ?(methods = []) (definition : Syntax.definition) =
  let body =
    match definition.kind with
    | Function function_ -> show_function_definition function_
    | Method_declaration declared -> make_form "fn" (show_signature declared)
    | Type_definition { is_tuple; name; generics = parameters; body; clauses } ->
        let body =
          match body with
          | Fields list_ -> show_fields list_
          | Variants variants ->
              make_form "="
                (list
                   (fun (variant : Syntax.variant) ->
                     let name =
                       (if variant.indirect then "indirect " else "") ^ variant.name.text
                     in
                     match variant.fields with
                     | Some list_ -> make_form name [ show_fields list_ ]
                     | None -> name)
                   variants)
          | Type_todo -> "= todo"
        in
        let clauses =
          list
            (fun (clause : Syntax.type_clause) ->
              match clause.kind with
              | Type_invariant value -> make_form "invariant" [ show_expression value ]
              | Derives traits -> make_form "derives" (list show_path_type traits)
              | Potential value -> make_form "cost potential" [ show_expression value ])
            clauses
        in
        make_form
          (if is_tuple then "tuple type" else "type")
          ([ name.text ^ show_generics parameters; body ] @ clauses)
    | Trait { name; generics = parameters; requires; members = trait_members } ->
        make_form "trait"
          ([
             name.text ^ show_generics parameters;
             (match requires with
             | [] -> ""
             | _ -> ": " ^ String.concat " + " (list show_path_type requires));
           ]
          @ show_members
              (function
                | Syntax.Associated_type (name, []) -> make_form "type" [ name.text ]
                | Associated_type (name, bounds) ->
                    make_form "type"
                      [ name.text ^ ": " ^ String.concat " + " (list show_path_type bounds) ]
                | Associated_capability name -> make_form "capability" [ name.text ]
                | Law written -> show_law written
                | Trait_member_error -> "error")
              trait_members
          @ methods)
    | Impl { trait_; type_; uses; members = impl_members } ->
        make_form "impl"
          ([
             show_path_type trait_;
             "for";
             show_type_head type_;
             (match uses with
             | [] -> ""
             | _ -> make_form "uses" (list show_capability_reference uses));
           ]
          @ show_members
              (function
                | Syntax.Associated_definition (name, type_) ->
                    make_form "type" [ name.text; "="; show_type_expression type_ ]
                | Capability_definition (name, capabilities) ->
                    make_form "capability"
                      (name.text :: "=" :: list show_capability_use capabilities)
                | Impl_member_error -> "error")
              impl_members
          @ methods)
    | Capability { name; members = capability_members } ->
        make_form "capability"
          (name.text
           :: show_members (function Syntax.Capability_member_error -> "error") capability_members
          @ methods)
    | Constant { name; type_; value } ->
        make_form "let"
          [ show_definition_name name; ": " ^ show_type_expression type_; show_expression value ]
    | Test { name; uses; body } ->
        make_form "test"
          [
            show_string_literal name;
            (match uses with
            | [] -> ""
            | _ -> make_form "uses" (list show_capability_reference uses));
            show_block body;
          ]
    | Theorem { name; generics = parameters; parameters = theorem_parameters; clauses; body } ->
        make_form "theorem"
          ([
             name.text ^ show_generics parameters;
             make_form "" (list show_parameter theorem_parameters);
           ]
          @ list show_clause clauses
          @ [ show_block body ])
    | Law_proof { trait_; law; type_; body } ->
        make_form "proof"
          [ show_path_type trait_ ^ "." ^ law.text; "for"; show_type_head type_; show_block body ]
    | Definition_error { intended; name } ->
        make_form "error"
          [ show_optional show_intended_keyword intended; show_optional show_definition_name name ]
  in
  match show_visibility definition.visibility with
  | "" -> body
  | written -> make_form written [ body ]

let show_definitions (top_levels : Syntax.top_level list) =
  List.map
    (fun (top_level : Syntax.top_level) ->
      show_definition
        ~methods:
          (List.map
             (fun (method_ : Syntax.definition Syntax.item) -> show_definition method_.value)
             top_level.methods)
        top_level.definition.value)
    top_levels

let show_file (file : Syntax.file) =
  String.concat "\n"
    (List.map
       (fun (item : Syntax.path Syntax.item) -> make_form "use" [ show_path item.value ])
       file.uses
    @ show_definitions file.definitions)
