open Syntax

type digest = string

let format_version = 1

(* BLAKE3's code in the multiformats table. *)
let blake3_code = 0x1e
let prefix = String.init 2 (function 0 -> Char.chr format_version | _ -> Char.chr blake3_code)
let digest value = prefix ^ Blake3.hash (Cbor.encode value)
let show digest = Blake3.to_hex digest

type part =
  | Interface
  | Contract
  | Default of string
  | Body
  | Proof of int
  | Shape
  | Invariant of int
  | Potential
  | Value
  | Member of string * Path.receiver * part
  | Law of string

let rec show_part = function
  | Interface -> "interface"
  | Contract -> "contract"
  | Default name -> "default " ^ name
  | Body -> "body"
  | Proof index -> Printf.sprintf "proof %d" index
  | Shape -> "shape"
  | Invariant index -> Printf.sprintf "invariant %d" index
  | Potential -> "potential"
  | Value -> "value"
  | Member (name, receiver, part) ->
      let receiver =
        match receiver with
        | Static -> ""
        | Read -> "(self)"
        | Mut -> "(mut self)"
        | Own -> "(own self)"
      in
      Printf.sprintf "%s%s: %s" name receiver (show_part part)
  | Law name -> "law " ^ name

(* The encoding *)

let text value = Cbor.Text value
let node kind fields = Cbor.Array (text kind :: fields)
let list encode items = Cbor.Array (List.map encode items)
let option encode = function Some value -> encode value | None -> Cbor.Null
let bool value = Cbor.Bool value

type context = { resolved : Resolve.resolved; local_names : (id, string) Hashtbl.t }

(* A name, as what it refers to. Locals are hashed by their names, as
   DESIGN.md requires, so that cached messages show current names. *)
let name context (written : name) =
  match context.resolved.names.(written.id) with
  | None -> node "member" [ text written.text ]
  | Some target -> (
      match target with
      | Binding -> node "binding" [ text written.text ]
      | Local id | Generic id ->
          node "local"
            [ text (Option.value ~default:written.text (Hashtbl.find_opt context.local_names id)) ]
      | Definition path -> node "definition" [ text (Path.show path) ]
      | Variant (type_, variant) -> node "variant" [ text (Path.show type_); text variant ]
      | Module module_ -> node "module" [ text (Path.show_module module_) ]
      | Field field -> node "field" [ text field ]
      | Result_value -> node "result" []
      | Old -> node "old" []
      | Cost_function function_ ->
          node "cost_function"
            [
              text
                (match function_ with
                | Log -> "log"
                | Power -> "power"
                | Time -> "time"
                | Calls -> "calls");
            ]
      | Unknown -> node "unknown" [ text written.text ])

(* A path is hashed as its last name, which resolution resolved; the
   modules before it only say where to look. *)
let path context (written : path) = name context written.last
let mode = function Mut -> text "mut" | Own -> text "own"

let decimal (value : Token.Decimal.t) =
  (* The same number however it was written: no trailing zeros. *)
  let rec normal significand exponent =
    if (not (Z.equal significand Z.zero)) && Z.equal (Z.rem significand (Z.of_int 10)) Z.zero then
      normal (Z.div significand (Z.of_int 10)) (Z.succ exponent)
    else (significand, exponent)
  in
  let significand, exponent = normal value.significand value.exponent in
  node "float" [ Cbor.Integer significand; Cbor.Integer exponent ]

let binary_name = function
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

let assignment_name = function
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

let rec type_ context (written : type_expression) =
  match written.kind with
  | Path_type written -> path_type context written
  | Self_type key -> node "self" [ option (fun (key : Syntax.name) -> text key.text) key ]
  | Associated (base, key) -> node "associated" [ name context base; text key.text ]
  | Any_type written -> node "any" [ path_type context written ]
  | Function_type { inputs; output; clauses } ->
      node "function"
        [
          list
            (fun (written_mode, input) ->
              Cbor.Array [ option mode written_mode; type_ context input ])
            inputs;
          option (type_ context) output;
          clause_groups context clauses;
        ]
  | Type_error -> node "error" []

and path_type context (written : path_type) =
  node "path" [ path context written.path; list (type_argument context) written.arguments ]

and type_argument context = function
  | Type_argument written -> type_ context written
  | Count (value, _) -> Cbor.Integer value
  | Count_name written -> name context written
  | Constraint (key, written) -> node "constraint" [ text key.text; type_ context written ]

(* Clauses in groups by kind, in a fixed order of kinds, keeping the order
   written within each kind. *)
and clause_groups context (clauses : clause list) =
  let of_kind keep = List.filter_map keep clauses in
  Cbor.Array
    [
      list (path_type context)
        (List.concat
           (of_kind (fun (clause : clause) ->
                match clause.kind with Uses paths -> Some paths | _ -> None)));
      list (expression context)
        (of_kind (fun clause -> match clause.kind with Requires value -> Some value | _ -> None));
      list (expression context)
        (of_kind (fun clause -> match clause.kind with Ensures value -> Some value | _ -> None));
      list
        (list (expression context))
        (of_kind (fun clause ->
             match clause.kind with Decreases values -> Some values | _ -> None));
      list (cost context)
        (of_kind (fun clause -> match clause.kind with Cost cost -> Some cost | _ -> None));
    ]

and cost context (written : cost) =
  let resource =
    match written.resource with
    | Time -> text "time"
    | Allocations -> text "allocations"
    | Allocated_bytes -> text "allocated_bytes"
    | Calls (Call_parameter target) -> node "calls" [ name context target ]
    | Calls (Call_capability target) -> node "calls" [ path_type context target ]
    | Calls (Call_method (target, method_)) ->
        node "calls" [ path_type context target; text method_.text ]
  in
  let bound =
    match written.bound with
    | Big_o value -> node "O" [ expression context value ]
    | Finite -> text "finite"
    | At_most value -> node "<=" [ expression context value ]
    | Exactly value -> node "==" [ expression context value ]
  in
  Cbor.Array [ bool written.amortized; resource; bound ]

and string_literal context (literal : string_literal) =
  node "string"
    [
      option (path context) literal.tag;
      text literal.first.value;
      list
        (fun (value, (piece : Syntax.text)) ->
          Cbor.Array [ expression context value; text piece.value ])
        literal.rest;
    ]

and expression context (value : expression) =
  let expression = expression context in
  match value.kind with
  | Integer value -> Cbor.Integer value
  | Float value -> decimal value
  | String literal -> string_literal context literal
  | True -> Cbor.Bool true
  | False -> Cbor.Bool false
  | Todo -> node "todo" []
  | Unreachable -> node "unreachable" []
  | Break -> node "break" []
  | Continue -> node "continue" []
  | Self_value -> node "self" []
  | Self_type_value -> node "Self" []
  | Name written -> path context written
  | Member (base, member) -> node "." [ expression base; text member.text ]
  | Bracket (base, items) ->
      let reading =
        match context.resolved.brackets.(value.id) with
        | Some Index -> "index"
        | Some Type_arguments -> "type_arguments"
        | Some Method_bracket | None -> "bracket"
      in
      node reading
        [
          expression base;
          list
            (function
              | Item item -> expression item
              | Item_constraint (key, written) ->
                  node "constraint" [ text key.text; type_ context written ])
            items;
        ]
  | Call (callee, arguments) ->
      node "call"
        [
          expression callee;
          list
            (fun (argument : argument) ->
              Cbor.Array
                [
                  option (fun (label : Syntax.name) -> text label.text) argument.label;
                  expression argument.value;
                ])
            arguments;
        ]
  | Try inner -> node "?" [ expression inner ]
  | With (base, updates) ->
      node "with"
        [
          expression base;
          list
            (fun (update : update) ->
              match update.kind with
              | Update { field; path = rest; value } ->
                  Cbor.Array
                    [
                      list (fun (written : Syntax.name) -> text written.text) (field :: rest);
                      (match value with
                      | Some value -> expression value
                      | None -> name context field);
                    ]
              | Update_error -> node "error" [])
            updates;
        ]
  | Prefix (operator, inner) ->
      node
        (match operator with Negate -> "negate" | Not -> "!" | Complement -> "~")
        [ expression inner ]
  | Mode (written, inner) -> node "mode" [ mode written; expression inner ]
  | Any inner -> node "any" [ expression inner ]
  | Binary { operator; left; right; _ } ->
      node (binary_name operator) [ expression left; expression right ]
  | Is { value = tested; pattern = written; _ } ->
      node "is" [ expression tested; pattern context written ]
  | Range { start; stop; inclusive; _ } ->
      node (if inclusive then "..=" else "..") [ option expression start; option expression stop ]
  | Quantified { quantifier; binder; body } ->
      node
        (match quantifier with Forall -> "forall" | Exists -> "exists")
        [
          (match binder with
          | Binder_in (written, collection) ->
              node "in" [ pattern context written; expression collection ]
          | Binder_type (bound, written) -> node "type" [ text bound.text; type_ context written ]);
          expression body;
        ]
  | Echo inner -> node "echo" [ expression inner ]
  | Return inner -> node "return" [ option expression inner ]
  | Parenthesized inner -> expression inner
  | List items -> node "list" [ list expression items ]
  | Map entries ->
      node "map"
        [ list (fun (key, item) -> Cbor.Array [ expression key; expression item ]) entries ]
  | Lambda { parameters; body } ->
      node "lambda" [ list (pattern context) parameters; block context body ]
  | If { condition; then_; else_ } ->
      node "if"
        [
          expression condition;
          block context then_;
          option
            (function Else written -> block context written | Else_if branch -> expression branch)
            else_;
        ]
  | Match { scrutinees; arms } ->
      node "match"
        [
          list expression scrutinees;
          list
            (fun (arm : arm) ->
              Cbor.Array
                [
                  list (pattern context) arm.patterns;
                  option expression arm.guard;
                  statement context arm.body;
                ])
            arms;
        ]
  | Provide { implementations; body } ->
      node "provide" [ list expression implementations; block context body ]
  | Block body -> block context body
  | Expression_error -> node "error" []

(* A body's [proof] blocks are hashed apart from it, so editing a proof
   rebuilds no code. In the body, each stands as a placeholder. *)
and block context (written : block) = list (statement context) written.statements

and statement context (written : statement) =
  let expression = expression context in
  match written.kind with
  | Let { mutable_; pattern = bound; annotation; value; else_ } ->
      node
        (if mutable_ then "var" else "let")
        [
          pattern context bound;
          option (type_ context) annotation;
          expression value;
          option (block context) else_;
        ]
  | Expression value -> expression value
  | Assignment { target; operator; value } ->
      node (assignment_name operator) [ expression target; expression value ]
  | For { parallel; pattern = bound; iterable; clauses; body } ->
      node
        (if parallel then "parallel_for" else "for")
        [
          pattern context bound;
          expression iterable;
          loop_clauses context clauses;
          block context body;
        ]
  | While { condition; clauses; body } ->
      node "while" [ expression condition; loop_clauses context clauses; block context body ]
  | Parallel body -> node "parallel" [ block context body ]
  | Proof _ -> node "proof" []
  | Assert value -> node "assert" [ expression value ]
  | Yield value -> node "yield" [ expression value ]
  | Statement_error -> node "error" []

and loop_clauses context (clauses : loop_clause list) =
  Cbor.Array
    [
      list (expression context)
        (List.filter_map
           (fun (clause : loop_clause) ->
             match clause.kind with Invariant value -> Some value | _ -> None)
           clauses);
      list
        (list (expression context))
        (List.filter_map
           (fun (clause : loop_clause) ->
             match clause.kind with Loop_decreases values -> Some values | _ -> None)
           clauses);
    ]

and pattern context (written : pattern) =
  match written.kind with
  | Wildcard -> node "_" []
  | Binding_or_constant bound -> name context bound
  | Qualified_constant constant_ -> constant context constant_
  | Literal literal_ -> literal context literal_
  | Pattern_range { start; stop; inclusive } ->
      node (if inclusive then "..=" else "..") [ range_end context start; range_end context stop ]
  | Variant { name = variant; fields } ->
      node "variant" [ text variant.last.text; option (list (pattern_field context)) fields ]
  | Record fields -> node "record" [ list (pattern_field context) fields ]
  | Alternatives alternatives -> node "|" [ list (pattern context) alternatives ]
  | Pattern_error -> node "error" []

and pattern_field context (written : pattern_field) =
  match written.kind with
  | Named_field (field, inner) -> node "field" [ text field.text; pattern context inner ]
  | Field inner -> node "bare" [ pattern context inner ]
  | Rest -> node ".." []

and literal context = function
  | Literal_integer value -> Cbor.Integer value
  | Literal_true -> Cbor.Bool true
  | Literal_false -> Cbor.Bool false
  | Literal_string literal_ -> string_literal context literal_

and constant context = function
  | Module_constant written -> path context written
  | Type_constant (written, member) -> node "." [ path context written; text member.text ]

and range_end context (written : range_end) =
  match written.kind with
  | End_literal literal_ -> literal context literal_
  | End_constant constant_ -> constant context constant_
  | End_name bound -> name context bound

(* The proof blocks of a body, at any depth, in order. *)
let proofs (body : block) =
  let found = ref [] in
  let rec statement (written : statement) =
    match written.kind with
    | Proof inner -> found := inner :: !found
    | _ -> Syntax_walk.statement_parts ~expression ~statement written
  and expression value = Syntax_walk.expression_parts ~expression ~statement value in
  List.iter statement body.statements;
  List.rev !found

(* Definitions *)

let generic context (written : generic_parameter) =
  match written.kind with
  | Type_parameter (bound, bounds) ->
      node "type" [ text bound.text; list (path_type context) bounds ]
  | Value_parameter (bound, written) -> node "value" [ text bound.text; type_ context written ]
  | Capability_parameter bound -> node "capability" [ text bound.text ]
  | Generic_error -> node "error" []

let parameter context (written : parameter) =
  match written.kind with
  | Self_parameter written_mode -> node "self" [ option mode written_mode ]
  | Named_parameter { name = bound; mode = written_mode; type_ = written; default } ->
      node "parameter"
        [
          text bound.text;
          option mode written_mode;
          type_ context written;
          bool (Option.is_some default);
        ]
  | Parameter_error -> node "error" []

let result context = function
  | None -> Cbor.Null
  | Some (Returns written) -> node "->" [ type_ context written ]
  | Some (Yields (written_mode, written)) ->
      node "yields" [ option mode written_mode; type_ context written ]
  | Some (Lends (written_mode, written)) ->
      node "lends" [ option mode written_mode; type_ context written ]

let visibility = function
  | Private -> text "private"
  | Internal -> text "internal"
  | Public -> text "public"
  | Public_opaque -> text "public_opaque"

let head context = function
  | Plain_name _ -> Cbor.Null
  | Member_name (written, _) ->
      Cbor.Array [ path context written.path; list (generic context) written.generics ]

(* A signature's clauses, apart from [uses], are its contract. *)
let is_contract (clause : clause) =
  match clause.kind with Uses _ | Clause_error -> false | _ -> true

let signature_parts context ~visible (written : signature) ~body =
  let interface =
    node "interface"
      [
        visible;
        head context written.name;
        list (generic context) written.generics;
        list (parameter context) written.parameters;
        result context written.result;
        clause_groups context (List.filter (fun clause -> not (is_contract clause)) written.clauses);
      ]
  in
  let contract = clause_groups context (List.filter is_contract written.clauses) in
  let defaults =
    List.filter_map
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name = bound; default = Some value; _ } ->
            Some (Default bound.text, expression context value)
        | _ -> None)
      written.parameters
  in
  [ (Interface, interface); (Contract, contract) ]
  @ defaults
  @
  match body with
  | None -> []
  | Some body ->
      (Body, block context body)
      :: List.mapi (fun index proof -> (Proof index, block context proof)) (proofs body)

let field_shape context ~ordered (fields : field list) =
  let encoded =
    List.filter_map
      (fun (field : field) ->
        match field.kind with
        | Field_declaration { name = bound; type_ = written; default } ->
            Some
              ( bound.text,
                Cbor.Array [ text bound.text; type_ context written; bool (Option.is_some default) ]
              )
        | Field_error -> None)
      fields
  in
  (* Field order counts only for a derived [Ordered], which compares fields
     in the order declared. *)
  let encoded =
    if ordered then encoded else List.sort (fun (left, _) (right, _) -> compare left right) encoded
  in
  list snd encoded

let derives_ordered context (clauses : type_clause list) =
  List.exists
    (fun (clause : type_clause) ->
      match clause.kind with
      | Derives traits ->
          List.exists
            (fun (written : path_type) ->
              match context.resolved.names.(written.path.last.id) with
              | Some (Definition (Top { module_; name = "Ordered" })) ->
                  module_.package = Resolve.Prelude.standard
              | _ -> false)
            traits
      | _ -> false)
    clauses

let definition_parts context (definition : definition) =
  let visible = visibility definition.visibility in
  match definition.kind with
  | Function { signature; body } -> signature_parts context ~visible signature ~body:(Some body)
  | Type_definition { generics; body; clauses; _ } ->
      let ordered = derives_ordered context clauses in
      let encoded_body =
        match body with
        | Fields fields -> node "record" [ field_shape context ~ordered fields ]
        | Variants variants ->
            node "variants"
              [
                list
                  (fun (variant : variant) ->
                    Cbor.Array
                      [
                        text variant.name.text;
                        bool variant.indirect;
                        option (field_shape context ~ordered) variant.fields;
                      ])
                  variants;
              ]
        | Type_todo -> node "todo" []
      in
      let derives =
        List.concat_map
          (fun (clause : type_clause) ->
            match clause.kind with Derives traits -> traits | _ -> [])
          clauses
      in
      let field_defaults (fields : field list) =
        List.filter_map
          (fun (field : field) ->
            match field.kind with
            | Field_declaration { name = bound; default = Some value; _ } -> Some (bound.text, value)
            | _ -> None)
          fields
      in
      let defaults =
        match body with
        | Fields fields ->
            List.map (fun (name, value) -> (Default name, value)) (field_defaults fields)
        | Variants variants ->
            List.concat_map
              (fun (variant : variant) ->
                List.map
                  (fun (name, value) -> (Default (variant.name.text ^ "." ^ name), value))
                  (field_defaults (Option.value ~default:[] variant.fields)))
              variants
        | Type_todo -> []
      in
      let invariants =
        List.filter_map
          (fun (clause : type_clause) ->
            match clause.kind with Type_invariant value -> Some value | _ -> None)
          clauses
      in
      let potentials =
        List.filter_map
          (fun (clause : type_clause) ->
            match clause.kind with Potential value -> Some value | _ -> None)
          clauses
      in
      ( Shape,
        node "shape"
          [
            visible; list (generic context) generics; encoded_body; list (path_type context) derives;
          ] )
      :: List.map (fun (part, value) -> (part, expression context value)) defaults
      @ List.mapi (fun index value -> (Invariant index, expression context value)) invariants
      @ List.map (fun value -> (Potential, expression context value)) potentials
  | Trait { generics; requires; members; _ } ->
      let member_parts =
        List.concat_map
          (fun (line : trait_member line) ->
            match line.kind with
            | Trait_method { signature; body } ->
                let member =
                  match signature.name with
                  | Plain_name bound | Member_name (_, bound) -> bound.text
                in
                let receiver = Resolve.Names.receiver signature.parameters in
                List.map
                  (fun (part, value) -> (Member (member, receiver, part), value))
                  (signature_parts context ~visible:Cbor.Null signature ~body)
            | Associated_type (bound, bounds) ->
                [
                  ( Member (bound.text, Static, Interface),
                    node "associated" [ list (path_type context) bounds ] );
                ]
            | Law law ->
                [
                  ( Law law.name.text,
                    node "law"
                      [
                        list (parameter context) law.parameters;
                        list (expression context) law.requires;
                        block context law.body;
                      ] );
                ]
            | Trait_member_error -> [])
          members
      in
      let interfaces =
        List.filter_map
          (function
            | (Member (_, _, Interface) as part), value ->
                Some (Cbor.Array [ text (show_part part); value ])
            | _ -> None)
          member_parts
      in
      ( Interface,
        node "trait"
          [
            visible;
            list (generic context) generics;
            list (path_type context) requires;
            Cbor.Array interfaces;
          ] )
      :: List.filter (function Member (_, _, Interface), _ -> false | _ -> true) member_parts
  | Impl { trait_; type_ = head_; uses; members } ->
      let associated =
        List.filter_map
          (fun (line : impl_member line) ->
            match line.kind with
            | Associated_definition (bound, written) ->
                Some (Cbor.Array [ text bound.text; type_ context written ])
            | _ -> None)
          members
      in
      let methods =
        List.concat_map
          (fun (line : impl_member line) ->
            match line.kind with
            | Impl_method { signature; body } ->
                let member =
                  match signature.name with
                  | Plain_name bound | Member_name (_, bound) -> bound.text
                in
                let receiver = Resolve.Names.receiver signature.parameters in
                List.map
                  (fun (part, value) -> (Member (member, receiver, part), value))
                  (signature_parts context ~visible:Cbor.Null signature ~body:(Some body))
            | _ -> [])
          members
      in
      ( Interface,
        node "impl"
          [
            path_type context trait_;
            Cbor.Array [ path context head_.path; list (generic context) head_.generics ];
            list (path_type context) uses;
            Cbor.Array associated;
          ] )
      :: methods
  | Capability { members; _ } ->
      [
        ( Interface,
          node "capability"
            [
              visible;
              list
                (fun (line : capability_member line) ->
                  match line.kind with
                  | Capability_method signature ->
                      Cbor.Array
                        (List.map snd
                           (signature_parts context ~visible:Cbor.Null signature ~body:None))
                  | Capability_member_error -> node "error" [])
                members;
            ] );
      ]
  | Constant { name = written; type_ = written_type; value } ->
      [
        (Interface, node "constant" [ visible; head context written; type_ context written_type ]);
        (Value, expression context value);
      ]
  | Test { uses; body; _ } ->
      [ (Interface, node "test" [ list (path_type context) uses ]); (Body, block context body) ]
  | Theorem { generics; parameters; clauses; body; _ } ->
      [
        ( Interface,
          node "theorem"
            [
              visible;
              list (generic context) generics;
              list (parameter context) parameters;
              clause_groups context clauses;
            ] );
        (Body, block context body);
      ]
  | Law_proof { trait_; law; type_ = written; body } ->
      [
        ( Interface,
          node "law_proof" [ path_type context trait_; text law.text; type_ context written ] );
        (Body, block context body);
      ]
  | Definition_error _ -> [ (Interface, node "error" []) ]

let parts =
  Query.query ~name:"hash" ~show:Resolve.Names.show_key ~saved:true (fun database key ->
      match
        ( Query.demand database Resolve.Names.definition key,
          Query.demand database Resolve.resolved key )
      with
      | Some definition, Some resolved ->
          let local_names = Hashtbl.create 32 in
          List.iter
            (fun (written : Syntax.name) -> Hashtbl.replace local_names written.id written.text)
            (Syntax_walk.names definition);
          let context = { resolved; local_names } in
          let kind =
            match definition.kind with
            | Function _ -> "function"
            | Type_definition _ -> "type"
            | Trait _ -> "trait"
            | Impl _ -> "impl"
            | Capability _ -> "capability"
            | Constant _ -> "constant"
            | Test _ -> "test"
            | Theorem _ -> "theorem"
            | Law_proof _ -> "law_proof"
            | Definition_error _ -> "error"
          in
          Some
            (List.map
               (fun (part, value) ->
                 (part, digest (Cbor.Array [ text kind; text (show_part part); value ])))
               (definition_parts context definition))
      | _ -> None)

let part =
  Query.query ~name:"hash_part"
    ~show:(fun (key, part) -> Resolve.Names.show_key key ^ " " ^ show_part part)
    ~saved:true
    ~about:(fun ((key : Resolve.Names.key), part) ->
      Some { Query.path = key.path; part = Some (show_part part) })
    (fun database (key, wanted) ->
      match Query.demand database parts key with
      | Some parts -> List.assoc_opt wanted parts
      | None -> None)
