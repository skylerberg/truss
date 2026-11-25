type id = int
type case = Upper | Lower
type name = { text : string; case : case; id : id }
type path = { modules : name list; last : name }
type mode = Mut | Own
type prefix = Negate | Not | Complement
type arithmetic = Multiply | Divide | Remainder | Add | Subtract
type bitwise = Bit_and | Bit_xor | Bit_or
type shift = Shift_left | Shift_right
type operation = Arithmetic of arithmetic | Bitwise of bitwise | Shift of shift

type binary =
  | Operation of operation
  | Comparison of Language.Comparison.t
  | Connective of Language.Connective.t

type assignment = Assign | Compound of operation
type 'kind node = { kind : 'kind; id : id }

type type_expression = type_kind node

and type_kind =
  | Path_type of path_type
  | Self_type of name option
  | Associated of name * name
  | Function_type of function_type
  | View_type of type_expression
  | Type_error

and path_type = { path : path; arguments : type_argument list; id : id }

and type_argument =
  | Type_argument of type_expression
  | Count of Z.t * id
  | Count_name of name
  | Constraint of name * type_expression

and function_type = {
  inputs : function_input list;
  output : type_expression option;
  clauses : clause list;
}

and function_input = { name : name option; mode : mode option; type_ : type_expression }
and generic_parameter = generic_kind node

and generic_kind =
  | Type_parameter of name * path_type list
  | Value_parameter of name * type_expression
  | Generic_error

and capability_reference = capability_reference_kind node

and capability_reference_kind =
  | Capability_path of path_type
  | Self_capabilities of name
  | Associated_capabilities of name * name
  | Generic_capability of name

and clause = { kind : clause_kind; condition : condition option; id : id }

and clause_kind =
  | Uses of capability_use list
  | Requires of expression
  | Ensures of expression
  | Decreases of expression list
  | Modifies of expression list
  | Cost of cost
  | Clause_error

and capability_use = {
  capability : capability_reference;
  unless : condition option;
  unless_values : expression list;
}

and condition = bound_condition list
and bound_condition = { subject : type_expression; bounds : path_type list; id : id }
and cost = { amortized : bool; resource : resource; bound : bound }
and resource = Metric of Language.Metric.t | Calls of call_target

and call_target =
  | Call_parameter of name
  | Call_capability of path_type
  | Call_method of path_type * name

and bound = Big_o of expression | At_most of expression | Exactly of expression
and expression = expression_kind node

and expression_kind =
  | Integer of Z.t
  | Float of Token.Decimal.t
  | String of string_literal
  | True
  | False
  | Todo
  | Unreachable
  | Break
  | Continue
  | Self_value
  | Self_type_value
  | Name of name
  | Member of expression * name
  | Bracket of expression * bracket_item list
  | Call of expression * argument list
  | Try of expression
  | With of expression * update list
  | Prefix of prefix * expression
  | Mode of mode * expression
  | Binary of { operator : binary; operator_id : id; left : expression; right : expression }
  | Is of { value : expression; operator_id : id; pattern : pattern }
  | Range of {
      start : expression option;
      operator_id : id;
      stop : expression option;
      inclusive : bool;
    }
  | Quantified of { quantifier : Language.Quantifier.t; binder : binder; body : expression }
  | Echo of expression
  | Return of expression option
  | Parenthesized of expression
  | List of expression list
  | Map of (expression * expression) list
  | Lambda of { parameters : pattern list; body : block }
  | If of { condition : expression; then_ : block; else_ : else_branch option }
  | Match of { scrutinees : expression list; arms : arm list }
  | Provide of { implementations : expression list; body : block }
  | Block of block
  | Expression_error

and string_literal = {
  tag : path option;
  form : Token.form;
  first : text;
  rest : (expression * text) list;
  id : id;
}

and text = { value : string; id : id }
and argument = { label : name option; value : expression }

and bracket_item =
  | Item of expression
  | Item_constraint of name * type_expression
  | Item_type of type_expression

and update = update_kind node
and update_kind = Update of { path : name list; value : expression } | Update_error
and binder = Binder_in of pattern * expression | Binder_type of name * type_expression
and else_branch = Else of block | Else_if of expression
and block = { statements : statement list; id : id }
and statement = statement_kind node

and statement_kind =
  | Let of {
      is_var : bool;
      pattern : pattern;
      annotation : type_expression option;
      value : expression;
      else_ : block option;
    }
  | Expression of expression
  | Assignment of { target : expression; operator : assignment; value : expression }
  | For of {
      mode : Language.Loop_mode.t;
      pattern : pattern;
      annotation : type_expression option;
      iterable : expression;
      clauses : loop_clause list;
      body : block;
    }
  | While of { condition : expression; clauses : loop_clause list; body : block }
  | Parallel of block
  | Concurrent of block
  | Proof of block
  | Assert of { value : expression; by : Language.Proof_method.t option }
  | Statement_error

and loop_clause = { kind : loop_clause_kind; condition : condition option; id : id }

and loop_clause_kind =
  | Invariant of expression
  | Loop_decreases of expression list
  | Loop_cost of cost

and arm = { patterns : pattern list; guard : expression option; body : statement; id : id }
and pattern = pattern_kind node

and pattern_kind =
  | Wildcard
  | Binding of name
  | Qualified_constant of constant
  | Literal of literal
  | Pattern_range of { start : range_end; stop : range_end; inclusive : bool }
  | Variant of { name : name; fields : pattern_field list option }
  | Record of pattern_field list
  | Tuple of pattern list
  | Alternatives of pattern list
  | Pattern_error

and constant = Module_constant of path | Type_constant of path * name

and literal =
  | Literal_integer of Z.t
  | Literal_true
  | Literal_false
  | Literal_string of string_literal

and range_end = range_end_kind node
and range_end_kind = End_literal of literal | End_constant of constant
and pattern_field = pattern_field_kind node
and pattern_field_kind = Named_field of name * pattern | Field of pattern | Rest

type visibility = Internal | Public | Public_opaque
type type_head = { path : path; generics : generic_parameter list; id : id }
type definition_name = Plain_name of name | Member_name of type_head * name

type parameter = parameter_kind node

and parameter_kind =
  | Self_parameter of mode option
  | Named_parameter of {
      name : name;
      mode : mode option;
      type_ : type_expression;
      default : expression option;
    }
  | Parameter_error

type result = Returns of type_expression | Lends of mode option * type_expression

type signature = {
  name : definition_name;
  generics : generic_parameter list;
  parameters : parameter list;
  result : result option;
  clauses : clause list;
}

type function_definition = { signature : signature; body : block }

type field = field_kind node

and field_kind =
  | Field_declaration of { name : name; type_ : type_expression; default : expression option }
  | Field_error

type variant = { indirect : bool; name : name; fields : field list option; id : id }
type type_body = Fields of field list | Variants of variant list | Type_todo

type type_clause = type_clause_kind node

and type_clause_kind =
  | Type_invariant of expression
  | Derives of path_type list
  | Potential of expression

type law = { name : name; parameters : parameter list; requires : expression list; body : block }

type trait_member =
  | Associated_type of name * path_type list
  | Associated_capability of name
  | Law of law
  | Trait_member_error

type impl_member =
  | Associated_definition of name * type_expression
  | Capability_definition of name * capability_use list
  | Impl_member_error

type capability_member = Capability_member_error

type intended_kind =
  | Intended_function
  | Intended_constant
  | Intended_type
  | Intended_trait
  | Intended_capability
  | Intended_theorem

type definition_kind =
  | Function of function_definition
  | Method_declaration of signature
  | Type_definition of {
      is_tuple : bool;
      name : name;
      generics : generic_parameter list;
      body : type_body;
      clauses : type_clause list;
    }
  | Trait of {
      name : name;
      generics : generic_parameter list;
      requires : path_type list;
      members : trait_member node list;
    }
  | Impl of {
      trait_ : path_type;
      type_ : type_head;
      uses : capability_reference list;
      members : impl_member node list;
    }
  | Capability of { name : name; members : capability_member node list }
  | Constant of { name : definition_name; type_ : type_expression; value : expression }
  | Test of { name : string_literal; uses : capability_reference list; body : block }
  | Theorem of {
      name : name;
      generics : generic_parameter list;
      parameters : parameter list;
      clauses : clause list;
      body : block;
    }
  | Law_proof of { trait_ : path_type; law : name; type_ : type_head; body : block }
  | Definition_error of { intended : intended_kind option; name : definition_name option }

type definition = { visibility : visibility option; kind : definition_kind; id : id }

type positions = {
  spans : Source.Definition_span.t array;
  syntax_errors : Source.Definition_span.t list;
}

type 'value item = { base : int; stop : int; value : 'value; positions : positions }
type top_level = { definition : definition item; methods : definition item list }
type file = { uses : path item list; definitions : top_level list }
