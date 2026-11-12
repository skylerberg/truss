(** The syntax tree of one file, shared by every stage after the parser.

    The tree is an abstract syntax tree: it has the program's constructs and each node's span, not
    every token. Each definition records its base, the offset of its first token in the file, and
    every span in its tree is relative to that base, so a definition that only moved has exactly the
    same tree. Every kind of node that can fail to parse has an [Error] case, whose span covers the
    tokens that did not parse.

    Constructs that parse the same are one node, and later stages annotate them without rebuilding
    them: [Bracket] is an index or type arguments, [Name] is a variable, constant, function, type,
    or variant, and a bare name in a pattern is [Binding_or_constant]. *)

module Span = Span

type span = Span.t

type id = int
(** A node's id: a small integer, unique within its definition, assigned in the order the parser
    builds the definition's nodes. Later stages record their results for a node in tables keyed by
    its id, and never rebuild the tree. The same tokens produce the same ids. *)

type name = { text : string; span : span; id : id }

type path = { modules : name list; last : name }
(** [standard::json::parse] has the modules [standard] and [json]. *)

type mode = Mut | Own
type prefix = Negate | Not | Complement

type binary =
  | Multiply
  | Divide
  | Remainder
  | Add
  | Subtract
  | Shift_left
  | Shift_right
  | Bit_and
  | Bit_xor
  | Bit_or
  | Equal
  | Not_equal
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | And
  | Or
  | Implies

type assignment =
  | Assign
  | Add_assign
  | Subtract_assign
  | Multiply_assign
  | Divide_assign
  | Remainder_assign
  | Bit_and_assign
  | Bit_or_assign
  | Bit_xor_assign
  | Shift_left_assign
  | Shift_right_assign

type quantifier = Forall | Exists

type 'kind line = { kind : 'kind; span : span; blank_line_before : bool; id : id }
(** A statement, or a member of a trait, an [impl], or a capability: a node that also records
    whether a blank line came before it, which [truss fmt] keeps. *)

type 'kind node = { kind : 'kind; span : span; id : id }
(** Most of the tree is nodes: a construct's kind, its span, and its id. *)

(** {1 Types} *)

type type_expression = type_kind node

and type_kind =
  | Path_type of path_type
  | Self_type of name option  (** [Self], [Self.Key] *)
  | Associated of name * name  (** [Items.Element] *)
  | Any_type of path_type
  | Function_type of function_type
  | Type_error

and path_type = { path : path; arguments : type_argument list; span : span; id : id }

and type_argument =
  | Type_argument of type_expression
  | Count of Z.t * span  (** [32] in [Array[UInt8, 32]] *)
  | Count_name of name
      (** [count] in [Array[Int64, count]], or a constant, such as [digest_size]; name resolution
          decides *)
  | Constraint of name * type_expression  (** [Element = Int64] *)

and function_type = {
  inputs : (mode option * type_expression) list;
  input_names : name list;  (** Empty, or one for each input. *)
  output : type_expression option;
  clauses : clause list;
}
(** A function type in parentheses can carry [Uses], [Cost], and [Requires] clauses. Its inputs are
    named exactly when it has a [Requires], which names them; the names are not labels, and calls
    stay positional. *)

and generic_parameter = generic_kind node

and generic_kind =
  | Type_parameter of name * path_type list  (** [Element: Hash + Ordered] *)
  | Value_parameter of name * type_expression  (** [count: USize] *)
  | Capability_parameter of name  (** [capability Granted] *)
  | Generic_error

and capability_reference = capability_reference_kind node
(** One member of a [uses] list. *)

and capability_reference_kind =
  | Capability_path of path_type  (** [FileRead], or a capability parameter *)
  | Self_capabilities of name  (** [Self.Uses] *)
  | Associated_capabilities of name * name  (** [Source.Uses] *)

and clause = clause_kind node
(** {1 Clauses} *)

and clause_kind =
  | Uses of capability_reference list
  | Requires of expression
  | Ensures of expression
  | Decreases of expression list
  | Cost of cost
  | Clause_error

and cost = { amortized : bool; resource : resource; bound : bound }
and resource = Time | Allocations | Allocated_bytes | Calls of call_target

and call_target =
  | Call_parameter of name  (** [calls(visit)] *)
  | Call_capability of path_type  (** [calls(FileRead)] *)
  | Call_method of path_type * name  (** [calls(FileRead.read)] *)

and bound = Big_o of expression | Finite | At_most of expression | Exactly of expression

and expression = expression_kind node
(** {1 Expressions} *)

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
  | Name of path  (** [items], [json::parse], [Point], [geometry::Shape] *)
  | Member of expression * name  (** [config.port], [Shape.Circle], [Self.Key] *)
  | Bracket of expression * bracket_item list  (** An index or type arguments *)
  | Call of expression * argument list
  | Try of expression  (** [?] *)
  | With of expression * update list
  | Prefix of prefix * expression
  | Mode of mode * expression
  | Any of expression
  | Binary of { operator : binary; operator_span : span; left : expression; right : expression }
  | Is of { value : expression; operator_span : span; pattern : pattern }
  | Range of {
      start : expression option;
      operator_span : span;
      stop : expression option;
      inclusive : bool;
    }
  | Quantified of { quantifier : quantifier; binder : binder; body : expression }
  | Echo of expression
  | Return of expression option
  | Parenthesized of expression
  | List of expression list
  | Map of (expression * expression) list  (** [[:]] is [Map []] *)
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
  span : span;
  id : id;
}
(** A string literal: its tag, and its texts alternating with its interpolations, starting and
    ending with a text, as in the lexer's token. Its spelling is the source text under its span. *)

and text = { value : string; span : span }
and argument = { label : name option; value : expression }

and bracket_item =
  | Item of expression  (** [0], [String], [..3] *)
  | Item_constraint of name * type_expression  (** [Element = Int64] *)

and update = update_kind node
(** [server.port: 443] updates the field [server] at the path [port]. [with (x)] has no value. *)

and update_kind =
  | Update of { field : name; path : name list; value : expression option }
  | Update_error

and binder =
  | Binder_in of pattern * expression  (** [index in 0..count] *)
  | Binder_type of name * type_expression  (** [value: Int64] *)

and else_branch = Else of block | Else_if of expression
and block = { statements : statement list; span : span; id : id }

and statement = statement_kind line
(** {1 Statements} *)

(** How the iterations of a [for] loop run: one after another, at the same time with no
    capabilities, or each as a task. *)
and loop_mode = Sequential | Parallel_loop | Concurrent_loop

and statement_kind =
  | Let of {
      mutable_ : bool;  (** [var] rather than [let] *)
      pattern : pattern;
      annotation : type_expression option;
      value : expression;
      else_ : block option;
    }
  | Expression of expression
  | Assignment of { target : expression; operator : assignment; value : expression }
  | For of {
      mode : loop_mode;
      pattern : pattern;
      iterable : expression;
      clauses : loop_clause list;
      body : block;
    }
  | While of { condition : expression; clauses : loop_clause list; body : block }
  | Parallel of block
  | Concurrent of block
  | Proof of block
  | Assert of expression
  | Yield of expression
  | Statement_error

and loop_clause = loop_clause_kind node

and loop_clause_kind =
  | Invariant of expression
  | Loop_decreases of expression list
  | Loop_cost of cost  (** What the loop has spent since it started, at each iteration. *)

and arm = {
  patterns : pattern list;
  guard : expression option;
  body : statement;
  span : span;
  blank_line_before : bool;
  id : id;
}

and pattern = pattern_kind node
(** {1 Patterns} *)

and pattern_kind =
  | Wildcard
  | Binding_or_constant of name  (** Name resolution decides. *)
  | Qualified_constant of constant
  | Literal of literal
  | Pattern_range of { start : range_end; stop : range_end; inclusive : bool }
  | Variant of { name : path; fields : pattern_field list option }
      (** [Circle(radius, ..)], [Empty] *)
  | Record of pattern_field list  (** [(index, element)] *)
  | Alternatives of pattern list
  | Pattern_error

(** A qualified constant: [http::ok], or [Status.teapot] under a type. *)
and constant = Module_constant of path | Type_constant of path * name

and literal =
  | Literal_integer of Z.t  (** Including a negated one, [-1] *)
  | Literal_true
  | Literal_false
  | Literal_string of string_literal

and range_end = range_end_kind node
(** A bare name at the end of a range can only be a constant. *)

and range_end_kind = End_literal of literal | End_constant of constant | End_name of name
and pattern_field = pattern_field_kind node

and pattern_field_kind =
  | Named_field of name * pattern  (** [element: score] *)
  | Field of pattern  (** [radius], or a pattern for the only field *)
  | Rest  (** [..] *)

(** {1 Definitions} *)

type visibility =
  | Private
  | Internal
  | Public
  | Public_opaque  (** A type whose fields other packages cannot name. *)
  | Public_transparent
      (** A function whose body the proofs of callers in other packages can read. *)

type type_head = { path : path; generics : generic_parameter list; span : span; id : id }
(** The type a method or constant belongs to: [List[Element: Ordered]] in
    [fn List[Element: Ordered].sort], or [hourly::Forecast]. *)

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

(** A [yields] method yields parts of [self] any number of times, and a [lends] method lends one
    part exactly once. *)
type result =
  | Returns of type_expression
  | Yields of mode option * type_expression
  | Lends of mode option * type_expression

type signature = {
  name : definition_name;
  generics : generic_parameter list;
  parameters : parameter list;
  result : result option;
  clauses : clause list;
}

type function_definition = { signature : signature; body : block }
(** A function with its body. Only a trait or a capability declares a method without one. *)

type field = field_kind node

and field_kind =
  | Field_declaration of { name : name; type_ : type_expression; default : expression option }
  | Field_error

type variant = { indirect : bool; name : name; fields : field list option; span : span; id : id }
type type_body = Fields of field list | Variants of variant list | Type_todo

type type_clause = type_clause_kind node

and type_clause_kind =
  | Type_invariant of expression
  | Derives of path_type list
  | Potential of expression

type law = { name : name; parameters : parameter list; requires : expression list; body : block }

(** The members of a trait, an [impl], or a capability other than its methods. Each method declared
    inside one is a separate definition, which follows it among the file's definitions and records
    it as its container. *)
type trait_member =
  | Associated_type of name * path_type list
  | Associated_capability of name  (** [capability Uses] *)
  | Law of law
  | Trait_member_error

type impl_member =
  | Associated_definition of name * type_expression
  | Capability_definition of name * capability_reference list  (** [capability Uses = FileRead] *)
  | Impl_member_error

type capability_member = Capability_member_error

type definition_kind =
  | Function of function_definition
  | Method_declaration of signature
      (** A method that a trait or a capability declares without a body. *)
  | Type_definition of {
      name : name;
      generics : generic_parameter list;
      body : type_body;
      clauses : type_clause list;
    }
  | Trait of {
      name : name;
      generics : generic_parameter list;
      requires : path_type list;
      members : trait_member line list;
    }
  | Impl of {
      trait_ : path_type;
      type_ : type_head;
      uses : capability_reference list;
      members : impl_member line list;
    }
  | Capability of { name : name; members : capability_member line list }
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
  | Definition_error of { keyword : Token.keyword option; name : definition_name option }
      (** A definition whose header did not parse, with its keyword and its name when those were
          read, so that later stages can still know it is there. *)

type definition = {
  visibility : visibility;
  kind : definition_kind;
  span : span;
  recovered : span list;
  id : id;
}
(** [recovered] lists the spans where the parser recovered from an error in the definition, in
    order. At each one it built a node that does not match the source text: an [Error] node, or the
    node that a habit's fix would produce. A part of the definition matches its source text exactly
    when no recovery lies in its span. *)

type 'value item = {
  base : int;
  text : string;
  blank_line_before : bool;
  value : 'value;
  container : int option;
}
(** An item of a file: a [use] line or a definition, with its base, the absolute offset of its first
    token, and its source text, from its first token to the end of its last. Spans inside [value]
    are relative to [base], and index into [text]. A method written inside a trait, an [impl], or a
    capability is an item of its own, and [container] is the index of that trait, [impl], or
    capability among the file's definitions. *)

type file = { uses : path item list; definitions : definition item list }
