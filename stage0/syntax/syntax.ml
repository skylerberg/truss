(* The syntax tree of one file, shared by every stage after the parser. See
   PARSER.md, "The syntax tree".

   The tree is abstract: it keeps what the program says and each node's span,
   not every token. Each definition records where it starts in the file, its
   base, and every span in its tree is relative to that base, so a definition
   that only moved has exactly the same tree. Every kind of node that can fail
   to parse has an [Error] case, covering the span that did not parse.

   Constructs that parse the same are one node, and later stages annotate
   them without rebuilding them: [Bracket] is an index or type arguments,
   [Name] is a variable, constant, function, type, or variant, and a bare name
   in a pattern is [Binding_or_constant]. *)

(* A span relative to its definition's base: [start] is included and [stop]
   is not. Spans are made only by [Span.make], so [0 <= start <= stop]. *)
module Span : sig
  type t = private { start : int; stop : int }

  val make : int -> int -> t
end = struct
  type t = { start : int; stop : int }

  let make start stop =
    if start < 0 || stop < start then
      invalid_arg (Printf.sprintf "Syntax.Span.make %d %d" start stop);
    { start; stop }
end

type span = Span.t
type name = { text : string; span : span }

(* [standard::json::parse] has the modules [standard] and [json]. *)
type path = { modules : name list; last : name }
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

(* A statement, or a member of a trait, an [impl], or a capability: a node
   that also records whether a blank line came before it, which [truss fmt]
   keeps and hashing ignores. *)
type 'kind line = { kind : 'kind; span : span; blank_line_before : bool }

(* Most of the tree is nodes: what a part of the program is, and its span. *)
type 'kind node = { kind : 'kind; span : span }

(* Types *)

type type_expression = type_kind node

and type_kind =
  | Path_type of path_type
  | Self_type of name option  (** [Self], [Self.Key] *)
  | Associated of name * name  (** [Items.Element] *)
  | Any_type of path_type
  | Function_type of function_type
  | Type_error

and path_type = { path : path; arguments : type_argument list; span : span }

and type_argument =
  | Type_argument of type_expression
  | Count of Z.t * span  (** [32] in [Array[UInt8, 32]] *)
  | Count_parameter of name  (** [count] in [Array[Int64, count]] *)
  | Constraint of name * type_expression  (** [Element = Int64] *)

(* A function type in parentheses can carry [Uses] and [Cost] clauses. *)
and function_type = {
  inputs : (mode option * type_expression) list;
  output : type_expression option;
  clauses : clause list;
}

and generic_parameter = generic_kind node

and generic_kind =
  | Type_parameter of name * path_type list  (** [Element: Hash + Ordered] *)
  | Value_parameter of name * type_expression  (** [count: USize] *)
  | Capability_parameter of name  (** [capability Granted] *)
  | Generic_error

(* Clauses *)
and clause = clause_kind node

and clause_kind =
  | Uses of path_type list
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

(* Expressions *)
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

(* A string literal: its tag, and its texts alternating with its
   interpolations, starting and ending with a text, as the lexer gives them.
   How it was written is the source text under its span. *)
and string_literal = {
  tag : path option;
  first : text;
  rest : (expression * text) list;
  span : span;
}

and text = { value : string; span : span }
and argument = { label : name option; value : expression }

and bracket_item =
  | Item of expression  (** [0], [String], [..3] *)
  | Item_constraint of name * type_expression  (** [Element = Int64] *)

(* [server.port: 443] updates the field [server] at the path [port].
   [with (x)] has no value. *)
and update = update_kind node

and update_kind =
  | Update of { field : name; path : name list; value : expression option }
  | Update_error

and binder =
  | Binder_in of pattern * expression  (** [index in 0..count] *)
  | Binder_type of name * type_expression  (** [value: Int64] *)

and else_branch = Else of block | Else_if of expression
and block = { statements : statement list; span : span }

(* Statements *)
and statement = statement_kind line

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
      parallel : bool;
      pattern : pattern;
      iterable : expression;
      clauses : loop_clause list;
      body : block;
    }
  | While of { condition : expression; clauses : loop_clause list; body : block }
  | Parallel of block
  | Proof of block
  | Assert of expression
  | Yield of expression
  | Statement_error

and loop_clause = loop_clause_kind node
and loop_clause_kind = Invariant of expression | Loop_decreases of expression list

and arm = {
  patterns : pattern list;
  guard : expression option;
  body : statement;
  span : span;
  blank_line_before : bool;
}

(* Patterns *)
and pattern = pattern_kind node

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

(* A qualified constant: [http::ok], or [Status.teapot] under a type. *)
and constant = Module_constant of path | Type_constant of path * name

and literal =
  | Literal_integer of Z.t  (** Including a negated one, [-1] *)
  | Literal_true
  | Literal_false
  | Literal_string of string_literal

(* A bare name at the end of a range can only be a constant. *)
and range_end = range_end_kind node
and range_end_kind = End_literal of literal | End_constant of constant | End_name of name
and pattern_field = pattern_field_kind node

and pattern_field_kind =
  | Named_field of name * pattern  (** [element: score] *)
  | Field of pattern  (** [radius], or a pattern for the only field *)
  | Rest  (** [..] *)

(* Definitions *)

type visibility = Private | Internal | Public | Public_opaque

(* The type a method or constant belongs to: [List[Element: Ordered]] in
   [fn List[Element: Ordered].sort], or [hourly::Forecast]. *)
type type_head = { path : path; generics : generic_parameter list; span : span }
type function_name = Plain_name of name | Method_name of type_head * name

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

type result = Returns of type_expression | Yields of mode option * type_expression

type signature = {
  name : function_name;
  generics : generic_parameter list;
  parameters : parameter list;
  result : result option;
  clauses : clause list;
}

(* A function with its body. Only a trait or a capability declares a method
   without one. *)
type function_definition = { signature : signature; body : block }

type field = field_kind node

and field_kind =
  | Field_declaration of { name : name; type_ : type_expression; default : expression option }
  | Field_error

type variant = { indirect : bool; name : name; fields : field list option; span : span }
type type_body = Fields of field list | Variants of variant list | Type_todo

type type_clause = type_clause_kind node

and type_clause_kind =
  | Type_invariant of expression
  | Derives of path_type list
  | Potential of expression

type law = { name : name; parameters : parameter list; requires : expression list; body : block }

type trait_member =
  | Trait_method of { signature : signature; body : block option }
  | Associated_type of name * path_type list
  | Law of law
  | Trait_member_error

type impl_member =
  | Impl_method of function_definition
  | Associated_definition of name * type_expression
  | Impl_member_error

type capability_member = Capability_method of signature | Capability_member_error

type definition_kind =
  | Function of function_definition
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
      uses : path_type list;
      members : impl_member line list;
    }
  | Capability of { name : name; members : capability_member line list }
  | Constant of { name : function_name; type_ : type_expression; value : expression }
  | Test of { name : string_literal; uses : path_type list; body : block }
  | Theorem of {
      name : name;
      generics : generic_parameter list;
      parameters : parameter list;
      clauses : clause list;
      body : block;
    }
  | Law_proof of { trait_ : path_type; law : name; type_ : type_expression; body : block }
  | Definition_error

type definition = { visibility : visibility; kind : definition_kind; span : span }

(* A top-level item: a [use] line or a definition, with its base, the
   absolute offset of its first token, and its source text, from its first
   token to the end of its last. Spans inside [value] are relative to
   [base], and index into [text]. *)
type 'value item = { base : int; text : string; blank_line_before : bool; value : 'value }
type file = { uses : path item list; definitions : definition item list }
