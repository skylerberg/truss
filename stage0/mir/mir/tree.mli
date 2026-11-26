type local = int

type local_kind =
  | Source of { local : Core.local; mode : Language.Mode.t; is_var : bool; is_binding : bool }
  | Temporary
  | Lent of Language.Mode.t

type local_info = {
  kind : local_kind;
  type_ : Types.ty;
  origin : Core.origin;
  has_several_bindings : bool;
}

type constant = Unit | Integer of Z.t | Float of float | Boolean of bool

type place = { root : root; projections : projection list }

and root =
  | Local of local
  | Constant of Path.t
  | Literal of { value : Language.Literal.t; type_ : Types.ty }

and projection =
  | Field of string
  | Variant_field of { variant : string; field : string }
  | Element of { node : Core.id; index : operand; sequence : Types.ty; origin : Core.origin }
  | Range of {
      node : Core.id;
      start : operand;
      stop : operand option;
      sequence : Types.ty;
      origin : Core.origin;
    }

and operand =
  | Use of { place : place; type_ : Types.ty; origin : Core.origin }
  | Borrow of { place : place; type_ : Types.ty; mode : Language.Mode.t; origin : Core.origin }
  | Take of { place : place; type_ : Types.ty; origin : Core.origin }
  | Immediate of { value : constant; type_ : Types.ty }

type callee = { target : operand Core.target; uses : Types.capability_set }

type function_argument =
  | Function_reference of {
      path : Path.t;
      instantiation : Types.instantiation;
      origin : Core.origin;
    }
  | Lambda_expression of { body : int; origin : Core.origin; type_ : Types.ty }

type argument = { mode : Language.Mode.t; value : operand; function_ : function_argument option }
type call = { callee : callee; arguments : argument list; node : Core.id; origin : Core.origin }
type capture = { local : Core.local; type_ : Types.ty; place : place }

type yielded =
  | Part of operand
  | Built of { variant : string option; fields : (string * yielded option) list; type_ : Types.ty }

type provided = {
  mode : Language.Mode.t;
  value : operand;
  type_ : Types.ty;
  provides : Core.provided list;
  origin : Core.origin;
}

type loan_duration =
  | Loop_body
  | Provide_body
  | Rest_of_statement
  | Operand_evaluation
  | Alias_scope of Core.local

type task = Branch of { fork : Core.id; index : int } | Iteration of { loop : Core.id }

type iteration =
  | Range of { start : operand; stop : operand; inclusive : bool }
  | Pull of { cursor : place; next : callee; next_origin : Core.origin }

type rvalue =
  | Operand of operand
  | Operation of {
      operation : Intrinsic.scalar;
      type_arguments : Types.argument list;
      operands : operand list;
    }
  | Compare of { comparison : Language.Comparison.t; left : operand; right : operand }
  | Not of operand
  | Construct of {
      variant : string option;
      fields : (string * operand option) list;
      type_ : Types.ty;
    }
  | Array of operand list
  | Is_variant of { place : place; variant : string }
  | Convert of {
      conversion : Core.conversion;
      value : operand;
      converts_function_expression : bool;
    }
  | Copy of operand
  | Function_value of { path : Path.t; instantiation : Types.instantiation; is_argument : bool }
  | Lambda of { body : int; captures : capture list; is_argument : bool }
  | Value_parameter of Types.parameter
  | Parameter_default of { definition : Path.t; position : int; substitution : Types.substitution }
  | Specification of specification

and choice =
  | Conditional of { condition : block; then_ : block; else_ : block }
  | Cases of case list
  | Connective of { connective : Language.Connective.t; left : block; right : block }

and specification =
  | Result
  | Entry of local
  | Visited
  | Final_result
  | Identical of operand * operand
  | Applied of {
      function_ : Core.specification_function;
      arguments : operand list;
      unconverted : Types.ty list;
    }
  | Method_cost of { metric : Language.Metric.t; method_ : operand Core.target }
  | Map of (operand * operand) list
  | Quantified of {
      quantifier : Language.Quantifier.t;
      range : quantifier_range;
      parameter : local;
      matches : block;
      body : block;
    }

and case = { tests : block; guard : block option; value : block }

and quantifier_range =
  | Over_type of Types.ty
  | Over_range of { start : operand; stop : operand; inclusive : bool }

and block = { statements : statement list; value : operand option }

and formula = {
  parameters : local list;
  locals : local_info array;
  value : block;
  type_ : Types.ty;
  origin : Core.origin;
  lambdas : body array;
  holds_when : Types.condition;
}

and bound = Order_of of formula | At_most of formula | Exactly of formula

and cost = {
  origin : Core.origin;
  amortized : bool;
  resource : Core.resource;
  bound : bound;
  holds_when : Types.condition;
}

and loop_clause = Invariant of formula | Decreases of formula list | Cost of cost
and quantified = { quantifier : Language.Quantifier.t; decides : local }

and loop = {
  node : Core.id;
  clauses : loop_clause list;
  schedule : Language.Loop_mode.t;
  origin : Core.origin;
  quantified : quantified option;
}

and elements = { element : loop_element; collection : place; count : block }

and loop_element =
  | Lent_by_call of local
  | Sequence_element of { place : place; mode : Language.Mode.t }

and compared = {
  statements : statement list;
  comparison : Language.Comparison.t;
  left : operand;
  right : operand;
}

and early_exit = { resumed : block; returned : local option }
and statement = { kind : statement_kind; origin : Core.origin }

and basic =
  | Assign of { target : place; value : rvalue }
  | Call of { destination : place option; call : call }
  | Lend of { part : local; call : call }
  | Live of local list
  | Dead of local list
  | Assert of operand
  | Echo of operand
  | Loan_start of {
      loan : int;
      borrowed : operand;
      mode : Language.Mode.t;
      duration : loan_duration;
    }
  | Loan_end of int list
  | Ghost_assert of { condition : formula; by_bit_vector : bool }
  | Proof of t
  | Evaluated_assert of t

and statement_kind =
  | Basic of basic
  | Choose of { target : place; choice : choice }
  | Assert_by_bit_vector of { condition : operand; names : local list; code : block }
  | While of {
      loop : loop;
      condition : block;
      body : block;
      failed : statement list;
      compared : compared option;
    }
  | For of {
      loop : loop;
      iteration : iteration;
      part : local;
      elements : elements option;
      bindings : block;
      body : block;
    }
  | Fork of { fork : Core.id; concurrent : bool; branches : block list }
  | Provide of { target : place; provided : provided list; can_use_tasks : bool; body : block }
  | Resume of { winner : local; exits : early_exit list }
  | Yield of { mode : Language.Mode.t; part : yielded }
  | Jump of jump

and jump =
  | Return of operand option
  | Break
  | Continue
  | Cancel of { task : task; winner : local; number : int; returned : (operand * local) option }
  | Unreachable
  | Written_unreachable
  | Todo

and body = {
  parameters : local list;
  captures : local list;
  locals : local_info array;
  code : block;
  is_functional : bool;
  value_type : Types.ty option;
}

and t = { body : body; lambdas : body array }

type 'code field_default = {
  variant : string option;
  field : string;
  type_ : Types.ty;
  value : 'code;
}

type 'code defaults =
  | Parameter_defaults of (int * 'code) list
  | Field_defaults of 'code field_default list

type requirement = {
  clause : formula;
  is_executable : bool;
  names : (Core.local * Core.origin) list;
}

type callback = { inputs : Core.local list; requires : formula list; ensures : formula list }
type parameter = { local : Core.local; mode : Language.Mode.t; type_ : Types.ty }

type contract = {
  parameters : parameter list;
  panics_unless : requirement list;
  requires : requirement list;
  ensures : formula list;
  decreases : formula list;
  costs : cost list;
  callbacks : (int * callback) list;
}

type type_clauses = { invariants : requirement list; potential : formula option }

type law = {
  name : string;
  parameters : (Core.local * Types.ty) list;
  requires : formula list;
  states : formula;
}
