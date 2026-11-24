type id = int
type desugaring = Rewrite | For_loop | Quantifier | Try | Derived

type origin =
  | Written of Syntax.id
  | Desugared of { construct : Syntax.id; desugaring : desugaring }

type mode_keyword = {
  mode : Language.Mode.t;
  written : Syntax.id;
  operand : Syntax.id;
  place : Syntax.id;
}

type local =
  | Declared of { origin : Syntax.id; name : string }
  | Trait_parameter of { index : int; name : string }
  | Self
  | Synthetic of int

type pattern_constant =
  | Boolean_constant of bool
  | Integer_constant of Z.t
  | String_constant of string
  | Named_constant of Path.t

type range_bound = Integer_bound of Z.t | Constant_bound of Path.t

type 'indirect target =
  | Function of { path : Path.t; instantiation : Types.instantiation }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      instantiation : Types.instantiation;
      evidence : Types.evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Indirect of 'indirect

type callee = { target : operand target; uses : Types.capability_set }

and call = {
  callee : callee;
  arguments : argument list;
  evaluation_order : int list;
  lends : Language.Mode.t option;
}

and argument = { mode : Language.Mode.t; value : operand }
and operand = Place of place | Value of expression

and place =
  | Local of { local : local; type_ : Types.ty; origin : origin }
  | Constant of { path : Path.t; type_ : Types.ty; origin : origin }
  | Field of { base : place; field : string; type_ : Types.ty; origin : origin }
  | Element of { id : id; base : place; index : expression; type_ : Types.ty; origin : origin }
  | Range of {
      id : id;
      base : place;
      start : expression;
      stop : expression option;
      type_ : Types.ty;
      origin : origin;
    }
  | Lent of expression
  | Temporary of expression

and expression = { id : id; origin : origin; type_ : Types.ty; kind : kind }

and kind =
  | Integer of Z.t
  | Float of float
  | Boolean of bool
  | Literal of Language.Literal.t
  | Use of place
  | Copy of operand
  | Function_value of { path : Path.t; instantiation : Types.instantiation }
  | Value_parameter of Types.parameter
  | Parameter_default of { definition : Path.t; position : int; substitution : Types.substitution }
  | Lambda of {
      parameters : pattern list;
      captures : capture list;
      body : block;
      result : Types.ty;
    }
  | Construct of { variant : string option; fields : (string * operand option) list }
  | Collection_literal of { elements : expression list; construction : construction }
  | Map_literal of { entries : (expression * expression) list }
  | Record_update of { base : expression; updates : (string list * expression) list }
  | Call of call
  | Operator of { operation : Intrinsic.scalar; arguments : expression list }
  | Compare of { comparison : Language.Comparison.t; left : expression; right : expression }
  | Not of expression
  | Connective of { connective : Language.Connective.t; left : expression; right : expression }
  | Matches of { value : operand; pattern : pattern }
  | Convert of { conversion : conversion; value : expression }
  | If of { condition : expression; then_ : block; else_ : block option }
  | Match of { scrutinees : operand list; arms : arm list }
  | Block of block
  | Provide of { implementations : implementation list; body : block }
  | Return of expression option
  | Break
  | Continue
  | Todo
  | Unreachable
  | Echo of expression
  | Result
  | Old of expression
  | Current_target
  | Quantified of { quantifier : Language.Quantifier.t; binder : binder; body : expression }
  | Yielded
  | Identical of expression * expression
  | Specification_function of { function_ : specification_function; arguments : expression list }
  | Method_cost of { metric : Language.Metric.t; method_ : operand target }

and capture = { local : local; type_ : Types.ty }

and specification_function =
  | Log
  | Power
  | Callback_cost of Language.Metric.t
  | Callback_ensures
  | Calls

and construction = Array | Specification_only
and conversion = Widen | To_integer | From_integer | View_to_owned

and binder =
  | Over_type of { local : local; type_ : Types.ty }
  | Over_range of { pattern : pattern; start : expression; stop : expression; inclusive : bool }
  | Over_elements of { pattern : pattern; elements : elements }

and implementation = {
  origin : origin;
  mode : Language.Mode.t;
  value : operand;
  type_ : Types.ty;
  provides : provided list;
}

and provided = { capability : Path.t; impl : Path.t; arguments : Types.substitution }
and block = { statements : statement list; value : expression option }
and statement = { id : id; origin : origin; kind : statement_kind }

and statement_kind =
  | Let of { pattern : pattern; value : operand; else_ : block option }
  | Evaluate of expression
  | Assign of { target : place; value : expression }
  | Compound_assign of { target : place; operand : operand; bound : local; value : expression }
  | For of {
      pattern : pattern;
      iteration : iteration;
      clauses : loop_clause conditional list;
      body : block;
      mode : Language.Loop_mode.t;
    }
  | While of { condition : expression; clauses : loop_clause conditional list; body : block }
  | Parallel of statement list
  | Concurrent of statement list
  | Proof of block
  | Assert of { condition : condition; by : Language.Proof_method.t option }
  | Yield of { mode : Language.Mode.t; part : operand }

and iteration =
  | Integer_range of { start : expression; stop : expression; inclusive : bool }
  | Elements of elements
  | Cursor of { cursor : place; next : callee; next_origin : origin }

and elements = { count : expression; position : pattern; element : place; lends : Language.Mode.t }
and loop_clause = Invariant of expression | Decreases of expression list | Cost of cost
and 'clause conditional = { holds_when : Types.condition; clause : 'clause }
and cost = { origin : origin; amortized : bool; resource : resource; bound : bound }
and resource = Metric of Language.Metric.t | Calls of calls_target

and calls_target =
  | Function_parameter of local
  | Capability of Path.t
  | Capability_method of Path.t * string

and bound = Order_of of expression | At_most of expression | Exactly of expression
and condition = { value : expression; executable : bool }
and arm = { patterns : pattern list; guard : expression option; body : block; origin : origin }
and pattern = { id : id; origin : origin; type_ : Types.ty; kind : pattern_kind }

and pattern_kind =
  | Wildcard
  | Bind of { local : local; is_var : bool; mode : Language.Mode.t; may_alias : bool }
  | Variant of { variant : string; fields : (string * pattern) list }
  | Record of (string * pattern) list
  | Literal of pattern_constant
  | Range of { start : range_bound; stop : range_bound; inclusive : bool }
  | Equal_to of { value : pattern_constant; equal : callee }
  | Alternatives of pattern list

type parameter = {
  local : local;
  mode : Language.Mode.t;
  type_ : Types.ty;
  default : expression option;
  callback_contract : callback_contract option;
}

and callback_contract = {
  inputs : local list;
  requires : expression list;
  ensures : expression list;
}

type contract = {
  panics_unless : expression list;
  requires : condition conditional list;
  ensures : expression conditional list;
  decreases : expression conditional list;
  costs : cost conditional list;
}

type law = {
  name : string;
  parameters : parameter list;
  requires : expression list;
  body : block;
  origin : origin;
}

type definition =
  | Function of { parameters : parameter list; contract : contract; body : block option }
  | Type of {
      defaults : (string option * string * expression) list;
      invariants : condition list;
      potential : expression option;
    }
  | Trait of law list
  | Constant of expression option
  | Test of block option
  | Law_proof of { parameters : parameter list; body : block option }
  | Empty

type t = { definition : definition; origin : origin }
