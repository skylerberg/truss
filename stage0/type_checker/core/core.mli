type id = int
type origin = int
type local = Named of origin | Self | Synthetic of int
type quantifier = Forall | Exists
type evidence = Impl of { impl : Path.t; arguments : Types.substitution } | Bound | Dynamic

type pattern_constant =
  | Boolean_constant of bool
  | Integer_constant of Z.t
  | String_constant of string
  | Named_constant of Path.t

type range_bound = Integer_bound of Z.t | Constant_bound of Path.t

type 'indirect target =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Indirect of 'indirect

type callee = operand target

and call = {
  callee : callee;
  arguments : argument list;
  lends : Types.mode option;
  uses : Types.capability_set;
}

and argument =
  | Passed of { mode : Types.mode; value : operand; mode_keyword : mode_keyword option }
  | Default

and mode_keyword = { written : origin; operand : origin }
and operand = Place of place | Value of expression

and place =
  | Local of { local : local; type_ : Types.ty; origin : origin }
  | Constant of { path : Path.t; type_ : Types.ty; origin : origin }
  | Field of { base : place; field : string; type_ : Types.ty; origin : origin }
  | Lent of expression
  | Temporary of expression

and expression = { id : id; origin : origin; type_ : Types.ty; kind : kind }

and kind =
  | Integer of Z.t
  | Float of float
  | Boolean of bool
  | String of string
  | Template of { literals : string list; call : expression }
  | Use of place
  | Copy of operand
  | Function_value of { path : Path.t; type_arguments : Types.argument list }
  | Value_parameter of Types.parameter
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
  | Slice of { base : place; callee : callee; bounds : argument list }
  | Call of call
  | Operator of { operation : Intrinsic.operation; arguments : expression list }
  | Compare of { comparison : comparison; left : expression; right : expression }
  | Not of expression
  | And of expression * expression
  | Or of expression * expression
  | Implies of expression * expression
  | Matches of { value : operand; pattern : pattern }
  | Convert of { conversion : conversion; value : expression }
  | To_any of { value : expression; trait : Types.trait_reference; evidence : evidence }
  | If of { condition : expression; then_ : block; else_ : block option; binds_lent_part : bool }
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
  | Quantified of { quantifier : quantifier; binder : binder; body : expression }
  | Yielded
  | Identical of expression * expression
  | Specification_function of { function_ : specification_function; arguments : expression list }
  | Method_time of callee

and capture = { local : local; type_ : Types.ty }
and specification_function = Log | Power | Time | Calls
and comparison = Equal | Not_equal | Less | Less_equal | Greater | Greater_equal
and construction = Array | Specification_only
and conversion = Widen | To_integer | From_integer

and binder =
  | Over_type of { local : local; name : string; type_ : Types.ty }
  | Over_range of { pattern : pattern; start : expression; stop : expression; inclusive : bool }
  | Over_elements of { pattern : pattern; elements : elements }

and implementation = {
  origin : origin;
  mode : Types.mode;
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
      clauses : loop_clause list;
      body : block;
      mode : loop_mode;
    }
  | While of {
      condition : expression;
      clauses : loop_clause list;
      body : block;
      binds_lent_part : bool;
    }
  | Parallel of statement list
  | Concurrent of statement list
  | Proof of block
  | Assert of { condition : condition; by_bit_vector : bool }
  | Yield of { mode : Types.mode; part : operand }

and loop_mode = Sequential | Parallel_loop | Concurrent_loop

and iteration =
  | Integer_range of { start : expression; stop : expression; inclusive : bool }
  | Elements of elements
  | Cursor of { cursor : place; next : callee }

and elements = { count : expression; position : pattern; element : place }
and loop_clause = Invariant of expression | Decreases of expression list | Cost of cost
and cost = { origin : origin; amortized : bool; resource : resource; bound : bound }
and resource = Time | Allocations | Allocated_bytes | Calls of calls_target

and calls_target =
  | Function_parameter of local
  | Capability of Path.t
  | Capability_method of Path.t * string

and bound = Finite | Order_of of expression | At_most of expression | Exactly of expression
and condition = { value : expression; executable : bool }
and arm = { patterns : pattern list; guard : expression option; body : block; origin : origin }
and pattern = { id : id; origin : origin; type_ : Types.ty; kind : pattern_kind }

and pattern_kind =
  | Wildcard
  | Bind of { local : local; name : string; is_var : bool; mode : Types.mode }
  | Variant of { variant : string; fields : (string * pattern) list }
  | Record of (string * pattern) list
  | Literal of pattern_constant
  | Range of { start : range_bound; stop : range_bound; inclusive : bool }
  | Equal_to of { value : pattern_constant; equal : callee }
  | Alternatives of pattern list

type parameter = {
  local : local;
  name : string;
  mode : Types.mode;
  type_ : Types.ty;
  default : expression option;
  callback_contract : callback_contract option;
}

and callback_contract = { inputs : (local * string) list; requires : expression list }

type contract = {
  requires : condition list;
  ensures : expression list;
  decreases : expression list;
  costs : cost list;
}

type law = { name : string; parameters : parameter list; requires : expression list; body : block }

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

type t = { definition : definition }
