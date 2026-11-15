type in_tree = In_tree
type local = int

type local_kind =
  | Source of { local : Core.local; mode : Types.mode; name : string option; is_var : bool }
  | Temporary
  | Lent of Types.mode

type local_info = {
  kind : local_kind;
  type_ : Types.ty;
  origin : Core.origin;
  has_several_bindings : bool;
}

type place = { root : root; projections : projection list }
and root = Local of local | Constant of Path.t
and projection = Field of string | Variant_field of { variant : string; field : string }

type constant = Unit | Integer of Z.t | Float of float | Boolean of bool | String of string

type operand =
  | Use of { place : place; type_ : Types.ty; node : Core.id; origin : Core.origin }
  | Borrow of { place : place; type_ : Types.ty; mode : Types.mode; origin : Core.origin }
  | Take of { place : place; type_ : Types.ty; origin : Core.origin }
  | Constant of { value : constant; type_ : Types.ty }

type callee = operand Core.target

type function_argument =
  | Function_reference of { path : Path.t; node : Core.id; origin : Core.origin }
  | Lambda_expression of { body : int; node : Core.id; origin : Core.origin; type_ : Types.ty }

type argument =
  | Passed of {
      mode : Types.mode;
      value : operand;
      mode_keyword : Core.mode_keyword option;
      function_ : function_argument option;
    }
  | Default

type call = {
  callee : callee;
  arguments : argument list;
  uses : Types.capability_set;
  node : Core.id;
  origin : Core.origin;
}

type capture = { local : Core.local; type_ : Types.ty; place : place }

type yielded =
  | Part of operand
  | Built of {
      variant : string option;
      fields : (string * yielded option) list;
      type_ : Types.ty;
      node : Core.id;
    }

type provided = {
  mode : Types.mode;
  value : operand;
  type_ : Types.ty;
  provides : Core.provided list;
  origin : Core.origin;
}

type loan_duration = Loop_body | Provide_body | Rest_of_statement | Operand_evaluation
type task = Branch of { block : Core.origin; index : int } | Iteration of { loop : Core.origin }

type iteration =
  | Range of { start : operand; stop : operand; inclusive : bool }
  | Pull of { cursor : place; next : callee }

type connective = And | Or | Implies

type rvalue =
  | Operand of operand
  | Operation of {
      operation : Intrinsic.operation;
      type_arguments : Types.argument list;
      operands : operand list;
    }
  | Compare of { comparison : Core.comparison; left : operand; right : operand }
  | Not of operand
  | Construct of { variant : string option; fields : (string * operand option) list }
  | Array of operand list
  | Is_variant of { place : place; variant : string }
  | Convert of {
      conversion : Core.conversion;
      value : operand;
      converts_function_expression : bool;
    }
  | To_any of { value : operand; trait : Types.trait_reference; evidence : Core.evidence }
  | Copy of operand
  | Function_value of { path : Path.t; type_arguments : Types.argument list; is_argument : bool }
  | Lambda of { body : int; captures : capture list; is_argument : bool }
  | Value_parameter of Types.parameter
  | Conditional of {
      condition : operand;
      then_ : block;
      else_ : block;
      if_condition : Core.origin option;
    }
  | Cases of case list
  | Connective of { connective : connective; left : operand; right : block }
  | Specification of specification

and specification =
  | Result
  | Entry of local
  | Yielded
  | Identical of operand * operand
  | Applied of {
      function_ : Core.specification_function;
      arguments : operand list;
      unconverted : Types.ty list;
    }
  | Method_time of callee
  | Map of (operand * operand) list
  | Quantified of {
      quantifier : Core.quantifier;
      range : quantifier_range;
      parameter : local;
      matches : block;
      body : block;
    }

and case = { tests : block; guard : block option; value : block }

and quantifier_range =
  | Over_type of Types.ty
  | Over_range of { start : operand; stop : operand; inclusive : bool }
  | Over_collection of operand

and block = { statements : statement list; value : operand option }

and formula = {
  parameters : local list;
  locals : local_info array;
  value : block;
  type_ : Types.ty;
  origin : Core.origin;
  lambdas : body array;
}

and bound = Finite | Order_of of formula | At_most of formula | Exactly of formula
and cost = { origin : Core.origin; amortized : bool; resource : Core.resource; bound : bound }
and loop_clause = Invariant of formula | Decreases of formula list | Cost of cost

and quantified = {
  quantifier : Core.quantifier;
  binding_count : int;
  decision : int;
  holds : operand;
  decides : local;
}

and loop = {
  clauses : loop_clause list;
  schedule : Core.loop_mode;
  origin : Core.origin;
  quantified : quantified option;
}

and lent_element = { element : local; collection : place; count : block }
and compared = { comparison : Core.comparison; left : operand; right : operand }
and asserted = { names : local list; code : block }
and early_exit = { resumed : block; returned : local option }
and statement = { kind : in_tree statement_kind; origin : Core.origin }

and _ statement_kind =
  | Assign : { target : place; value : rvalue; node : Core.id option } -> 'form statement_kind
  | Call : { destination : place option; call : call } -> 'form statement_kind
  | Lend : { part : local; call : call } -> 'form statement_kind
  | Slice : { destination : place; base : place; call : call } -> 'form statement_kind
  | Template : { destination : place; literals : string list; call : call } -> 'form statement_kind
  | Live : local list -> 'form statement_kind
  | Dead : local list -> 'form statement_kind
  | Assert : { condition : operand; bit_vector : asserted option } -> 'form statement_kind
  | Echo : operand -> 'form statement_kind
  | Provide : { provided : provided list; can_use_tasks : bool } -> 'form statement_kind
  | Provide_end : 'form statement_kind
  | Loan_start : {
      loan : int;
      borrowed : operand;
      mode : Types.mode;
      duration : loan_duration;
    }
      -> 'form statement_kind
  | Loan_end : int list -> 'form statement_kind
  | Ghost_assert : { condition : formula; by_bit_vector : bool } -> 'form statement_kind
  | Matched : { patterns : Core.origin list } -> 'form statement_kind
  | Proof : t -> 'form statement_kind
  | While : {
      loop : loop;
      condition : block;
      body : block;
      failed : statement list;
      compared : compared option;
    }
      -> in_tree statement_kind
  | For : {
      loop : loop;
      iteration : iteration;
      part : local;
      lent : lent_element option;
      binding_count : int;
      body : block;
    }
      -> in_tree statement_kind
  | Fork : {
      fork : Core.origin;
      concurrent : bool;
      branches : block list;
    }
      -> in_tree statement_kind
  | Resume : { winner : local; exits : early_exit list } -> in_tree statement_kind
  | Yield : { mode : Types.mode; part : yielded } -> in_tree statement_kind
  | Jump : jump -> in_tree statement_kind

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

type callback = { inputs : (Core.local * string) list; requires : formula list }

type parameter = {
  local : Core.local;
  name : string;
  mode : Types.mode;
  type_ : Types.ty;
  has_default : bool;
}

type contract = {
  parameters : parameter list;
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
