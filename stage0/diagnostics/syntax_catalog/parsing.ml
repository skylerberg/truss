type expected =
  | Token_punctuation of Token.punctuation
  | Token_keyword of Token.keyword
  | Open_paren_after_calls
  | Open_paren_in_function_type
  | Open_paren_in_lambda
  | Open_paren_after_with
  | Type_body_start
  | Parameters_start
  | Function_type_clauses_end
  | Calls_target_end
  | Uses_separator
  | Modifies_separator
  | Self_capability_set
  | Type_arguments_end
  | Capability_member
  | Trait_member
  | Impl_member
  | Potential_word
  | Function_type_clause of Token.keyword
  | Body_start
  | Cost_bound
  | Resource
  | Clause
  | Constant
  | Definition
  | Field_name
  | Parenthesized_function_type
  | Generic_parameter
  | Line_break_after_definition
  | Line_break_after_module_path
  | Line_break_after_statement
  | Line_break_after_method
  | Line_break_or_brace
  | Range_bound
  | Method_name_after_dot
  | Method_name
  | Module_name
  | Name_after_dot
  | Name
  | Number_after_minus
  | Parameter_name
  | Pattern
  | Plain_test_name
  | Test_name
  | Tagged_string
  | Type_name
  | Type
  | Self_associated_capability_set
  | Associated_capability_set
  | Self_associated_type
  | Associated_type
  | Expression
  | Index_or_type_arguments
  | Range_end
  | Capability_parameter_name
  | Constant_name_after_dot
  | Constant_name
  | Law_name
  | Variant_name
  | Associated_capability_set_name
  | Associated_type_name
  | Capability_name
  | Theorem_name
  | Trait_name
  | Defined_type_name
  | Interpolation_end

type cost_word = Potential_cost_word | Resource_word | Bound_word
type loop_exit = Break_exit | Continue_exit
type conversion = Integer_conversion | Library_conversion

type macro =
  | Print_macro
  | Format_macro
  | Vector_macro
  | Assertion_macro
  | Debug_macro
  | Panic_macro
  | Other_macro

type visibility_owner = Test_owner | Law_proof_owner | Impl_owner
type range_part = Range_start | Range_stop
type chain = Range_chain | Comparison_chain | Implication_chain

type problem =
  | Unexpected of { expected : expected; found : Token.kind }
  | Reserved_word of { word : string }
  | Nesting_too_deep of { limit : int }
  | Chain_too_long of { limit : int }
  | Misspelled_cost_word of { category : cost_word; words : string list; found : string }
  | Whole_type_quantifier of { quantifier : string }
  | Implies_in_code
  | Echo_in_specification
  | Try_in_parallel
  | Return_in_parallel
  | Loop_exit_outside_loop of loop_exit
  | Loop_exit_across_lambda of loop_exit
  | Break_in_parallel_for
  | Loop_exit_from_parallel_branch of loop_exit
  | Misplaced_callback_requires
  | Misplaced_callback_ensures
  | Misplaced_proof
  | Misplaced_assert
  | Parameter_named_result
  | Lending_parameter_named_final
  | Associated_type_argument of { written : string; is_law_proof : bool }
  | Function_type_argument of { is_law_proof : bool }
  | Constraint_on_trait of {
      written : string;
      name : string;
      chosen : string option;
      is_law_proof : bool;
    }
  | Function_named_old
  | Function_named_identical
  | Increment of { sign : string; written : string }
  | Double_negation
  | Match_arm_comma
  | Conditional_operator
  | Let_mut
  | Address_of of { is_mut : bool }
  | Closure_bars
  | Brace_record
  | Turbofish
  | Angle_brackets
  | Qualified_variant of { variant : string }
  | Macro_call of { name : string; macro : macro }
  | Keyword_macro
  | Tuple
  | Tuple_field
  | Power_operator
  | Short_declaration
  | Pipe_operator
  | Lambda_annotation
  | Impl_parameters
  | Null_coalescing of { written : string }
  | Trailing_lambda of { parameter : string }
  | As_conversion of { target : string; conversion : conversion }
  | As_float_conversion of { method_ : string }
  | As_unknown_conversion
  | Elif
  | Loop_keyword
  | Constant_keyword of { word : string }
  | Misplaced_visibility of visibility_owner
  | Self_outside_method
  | Self_not_first
  | Self_in_capability
  | Lends_own
  | Repeated_uses
  | Repeated_decreases
  | Repeated_modifies
  | Repeated_loop_decreases
  | Missing_body
  | One_field_tuple
  | Interpolated_test_name
  | Misplaced_opaque
  | Misplaced_tuple_word of { written : string }
  | Statement_at_top_level
  | Empty_type_arguments
  | Function_type_condition
  | Function_type_cost_bound
  | Function_type_needs_names
  | Function_type_extra_names
  | Parenthesized_type
  | Empty_generic_parameters
  | Value_condition_in_when
  | Misplaced_potential
  | Inclusive_range_without_end
  | Open_range_outside_brackets of range_part
  | Open_range_comma
  | Open_range_with_items
  | Update_label
  | Mixed_collection
  | Tuple_pattern_annotation
  | Let_else_brace
  | Amortized_loop_cost
  | Interpolated_pattern
  | Float_pattern
  | Rest_not_last
  | Use_after_definition
  | Lowest_operand
  | Chained of chain
  | Mixed_and_or
  | Unordered_operators
  | Mixed_bitwise
  | Negation_and_is

type action =
  | Write of string
  | Write_conversion of string
  | Write_method of string
  | Remove_it
  | Remove_own
  | Add_todo_body
  | Remove_word of string
  | Remove_comma
  | Next_arm_on_line
  | Write_if
  | Remove_ampersand
  | Write_lambda
  | Use_parentheses
  | Use_square_brackets
  | Remove_qualifier
  | Write_list
  | Remove_macro_call
  | Declare_with_let
  | Write_call
  | Remove_annotation
  | Remove_parameters
  | Call_unwrap_or
  | Pass_lambda
  | Move_use_up
  | Parenthesize_expression
  | Add_parentheses
  | Group_first_two
  | Group_last_two
  | Join_comparisons
  | Negate_test
  | Negate_value

type fix = { action : action; edits : Source.span Diagnostic.edit list }
type t = { at : Source.span; problem : problem; fixes : fix list }

let say text : _ Description.piece list = [ Text text ]

let show_expected = function
  | Token_punctuation punctuation -> Printf.sprintf "`%s`" (Token.spell_punctuation punctuation)
  | Token_keyword keyword -> Printf.sprintf "`%s`" (Token.spell_keyword keyword)
  | Open_paren_after_calls -> "`(` after `calls`"
  | Open_paren_in_function_type -> "`(` after `fn` in a function type"
  | Open_paren_in_lambda -> "`(` after `fn` in a lambda"
  | Open_paren_after_with -> "`(` after `with`"
  | Type_body_start -> "`(` to start the fields, or `=` before the variants"
  | Parameters_start -> "`(` to start the parameters"
  | Function_type_clauses_end -> "`)` after the clauses of the function type"
  | Calls_target_end -> "`)` after the target of `calls`"
  | Modifies_separator -> "`,` or the end of the `modifies` clause, which takes no condition"
  | Uses_separator ->
      "`,` or the end of the `uses` clause; a capability's condition follows `unless`, as in `uses \
       RunForever unless Source: FiniteCursor`"
  | Self_capability_set ->
      "`.` and an associated capability set, as in `Self.Uses`; `Self` is a type, not a capability"
  | Type_arguments_end -> "`>` after the type arguments"
  | Capability_member -> "`fn` to start a method of the capability"
  | Trait_member -> "`fn`, `type`, `capability`, or `law` to start a member of the trait"
  | Impl_member -> "`fn`, `type`, or `capability` to start a member of the `impl`"
  | Potential_word -> "`potential`; a type's only cost clause is `cost potential expression`"
  | Function_type_clause keyword ->
      Printf.sprintf "`uses`, `cost`, `requires`, or `ensures`; a function type has no `%s`"
        (Token.spell_keyword keyword)
  | Body_start -> "`{` to start the body"
  | Cost_bound -> "a bound: `O(...)`, `<=`, or `==`"
  | Resource ->
      Printf.sprintf "a resource: %s, or `calls(...)`"
        (String.concat ", "
           (List.map (fun metric -> "`" ^ Language.Metric.show metric ^ "`") Language.Metric.all))
  | Clause -> "a clause"
  | Constant -> "a constant"
  | Definition ->
      "a definition: `fn`, `type`, `trait`, `impl`, `capability`, `let`, `test`, `theorem`, or \
       `proof`"
  | Field_name -> "a field name"
  | Parenthesized_function_type ->
      "a function type; parentheses in a type only hold a function type with clauses"
  | Generic_parameter -> "a generic parameter"
  | Line_break_after_definition -> "a line break after the definition"
  | Line_break_after_module_path -> "a line break after the module path"
  | Line_break_after_statement -> "a line break after the statement"
  | Line_break_after_method -> "a line break or `}` after the method"
  | Line_break_or_brace -> "a line break or `}`"
  | Range_bound -> "a literal or a constant with its module or type, such as `http.last`"
  | Method_name_after_dot -> "a method name after `.`"
  | Method_name -> "a method name"
  | Module_name -> "a module name"
  | Name_after_dot -> "a name after `.`"
  | Name -> "a name"
  | Number_after_minus -> "a number after `-` in a pattern"
  | Parameter_name -> "a parameter name"
  | Pattern -> "a pattern"
  | Plain_test_name -> "a plain string, with no tag, to name the test"
  | Test_name -> "a string to name the test"
  | Tagged_string -> "a tagged string after its module path"
  | Type_name -> "a type name"
  | Type -> "a type"
  | Self_associated_capability_set -> "an associated capability set after `Self.`"
  | Associated_capability_set -> "an associated capability set"
  | Self_associated_type -> "an associated type after `Self.`"
  | Associated_type -> "an associated type"
  | Expression -> "an expression"
  | Index_or_type_arguments -> "an index or type arguments"
  | Range_end -> "the end of the range; a range pattern needs both ends"
  | Capability_parameter_name -> "the name of a capability parameter"
  | Constant_name_after_dot -> "the name of a constant after `.`"
  | Constant_name -> "the name of a constant"
  | Law_name -> "the name of a law"
  | Variant_name -> "the name of a variant"
  | Associated_capability_set_name -> "the name of an associated capability set"
  | Associated_type_name -> "the name of an associated type"
  | Capability_name -> "the name of the capability"
  | Theorem_name -> "the name of the theorem"
  | Trait_name -> "the name of the trait"
  | Defined_type_name -> "the name of the type"
  | Interpolation_end -> "the end of the interpolation"

let describe_token (kind : Token.kind) =
  match kind with
  | Newline -> "a line break"
  | End_of_file -> "the end of the definition"
  | Upper name | Lower name -> Printf.sprintf "the name `%s`" name
  | Underscore -> "`_`"
  | Keyword keyword -> Printf.sprintf "`%s`" (Token.spell_keyword keyword)
  | Reserved reserved -> Printf.sprintf "`%s`" (Token.spell_reserved reserved)
  | Integer _ | Float _ -> "a number"
  | String _ -> "a string"
  | Punctuation punctuation -> Printf.sprintf "`%s`" (Token.spell_punctuation punctuation)
  | Foreign foreign -> Printf.sprintf "`%s`" (Token.spell_foreign foreign)

let show_loop_exit = function Break_exit -> "break" | Continue_exit -> "continue"

let show_macro_advice = function
  | Print_macro ->
      " Print with `Console.print_line(text)`, and build the text with `${...}` in a string."
  | Format_macro -> " Build text with `${...}` in a string."
  | Vector_macro -> " A list is written `[first, second]`."
  | Assertion_macro ->
      " An assertion is a statement, `assert condition`, in a test, a theorem, or a proof."
  | Debug_macro -> " `echo value` prints a value while debugging."
  | Panic_macro -> " Code that cannot be reached is `unreachable`, and a failure is a `Result`."
  | Other_macro -> ""

let find_code : problem -> Diagnostic.Code.parser = function
  | Unexpected _ -> Unexpected_token
  | Reserved_word _ | Loop_keyword | Constant_keyword _ -> Reserved_word
  | Nesting_too_deep _ | Chain_too_long _ -> Nesting_too_deep
  | Misspelled_cost_word _ -> Cost_word
  | Whole_type_quantifier _ | Implies_in_code -> Specification_only
  | Echo_in_specification -> Echo_in_specification
  | Try_in_parallel | Return_in_parallel | Break_in_parallel_for | Loop_exit_from_parallel_branch _
    ->
      Exits_parallel
  | Loop_exit_outside_loop _ | Loop_exit_across_lambda _ -> Misplaced_loop_exit
  | Misplaced_callback_requires | Misplaced_callback_ensures -> Misplaced_callback_contract
  | Misplaced_proof -> Misplaced_proof
  | Misplaced_assert -> Misplaced_assert
  | Parameter_named_result | Lending_parameter_named_final | Function_named_old
  | Function_named_identical ->
      Reserved_specification_name
  | Associated_type_argument _ -> Misplaced_associated_type
  | Function_type_argument _ -> Misplaced_function_type
  | Constraint_on_trait _ -> Misplaced_constraint
  | Increment _ -> Increment
  | Double_negation -> Double_negation
  | Match_arm_comma -> Match_arm_comma
  | Conditional_operator -> Conditional_operator
  | Let_mut -> Let_mut
  | Address_of _ -> Address_of
  | Closure_bars -> Closure_bars
  | Brace_record -> Brace_record
  | Turbofish -> Turbofish
  | Angle_brackets -> Angle_brackets
  | Qualified_variant _ -> Qualified_variant
  | Macro_call _ | Keyword_macro -> Macro_call
  | Tuple | Tuple_field -> Tuple
  | Power_operator -> Power_operator
  | Short_declaration -> Short_declaration
  | Pipe_operator -> Pipe_operator
  | Lambda_annotation -> Lambda_annotation
  | Impl_parameters -> Impl_parameters
  | Null_coalescing _ -> Null_coalescing
  | Trailing_lambda _ -> Trailing_lambda
  | As_conversion _ | As_float_conversion _ | As_unknown_conversion -> As_conversion
  | Elif -> Elif
  | Misplaced_visibility _ -> Misplaced_visibility
  | Self_outside_method | Self_not_first | Self_in_capability -> Misplaced_self
  | Lends_own -> Lends_own
  | Repeated_uses | Repeated_decreases | Repeated_modifies | Repeated_loop_decreases ->
      Repeated_clause
  | Missing_body -> Missing_body
  | One_field_tuple | Misplaced_tuple_word _ -> Misplaced_tuple
  | Interpolated_test_name | Interpolated_pattern -> Interpolation_not_allowed
  | Misplaced_opaque -> Misplaced_opaque
  | Statement_at_top_level -> Statement_at_top_level
  | Empty_type_arguments | Parenthesized_type | Empty_generic_parameters | Update_label
  | Mixed_collection | Tuple_pattern_annotation | Rest_not_last ->
      Unexpected_token
  | Function_type_condition | Value_condition_in_when -> Misplaced_condition
  | Function_type_cost_bound -> Function_type_cost_bound
  | Function_type_needs_names | Function_type_extra_names -> Function_type_names
  | Misplaced_potential -> Misplaced_potential
  | Inclusive_range_without_end | Open_range_outside_brackets _ | Open_range_comma
  | Open_range_with_items ->
      Open_range
  | Let_else_brace -> Let_else_brace
  | Amortized_loop_cost -> Loop_cost_bound
  | Float_pattern -> Float_pattern
  | Use_after_definition -> Use_after_definition
  | Lowest_operand | Chained _ | Mixed_and_or | Unordered_operators | Mixed_bitwise
  | Negation_and_is ->
      Needs_parentheses

let describe_problem = function
  | Unexpected { expected; found } ->
      Printf.sprintf "Expected %s, found %s." (show_expected expected) (describe_token found)
  | Reserved_word { word } ->
      Printf.sprintf "`%s` is reserved for possible later use, and means nothing in Truss yet." word
  | Nesting_too_deep { limit } -> Printf.sprintf "This is nested more than %d levels deep." limit
  | Chain_too_long { limit } ->
      Printf.sprintf
        "This chains more than %d operations, each of which nests one level deeper. Give parts of \
         it names with `let`."
        limit
  | Misspelled_cost_word { category; words; found } ->
      Printf.sprintf "Expected %s, one of %s, found `%s`."
        (match category with
        | Potential_cost_word -> show_expected Potential_word
        | Resource_word -> "a resource"
        | Bound_word -> "a bound")
        (String.concat ", " (List.map (fun word -> "`" ^ word ^ "`") words))
        found
  | Whole_type_quantifier { quantifier } ->
      Printf.sprintf
        "`%s` over a whole type cannot run, so it is only for specifications and the bodies of \
         functions for specifications only. Quantify over a range or a collection, as in `%s i in \
         0..count => ...`."
        quantifier quantifier
  | Implies_in_code ->
      "`==>` is only for specifications and the bodies of functions for specifications only; in \
       code, write `!a || b`."
  | Echo_in_specification -> "`echo` is not allowed in specifications, which never run."
  | Try_in_parallel ->
      "`?` cannot exit a `parallel` block or a `parallel for`; return a `Result` from the branch \
       and use `?` after it."
  | Return_in_parallel -> "`return` cannot exit a `parallel` block or a `parallel for`."
  | Loop_exit_outside_loop word ->
      Printf.sprintf "`%s` is only allowed in a loop." (show_loop_exit word)
  | Loop_exit_across_lambda word ->
      Printf.sprintf "`%s` cannot reach a loop outside the lambda it is in." (show_loop_exit word)
  | Break_in_parallel_for -> "`break` cannot exit a `parallel for`; `continue` can."
  | Loop_exit_from_parallel_branch word ->
      Printf.sprintf "`%s` cannot leave a branch of a `parallel` block." (show_loop_exit word)
  | Misplaced_callback_requires ->
      "A function type has a `requires` only as the type of a parameter, where it constrains the \
       arguments the callee passes its callback."
  | Misplaced_callback_ensures ->
      "A function type has an `ensures` only as the type of a parameter, where it constrains the \
       results the callback returns to the callee."
  | Misplaced_proof -> "A `proof` block is only allowed in a function's body."
  | Misplaced_assert -> "`assert` is only allowed in tests, theorems, and proofs."
  | Parameter_named_result ->
      "A parameter cannot be named `result`, which names the return value in `ensures` and `cost`."
  | Lending_parameter_named_final ->
      "A parameter of a lending method cannot be named `final`: in the method's `ensures`, \
       `final(result)` is the part as the caller left it."
  | Associated_type_argument { written; is_law_proof = true } ->
      Printf.sprintf "`%s` cannot be a trait argument of a law proof, since no `impl` can have one."
        written
  | Associated_type_argument { written; is_law_proof = false } ->
      Printf.sprintf
        "`%s` cannot be a trait argument of an `impl`: an associated type may stand for any type, \
         so the `impl` could overlap every other `impl` of the trait for its type."
        written
  | Function_type_argument { is_law_proof = true } ->
      "A function type cannot be a trait argument of a law proof, since no `impl` can have one."
  | Function_type_argument { is_law_proof = false } ->
      "A function type cannot be a trait argument of an `impl`. Use a record that holds the \
       function, such as `type Callback(run: fn(Int64) -> Int64)`, as the argument."
  | Constraint_on_trait { written; name; is_law_proof = true; _ } ->
      Printf.sprintf
        "A law proof's trait takes no constraint such as `%s`: the `impl` it proves chooses `%s` \
         in its body."
        written name
  | Constraint_on_trait { written; name; chosen; is_law_proof = false } ->
      Printf.sprintf
        "An `impl` chooses its associated types in its body, so `%s` on its trait would have no \
         effect. Write `type %s = %s` in the `impl` instead."
        written name
        (Option.value ~default:"..." chosen)
  | Function_named_old ->
      "A function cannot be named `old`, which names a value as it was when a function was called, \
       in specifications."
  | Function_named_identical ->
      "A function cannot be named `identical`, which tests whether two values are the same value, \
       in specifications."
  | Increment { sign; written } ->
      Printf.sprintf "Truss has no `%s%s`; write `%s`." sign sign written
  | Double_negation -> "Truss has no `--`; to negate twice, write `-(-x)`."
  | Match_arm_comma -> "`match` arms are separated by line breaks, not commas."
  | Conditional_operator -> "Truss has no conditional operator; write `if x { a } else { b }`."
  | Let_mut -> "A mutable variable is declared with `var`, not `let mut`."
  | Address_of { is_mut } ->
      Printf.sprintf
        "Truss has no `&`; write %s, with `mut` or `own` before a place only when it is mutated or \
         moved."
        (if is_mut then "`mut x`" else "`x`")
  | Closure_bars -> "A lambda is written `fn(x) { x + 1 }`."
  | Brace_record -> "Records are built with parentheses: `Point(x: 1.0, y: 2.0)`."
  | Turbofish -> "Type arguments go in square brackets: `parse[Int64](text)`."
  | Angle_brackets ->
      "Type arguments and generic parameters go in square brackets: `List[String]`, `fn \
       first[Element](...)`."
  | Qualified_variant { variant } ->
      Printf.sprintf
        "A pattern names a variant alone: `%s`. The type of the scrutinee says which type's \
         variant it is."
        variant
  | Macro_call { name; macro } ->
      Printf.sprintf "Truss has no macros, so `%s!` is not a call.%s" name (show_macro_advice macro)
  | Keyword_macro -> "Truss has no macros. `todo` and `unreachable` are written without `!()`."
  | Tuple ->
      "Parentheses do not make a tuple: every tuple type has a name and named fields. Values that \
       belong together go in a record or a tuple type, such as `core.Pair`, built as \
       `core.Pair(first: a, second: b)`."
  | Tuple_field ->
      "A value has no numbered fields. Every field has a name, in a tuple type too, as in \
       `pair.first`."
  | Power_operator ->
      "Truss has no power operator. Multiply, as in `x * x`, or call the type's own method for a \
       power."
  | Short_declaration -> "Truss has no `:=`. A new name is declared with `let name = value`."
  | Pipe_operator -> "Truss has no `|>`. A function is called with its argument: `function(value)`."
  | Lambda_annotation ->
      "A lambda's parameters and result have no annotations. Their types are inferred from where \
       the lambda is passed."
  | Impl_parameters ->
      "An `impl` has no parameters of its own. The type after `for` declares them, with their \
       bounds: `impl Trait for Box[Item: Ordered]`."
  | Null_coalescing { written } ->
      Printf.sprintf
        "Truss has no `%s`. An `Option`'s value, or a default when it has none, is \
         `option.unwrap_or(default)`."
        written
  | Trailing_lambda { parameter } ->
      Printf.sprintf
        "A lambda is passed inside the parentheses, with a named parameter: `fn(%s) { ... }`."
        parameter
  | As_conversion { target; conversion } ->
      let checked, fallible =
        match conversion with
        | Integer_conversion -> ("from_integer", "try_from_integer")
        | Library_conversion -> ("from", "try_from")
      in
      Printf.sprintf
        "Truss has no `as`; write `%s.%s(x)`, or `%s.%s(x)` when the value may not fit." target
        checked target fallible
  | As_float_conversion { method_ } -> Printf.sprintf "Truss has no `as`; write `x.%s()`." method_
  | As_unknown_conversion ->
      "Truss has no `as`; call a conversion of the target type, such as `from_integer` or \
       `try_from_integer` for an integer, or `from` or `try_from` for a library type."
  | Elif -> "Truss writes `else if`, not `elif`."
  | Loop_keyword -> "Truss has no `loop`; write `while true`."
  | Constant_keyword { word } ->
      Printf.sprintf "Truss has no `%s`; a constant is a `let` at the top level." word
  | Misplaced_visibility Test_owner -> "A test takes no visibility: nothing refers to it by name."
  | Misplaced_visibility Law_proof_owner ->
      "A law's proof takes no visibility: nothing refers to it by name."
  | Misplaced_visibility Impl_owner ->
      "An `impl` takes no visibility: it applies wherever its trait and the types it names are \
       visible."
  | Self_outside_method ->
      "Only a method takes `self`: one written `fn Type.name`, or one in a trait or an `impl`."
  | Self_not_first -> "`self` must be the first parameter."
  | Self_in_capability ->
      "A capability's methods take no `self`; they are called as `Capability.method(...)`, and \
       only an implementation's methods take `self`."
  | Lends_own ->
      "A part a `lends` method lends stays with `self`, so it cannot be `own`. A method that hands \
       over an owned value returns it with `->`."
  | Repeated_uses ->
      "A signature has at most one `uses` clause; list every capability in one, separated by \
       commas."
  | Repeated_decreases ->
      "A signature has at most one `decreases` clause; list several measures in one, separated by \
       commas."
  | Repeated_modifies ->
      "A signature has at most one `modifies` clause; list every part that the function changes in \
       one, separated by commas."
  | Repeated_loop_decreases ->
      "A loop has at most one `decreases` clause; list several measures in one, separated by \
       commas."
  | Missing_body -> "A function needs a body; write `{ todo }` for one that is not written yet."
  | One_field_tuple ->
      "Only a record with two or more fields can be a tuple type. A record with one field already \
       takes a bare pattern, and a sum type's fields belong to its variants."
  | Interpolated_test_name -> "A test's name cannot have interpolations."
  | Misplaced_opaque -> "Only a type can be `opaque`."
  | Misplaced_tuple_word { written } ->
      Printf.sprintf "Only `tuple` can come before `type`, not `%s`." written
  | Statement_at_top_level ->
      "Statements must be inside a function, a test, or another definition with a body."
  | Empty_type_arguments -> "Type arguments cannot be empty."
  | Function_type_condition ->
      "A function type's clauses take no condition: a call through a function value has no type \
       arguments to decide one."
  | Function_type_cost_bound ->
      "An `O(...)`, `<=`, or `==` bound in a function type is an integer literal, as in `O(1)` or \
       `<= 2`, since the type holds a number and not an expression. State a bound that depends on \
       a value in the enclosing function's own `cost` clause, which names the callback's cost as \
       `time(visit)`."
  | Function_type_needs_names ->
      "A function type with `requires` or `ensures` names every input, as in `fn(index: UInt64)`, \
       so that its clauses can mention them."
  | Function_type_extra_names ->
      "A function type names its inputs only when a `requires` or an `ensures` mentions them; \
       remove the names, since calls through a function value pass arguments by position."
  | Parenthesized_type ->
      "Parentheses around a function type are only for its clauses; remove them."
  | Empty_generic_parameters -> "Generic parameters cannot be empty."
  | Value_condition_in_when ->
      "A `when` condition names bounds, such as `T: Trait`. A clause that holds where a value \
       condition does is written with `==>`, as in `ensures P ==> Q`."
  | Misplaced_potential ->
      "`cost potential` belongs to a type, and states the potential its values hold."
  | Inclusive_range_without_end ->
      "A range that includes its end needs the end, as in `items[2..=4]`."
  | Open_range_outside_brackets part ->
      let part = match part with Range_start -> "start" | Range_stop -> "end" in
      Printf.sprintf
        "A range without a%s %s is only allowed directly in brackets, as in `items[2..]`."
        (if part = "end" then "n" else "")
        part
  | Open_range_comma ->
      "A range without a start or an end has no comma after it, as in `items[2..]`."
  | Open_range_with_items ->
      "A range without a start or an end must be the only item in its brackets, as in `items[2..]`."
  | Update_label -> "The label of an update is a field or a path of fields, such as `server.port`."
  | Mixed_collection ->
      "A collection holds either list elements or map entries, `key: value`, not both."
  | Tuple_pattern_annotation ->
      "A tuple pattern takes no type annotation: the value's tuple type gives each pattern the \
       type of its field."
  | Let_else_brace ->
      "The expression before the `else` of a `let ... else` cannot end with `}`; put it in \
       parentheses."
  | Amortized_loop_cost ->
      "A loop's `cost` bounds the loop's cost so far, so it is never `amortized`. Potential \
       belongs to the values the loop mutates, which the function's own `cost` accounts for."
  | Interpolated_pattern -> "A string in a pattern cannot have interpolations."
  | Float_pattern ->
      "A float literal cannot be a pattern, since `==` on floats treats `-0.0` and `0.0` as equal; \
       match with a guard instead, as in `value if value == 0.0`."
  | Rest_not_last -> "`..` must be the last field of a pattern."
  | Use_after_definition -> "`use` lines come before every definition in a file."
  | Lowest_operand ->
      "This takes everything after it, so as an operand it must be in parentheses, except that \
       `forall` and `exists` may be the last operand of `&&`, `||`, or `==>`."
  | Chained Range_chain -> "Ranges do not chain."
  | Chained Comparison_chain -> "Comparisons do not chain."
  | Chained Implication_chain -> "`==>` does not chain."
  | Mixed_and_or -> "`&&` and `||` cannot be mixed without parentheses."
  | Unordered_operators -> "These operators need parentheses to say which applies first."
  | Mixed_bitwise -> "Shifts and bitwise operators combine only with themselves; add parentheses."
  | Negation_and_is ->
      "`!` and `is` have no relative precedence. Add parentheses to say whether the test or the \
       value is negated."

let describe_action = function
  | Write code -> Printf.sprintf "Write `%s`" code
  | Write_conversion code -> Printf.sprintf "Write `%s(...)`" code
  | Write_method method_ -> Printf.sprintf "Write `.%s()`" method_
  | Remove_it -> "Remove it"
  | Remove_own -> "Remove `own`"
  | Add_todo_body -> "Add `{ todo }`"
  | Remove_word word -> Printf.sprintf "Remove `%s`" word
  | Remove_comma -> "Remove the comma"
  | Next_arm_on_line -> "Put the next arm on its own line"
  | Write_if -> "Write an `if` expression"
  | Remove_ampersand -> "Remove the `&`"
  | Write_lambda -> "Write `fn(...) { ... }`"
  | Use_parentheses -> "Use parentheses"
  | Use_square_brackets -> "Use square brackets"
  | Remove_qualifier -> "Remove the qualifier"
  | Write_list -> "Write a list"
  | Remove_macro_call -> "Remove `!()`"
  | Declare_with_let -> "Declare the name with `let`"
  | Write_call -> "Write the call"
  | Remove_annotation -> "Remove the annotation"
  | Remove_parameters -> "Remove the parameters"
  | Call_unwrap_or -> "Call `unwrap_or`"
  | Pass_lambda -> "Pass a lambda"
  | Move_use_up -> "Move it up to the other `use` lines"
  | Parenthesize_expression -> "Put the expression in parentheses"
  | Add_parentheses -> "Add parentheses"
  | Group_first_two -> "Group the first two operands"
  | Group_last_two -> "Group the last two operands"
  | Join_comparisons -> "Join the comparisons with `&&`"
  | Negate_test -> "Negate the test"
  | Negate_value -> "Negate the value"

let describe ({ at; problem; fixes } : t) : Source.span Description.t =
  {
    code = Parser (find_code problem);
    severity = Error;
    location = At at;
    message = say (describe_problem problem);
    notes = [];
    fixes =
      List.map
        (fun ({ action; edits } : fix) : Source.span Description.fix ->
          {
            title = say (describe_action action);
            edits =
              List.map
                (fun (edit : Source.span Diagnostic.edit) ->
                  Description.Replace (edit.span, [ Text edit.replacement ]))
                edits;
          })
        fixes;
  }

let render diagnostic = Description.render_spans (describe diagnostic)

let examples : t list =
  [
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected { expected = Token_punctuation Token.Comma; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Token_keyword Token.Fn; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_after_calls; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_in_function_type; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_in_lambda; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_after_with; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_body_start; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parameters_start; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Function_type_clauses_end; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Calls_target_end; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Uses_separator; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Self_capability_set; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_arguments_end; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_member; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Trait_member; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Impl_member; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Potential_word; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected
          { expected = Function_type_clause Token.Decreases; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Body_start; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Cost_bound; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Resource; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Clause; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Definition; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Field_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parenthesized_function_type; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Generic_parameter; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_definition; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected { expected = Line_break_after_module_path; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_statement; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_method; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_or_brace; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Range_bound; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Method_name_after_dot; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Method_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Module_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Name_after_dot; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Number_after_minus; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parameter_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Pattern; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Plain_test_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Test_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Tagged_string; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected { expected = Self_associated_capability_set; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_capability_set; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Self_associated_type; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_type; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Expression; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Index_or_type_arguments; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Range_end; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_parameter_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant_name_after_dot; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Law_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Variant_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected { expected = Associated_capability_set_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_type_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Theorem_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Trait_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Defined_type_name; found = Token.Lower "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Interpolation_end; found = Token.Lower "‹found›" };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Reserved_word { word = "‹word›" }; fixes = [] };
    { at = Source.make_span 0 1; problem = Nesting_too_deep { limit = 64 }; fixes = [] };
    { at = Source.make_span 0 1; problem = Chain_too_long { limit = 64 }; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem =
        Misspelled_cost_word
          { category = Potential_cost_word; words = [ "‹words›" ]; found = "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Misspelled_cost_word { category = Resource_word; words = [ "‹words›" ]; found = "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Misspelled_cost_word { category = Bound_word; words = [ "‹words›" ]; found = "‹found›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Whole_type_quantifier { quantifier = "‹quantifier›" };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Implies_in_code; fixes = [] };
    { at = Source.make_span 0 1; problem = Echo_in_specification; fixes = [] };
    { at = Source.make_span 0 1; problem = Try_in_parallel; fixes = [] };
    { at = Source.make_span 0 1; problem = Return_in_parallel; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_exit_outside_loop Break_exit; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_exit_outside_loop Continue_exit; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_exit_across_lambda Break_exit; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_exit_across_lambda Continue_exit; fixes = [] };
    { at = Source.make_span 0 1; problem = Break_in_parallel_for; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_exit_from_parallel_branch Break_exit; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Loop_exit_from_parallel_branch Continue_exit;
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Misplaced_callback_requires; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_callback_ensures; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_proof; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_assert; fixes = [] };
    { at = Source.make_span 0 1; problem = Parameter_named_result; fixes = [] };
    { at = Source.make_span 0 1; problem = Lending_parameter_named_final; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Associated_type_argument { written = "‹written›"; is_law_proof = false };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Associated_type_argument { written = "‹written›"; is_law_proof = true };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Function_type_argument { is_law_proof = false };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Function_type_argument { is_law_proof = true };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Constraint_on_trait
          { written = "‹written›"; name = "‹name›"; chosen = Some "‹chosen›"; is_law_proof = false };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Constraint_on_trait
          { written = "‹written›"; name = "‹name›"; chosen = None; is_law_proof = false };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Constraint_on_trait
          { written = "‹written›"; name = "‹name›"; chosen = Some "‹chosen›"; is_law_proof = true };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Function_named_old; fixes = [] };
    { at = Source.make_span 0 1; problem = Function_named_identical; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Increment { sign = "‹sign›"; written = "‹written›" };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Double_negation; fixes = [] };
    { at = Source.make_span 0 1; problem = Match_arm_comma; fixes = [] };
    { at = Source.make_span 0 1; problem = Conditional_operator; fixes = [] };
    { at = Source.make_span 0 1; problem = Let_mut; fixes = [] };
    { at = Source.make_span 0 1; problem = Address_of { is_mut = false }; fixes = [] };
    { at = Source.make_span 0 1; problem = Address_of { is_mut = true }; fixes = [] };
    { at = Source.make_span 0 1; problem = Closure_bars; fixes = [] };
    { at = Source.make_span 0 1; problem = Brace_record; fixes = [] };
    { at = Source.make_span 0 1; problem = Turbofish; fixes = [] };
    { at = Source.make_span 0 1; problem = Angle_brackets; fixes = [] };
    { at = Source.make_span 0 1; problem = Qualified_variant { variant = "‹variant›" }; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Print_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Format_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Vector_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Assertion_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Debug_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Panic_macro };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Macro_call { name = "‹name›"; macro = Other_macro };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Keyword_macro; fixes = [] };
    { at = Source.make_span 0 1; problem = Tuple; fixes = [] };
    { at = Source.make_span 0 1; problem = Tuple_field; fixes = [] };
    { at = Source.make_span 0 1; problem = Power_operator; fixes = [] };
    { at = Source.make_span 0 1; problem = Short_declaration; fixes = [] };
    { at = Source.make_span 0 1; problem = Pipe_operator; fixes = [] };
    { at = Source.make_span 0 1; problem = Lambda_annotation; fixes = [] };
    { at = Source.make_span 0 1; problem = Impl_parameters; fixes = [] };
    { at = Source.make_span 0 1; problem = Null_coalescing { written = "‹written›" }; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Trailing_lambda { parameter = "‹parameter›" };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = As_conversion { target = "‹target›"; conversion = Integer_conversion };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = As_conversion { target = "‹target›"; conversion = Library_conversion };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = As_float_conversion { method_ = "‹method_›" };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = As_unknown_conversion; fixes = [] };
    { at = Source.make_span 0 1; problem = Elif; fixes = [] };
    { at = Source.make_span 0 1; problem = Loop_keyword; fixes = [] };
    { at = Source.make_span 0 1; problem = Constant_keyword { word = "‹word›" }; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_visibility Test_owner; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_visibility Law_proof_owner; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_visibility Impl_owner; fixes = [] };
    { at = Source.make_span 0 1; problem = Self_outside_method; fixes = [] };
    { at = Source.make_span 0 1; problem = Self_not_first; fixes = [] };
    { at = Source.make_span 0 1; problem = Self_in_capability; fixes = [] };
    { at = Source.make_span 0 1; problem = Lends_own; fixes = [] };
    { at = Source.make_span 0 1; problem = Repeated_uses; fixes = [] };
    { at = Source.make_span 0 1; problem = Repeated_decreases; fixes = [] };
    { at = Source.make_span 0 1; problem = Repeated_modifies; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Function_type_clause Token.Modifies; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Modifies_separator; found = Token.Keyword Token.When };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Repeated_loop_decreases; fixes = [] };
    { at = Source.make_span 0 1; problem = Missing_body; fixes = [] };
    { at = Source.make_span 0 1; problem = One_field_tuple; fixes = [] };
    { at = Source.make_span 0 1; problem = Interpolated_test_name; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_opaque; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Misplaced_tuple_word { written = "‹written›" };
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Statement_at_top_level; fixes = [] };
    { at = Source.make_span 0 1; problem = Empty_type_arguments; fixes = [] };
    { at = Source.make_span 0 1; problem = Function_type_condition; fixes = [] };
    { at = Source.make_span 0 1; problem = Function_type_cost_bound; fixes = [] };
    { at = Source.make_span 0 1; problem = Function_type_needs_names; fixes = [] };
    { at = Source.make_span 0 1; problem = Function_type_extra_names; fixes = [] };
    { at = Source.make_span 0 1; problem = Parenthesized_type; fixes = [] };
    { at = Source.make_span 0 1; problem = Empty_generic_parameters; fixes = [] };
    { at = Source.make_span 0 1; problem = Value_condition_in_when; fixes = [] };
    { at = Source.make_span 0 1; problem = Misplaced_potential; fixes = [] };
    { at = Source.make_span 0 1; problem = Inclusive_range_without_end; fixes = [] };
    { at = Source.make_span 0 1; problem = Open_range_outside_brackets Range_start; fixes = [] };
    { at = Source.make_span 0 1; problem = Open_range_outside_brackets Range_stop; fixes = [] };
    { at = Source.make_span 0 1; problem = Open_range_comma; fixes = [] };
    { at = Source.make_span 0 1; problem = Open_range_with_items; fixes = [] };
    { at = Source.make_span 0 1; problem = Update_label; fixes = [] };
    { at = Source.make_span 0 1; problem = Mixed_collection; fixes = [] };
    { at = Source.make_span 0 1; problem = Tuple_pattern_annotation; fixes = [] };
    { at = Source.make_span 0 1; problem = Let_else_brace; fixes = [] };
    { at = Source.make_span 0 1; problem = Amortized_loop_cost; fixes = [] };
    { at = Source.make_span 0 1; problem = Interpolated_pattern; fixes = [] };
    { at = Source.make_span 0 1; problem = Float_pattern; fixes = [] };
    { at = Source.make_span 0 1; problem = Rest_not_last; fixes = [] };
    { at = Source.make_span 0 1; problem = Use_after_definition; fixes = [] };
    { at = Source.make_span 0 1; problem = Lowest_operand; fixes = [] };
    { at = Source.make_span 0 1; problem = Chained Range_chain; fixes = [] };
    { at = Source.make_span 0 1; problem = Chained Comparison_chain; fixes = [] };
    { at = Source.make_span 0 1; problem = Chained Implication_chain; fixes = [] };
    { at = Source.make_span 0 1; problem = Mixed_and_or; fixes = [] };
    { at = Source.make_span 0 1; problem = Unordered_operators; fixes = [] };
    { at = Source.make_span 0 1; problem = Mixed_bitwise; fixes = [] };
    { at = Source.make_span 0 1; problem = Negation_and_is; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Token_punctuation Token.Comma; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Token_keyword Token.Fn; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_after_calls; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_in_function_type; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_in_lambda; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Open_paren_after_with; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_body_start; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parameters_start; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Function_type_clauses_end; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Calls_target_end; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Uses_separator; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Self_capability_set; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_arguments_end; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_member; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Trait_member; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Impl_member; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Potential_word; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Unexpected { expected = Function_type_clause Token.Decreases; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Body_start; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Cost_bound; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Resource; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Clause; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Definition; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Field_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parenthesized_function_type; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Generic_parameter; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_definition; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_module_path; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_statement; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_after_method; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Line_break_or_brace; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Range_bound; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Method_name_after_dot; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Method_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Module_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Name_after_dot; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Number_after_minus; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Parameter_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Pattern; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Plain_test_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Test_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Tagged_string; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Type; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Self_associated_capability_set; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_capability_set; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Self_associated_type; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_type; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Expression; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Index_or_type_arguments; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Range_end; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_parameter_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant_name_after_dot; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Constant_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Law_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Variant_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_capability_set_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Associated_type_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Capability_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Theorem_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Trait_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Defined_type_name; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unexpected { expected = Interpolation_end; found = Token.Newline };
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Write "‹write›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Write_conversion "‹write_conversion›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Write_method "‹write_method›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Remove_it; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Remove_own; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          { action = Add_todo_body; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_word "‹remove_word›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          { action = Remove_comma; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Next_arm_on_line;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Write_if; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_ampersand;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          { action = Write_lambda; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Use_parentheses;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Use_square_brackets;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_qualifier;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Write_list; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_macro_call;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Declare_with_let;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Write_call; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_annotation;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Remove_parameters;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Call_unwrap_or;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Pass_lambda; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Move_use_up; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Parenthesize_expression;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Add_parentheses;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Group_first_two;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Group_last_two;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          {
            action = Join_comparisons;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [ { action = Negate_test; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] } ];
    };
    {
      at = Source.make_span 0 1;
      problem = Double_negation;
      fixes =
        [
          { action = Negate_value; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
  ]

let list_examples code =
  List.filter (fun example -> (describe example).code = Diagnostic.Code.Parser code) examples
