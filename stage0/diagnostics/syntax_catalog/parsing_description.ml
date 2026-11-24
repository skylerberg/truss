let say text : _ Description.piece list = [ Text text ]

let show_expected = function
  | Parsing.Token_punctuation punctuation ->
      Printf.sprintf "`%s`" (Token.spell_punctuation punctuation)
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

let show_loop_exit = function Parsing.Break_exit -> "break" | Continue_exit -> "continue"

let show_macro_advice = function
  | Parsing.Print_macro ->
      " Print with `Console.print_line(text)`, and build the text with `${...}` in a string."
  | Format_macro -> " Build text with `${...}` in a string."
  | Vector_macro -> " A list is written `[first, second]`."
  | Assertion_macro ->
      " An assertion is a statement, `assert condition`, in a test, a theorem, or a proof."
  | Debug_macro -> " `echo value` prints a value while debugging."
  | Panic_macro -> " Code that cannot be reached is `unreachable`, and a failure is a `Result`."
  | Other_macro -> ""

let find_code : Parsing.problem -> Diagnostic.Code.parser = function
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
  | Parsing.Unexpected { expected; found } ->
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
  | Parsing.Write code -> Printf.sprintf "Write `%s`" code
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

let describe ({ at; problem; fixes } : Parsing.t) : Source.span Description.t =
  {
    code = Parser (find_code problem);
    severity = Error;
    location = At at;
    message = say (describe_problem problem);
    notes = [];
    fixes =
      List.map
        (fun ({ action; edits } : Parsing.fix) : Source.span Description.fix ->
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
