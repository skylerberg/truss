let make ?(fixes = []) code location message =
  { Description.code = Prover code; severity = Error; location; message; notes = []; fixes }

let say text : _ Description.piece list = [ Text text ]
let quote_in { Prover.key; origin } = Description.Quote (Nodes.In_definition (key, origin))
let tick quoted = [ Description.Text "`"; quote_in quoted; Text "`" ]

let capitalize = function
  | Description.Text text :: rest -> Description.Text (String.capitalize_ascii text) :: rest
  | pieces -> pieces

let show_callee = Build.show_callee

let describe_call { Prover.at; callee } =
  match at with
  | Whole_definition -> [ Description.Text ("a " ^ Build.name_call callee) ]
  | Node origin -> Build.describe_call ?callee origin

let describe_recursive_call call =
  match call.Prover.at with
  | Node (Written _) -> [ Description.Text "This recursive call" ]
  | Node (Desugared _) | Whole_definition -> capitalize (describe_call call)

let join_with_and items =
  let last = List.length items - 1 in
  List.concat
    (List.mapi
       (fun index item ->
         if index = 0 then item
         else
           Description.Text (if index < last then ", " else if last = 1 then " and " else ", and ")
           :: item)
       items)

let join separator items =
  List.concat
    (List.mapi
       (fun index item -> (if index = 0 then [] else [ Description.Text separator ]) @ item)
       items)

let describe_value = function
  | Prover.Named name -> [ Description.Text (Printf.sprintf "`%s`" name) ]
  | Quoted quoted -> tick quoted
  | Temporary -> [ Text "a temporary" ]
  | Self_value -> [ Text "`self`" ]
  | Compiler_local -> [ Text "a local that the compiler introduces" ]

let describe_changed_part { Prover.root; fields } =
  let suffix = String.concat "" (List.map (fun field -> "." ^ field) fields) in
  match root with
  | Named name -> [ Description.Text (Printf.sprintf "`%s%s`" name suffix) ]
  | Self_value -> [ Text (Printf.sprintf "`self%s`" suffix) ]
  | Quoted quoted -> [ Text "`"; quote_in quoted; Text (suffix ^ "`") ]
  | Temporary | Compiler_local -> describe_value root

let describe_invariant_moment = function
  | Prover.When_lend_ends -> say "when the lend of this part ends"
  | When_passed call -> Text "when it is passed to " :: describe_call call
  | Lambda_result -> say "for the value this lambda returns"
  | Lambda_mut_parameter -> say "for a `mut` parameter when this lambda ends"
  | Returned_value -> say "for the value returned here"
  | Mut_parameter_at_return name ->
      say (Printf.sprintf "for `%s` when the function returns here" name)
  | Self_at_return -> say "for `self` when the method returns here"
  | Built_here -> say "for the value built here"
  | At_scope_end value ->
      (Description.Text "for " :: describe_value value) @ [ Text " when its scope ends" ]
  | Element_changed -> say "for the element changed here"
  | Part_lent -> say "for the part lent here"

let show_moment = function
  | Prover.On_entry -> "on entry to the loop"
  | After_iteration -> "after an iteration"
  | Where_left -> "where the loop is left"

let show_requirement = function
  | Prover.Room_written -> "have the room it writes into"
  | Elements_mutated -> "have the elements it mutates"
  | Elements_read -> "have the elements it reads"
  | Ends_with_zero -> "end with a zero, which it reads up to"
  | Element_at_index -> "have an element at its index"
  | Range_within_storage -> "be given a range within the storage"

let describe_difference = function
  | Prover.Upper_bound -> ("more than", "allows")
  | Exact -> ("more or less than", "states")

let show_promiser = function
  | Prover.Trait_promiser -> "trait"
  | Capability_promiser -> "capability"

let name_dependency { Prover.kind; path; _ } =
  match kind with Reads -> Path.show path | Calls | Uses -> show_callee path

let show_dependency_verb = function Prover.Reads -> "reads" | Calls -> "calls" | Uses -> "uses"

let describe_dependency ({ Prover.kind; omitted; _ } as dependency) =
  let verb = show_dependency_verb kind and name = name_dependency dependency in
  match omitted with
  | None -> Printf.sprintf "This %s `%s`" verb name
  | Some (Omitted_field field) ->
      Printf.sprintf "This leaves out the field `%s`, whose default %s `%s`" field verb name
  | Some (Omitted_argument parameter) ->
      Printf.sprintf "This leaves out the argument `%s`, whose default %s `%s`" parameter verb name

let describe_constant_cycle ~cyclic ({ Prover.kind; path; omitted } as dependency) =
  let cyclic_name = Path.show cyclic in
  let consequence = Printf.sprintf "so `%s` would be computed from itself." cyclic_name in
  let part = match kind with Reads -> "value" | Calls | Uses -> "code" in
  let described = describe_dependency dependency in
  match (omitted, Path.equal path cyclic) with
  | None, true -> Printf.sprintf "%s in its own value, %s" described consequence
  | None, false ->
      Printf.sprintf "%s, whose %s depends on `%s`, %s" described part cyclic_name consequence
  | Some _, true -> Printf.sprintf "%s, %s" described consequence
  | Some _, false ->
      Printf.sprintf "%s. The %s of `%s` depends on `%s`, %s" described part
        (name_dependency dependency) cyclic_name consequence

let describe_circular_proof = function
  | Prover.Circular_clause { clause; type_; dependency } ->
      let clause, verb =
        match clause with
        | Invariant_clause -> ("invariant", "proven")
        | Potential_clause -> ("potential", "defined")
      in
      Printf.sprintf "%s, whose proof depends on the %s of `%s`, so the %s would be %s from itself."
        (describe_dependency dependency) clause (Types.show type_) clause verb
  | Circular_contract { cyclic; dependency } when Path.equal dependency.path cyclic ->
      Printf.sprintf "%s in its own contract, so the contract would be proven from itself."
        (describe_dependency dependency)
  | Circular_contract { cyclic; dependency } ->
      Printf.sprintf
        "%s, whose proof depends on the contract of `%s`, so the contract would be proven from \
         itself."
        (describe_dependency dependency) (show_callee cyclic)
  | Circular_inherited_contract { cyclic; dependency } ->
      Printf.sprintf
        "The contract that this method takes from its trait %s `%s`, whose proof depends on the \
         contract of `%s`, so the contract would be proven from itself."
        (show_dependency_verb dependency.kind)
        (name_dependency dependency) (show_callee cyclic)
  | Circular_instance { type_; dependency; cyclic } when Path.equal dependency cyclic ->
      Printf.sprintf
        "A value of type `%s` is used here, and the invariant of that type or of a part of it \
         depends on `%s`, so the invariant would be proven from itself."
        (Types.show type_) (show_callee dependency)
  | Circular_instance { type_; dependency; cyclic } ->
      Printf.sprintf
        "A value of type `%s` is used here. The invariant of that type or of a part of it depends \
         on `%s`, whose proof depends on `%s`, so the invariant would be proven from itself."
        (Types.show type_) (show_callee dependency) (show_callee cyclic)
  | Circular_laws { trait; type_ } ->
      Printf.sprintf
        "This assumes the laws of `%s` for `%s`, whose proof depends on this one, so a law would \
         be proven from itself."
        (Types.show_trait trait) (Types.show type_)

let describe_unbounded = function
  | Prover.Unstated_costs { metric; callees; editable; counts_units } ->
      let metric = Language.Metric.show metric in
      let quote_callees callees =
        join_with_and
          (List.map
             (fun callee -> [ Description.Text (Printf.sprintf "`%s`" (show_callee callee)) ])
             callees)
      in
      let clause = Printf.sprintf "`cost %s`" metric in
      let example = if counts_units then Printf.sprintf ", such as `cost %s O(1)`" metric else "" in
      let advice =
        let recipients =
          match editable with
          | [ _ ] -> quote_callees editable
          | _ when List.length editable = List.length callees -> [ Text "each" ]
          | _ -> quote_callees editable @ [ Text " each" ]
        in
        if editable = [] then []
        else
          (Description.Text " Give " :: recipients)
          @ [ Text (Printf.sprintf " a %s clause%s." clause example) ]
      in
      (Description.Text "This loop calls " :: quote_callees callees)
      @ Text
          (Printf.sprintf ", which %s no %s, so the prover cannot bound the cost of an iteration."
             (match callees with [ _ ] -> "states" | _ -> "state")
             clause)
        :: advice
  | Changing_cost { is_amortized; call; values } -> (
      let cost, dependency =
        if is_amortized then ("amortized cost", "the potential of ") else ("cost", "")
      in
      match values with
      | [] ->
          [
            Text (Printf.sprintf "The prover cannot bound the %s of `" cost);
            quote_in call;
            Text
              "` by the values this loop does not mutate, so it cannot count the loop's cost: give \
               the loop a `cost` clause.";
          ]
      | values ->
          Description.Text (Printf.sprintf "The %s of `" cost)
          :: quote_in call
          :: Text ("` depends on " ^ dependency)
          :: join_with_and (List.map describe_changed_part values)
          @ [
              Text
                ", which this loop changes, so the prover cannot bound the cost of an iteration by \
                 the values the loop does not mutate. Give the loop a `cost` clause.";
            ])
  | Uncounted_potential { metric; callee; call; is_editable } ->
      let metric = Language.Metric.show metric in
      let callee = Printf.sprintf "`%s`" (show_callee callee) in
      [
        Text
          (Printf.sprintf "%s states no `cost amortized %s`, so the prover counts `" callee metric);
        quote_in call;
        Text
          (Printf.sprintf
             "` at its plain cost plus the change in potential of the values it mutates or \
              returns. The prover cannot bound that change by the values this loop does not \
              mutate.%s"
             (if is_editable then
                Printf.sprintf " Give %s a `cost amortized %s` clause." callee metric
              else ""));
      ]
  | Unbounded_iteration ->
      say
        "The prover cannot bound the cost of one iteration of this loop by the values the loop \
         does not mutate, so it cannot count the loop's cost: give the loop a `cost` clause."

let describe_promise = function
  | Prover.Own_promise { counting; clause } ->
      let difference, verb = describe_difference counting in
      [
        Description.Text (Printf.sprintf "The function may spend %s `" difference);
        quote_in clause;
        Text (Printf.sprintf "` %s before it returns here." verb);
      ]
  | Inherited_promise { counting; promiser; clause } ->
      let difference, verb = describe_difference counting in
      [
        Text
          (Printf.sprintf "The method may spend %s its %s's `" difference (show_promiser promiser));
        quote_in clause;
        Text (Printf.sprintf "` %s before it returns here." verb);
      ]
  | Restated_promise { counting; for_type; name; clause; trait; declared } ->
      let difference, verb = describe_difference counting in
      [
        Text
          (Printf.sprintf "The contract of `%s`'s `%s` may spend %s `" (Types.show for_type) name
             difference);
        quote_in clause;
        Text
          (Printf.sprintf "`, which `%s` adds to `%s.%s`, %s." (Types.show_trait trait)
             (Types.show_trait declared) name verb);
      ]

let describe_obligation = function
  | Prover.Assertion_may_fail { clause } -> tick clause @ [ Text " may not hold." ]
  | Bit_vector_assertion_may_fail { clause } ->
      tick clause @ [ Text " may not hold for every value of the variables it names." ]
  | Desugared_assertion_may_fail { call } ->
      capitalize (describe_call call) @ [ Text " may not give `true`." ]
  | Recursion_not_on_part { call; compared } ->
      describe_recursive_call call
      @ [
          Text
            (Printf.sprintf " may not be on a part of %s: give the function a `decreases` clause."
               (match List.map (Printf.sprintf "`%s`") compared with
               | [ name ] -> name
               | names -> "the first of " ^ String.concat " and " names ^ " that it changes"));
        ]
  | Recursion_may_not_end { call; is_self_call = true } ->
      describe_recursive_call call
      @ [
          Text
            " may not end: give the function a `decreases` clause for the prover to show that the \
             recursion ends.";
        ]
  | Recursion_may_not_end { call; is_self_call = false } ->
      capitalize (describe_call call)
      @ [
          Text
            " may not end: it calls back here, and both need a `decreases` clause for the prover \
             to show that the recursion ends.";
        ]
  | Uncompared_recursion { call } ->
      capitalize (describe_call call)
      @ [
          Text
            " may not end: it calls back here, and the prover reads the call without the callee's \
             `decreases` clause.";
        ]
  | Measure_may_not_decrease { call; measures } ->
      capitalize (describe_call call)
      @ Description.Text " may not decrease `"
        :: join ", " (List.map (fun measure -> [ quote_in measure ]) measures)
      @ [ Text "`." ]
  | Recursion_through_impl { call; impl } ->
      capitalize (describe_call call)
      @ [
          Text
            (Printf.sprintf
               " reaches back here through code that its `impl` %s. No measure can be stated for \
                that code, so the recursion cannot be shown to end."
               (match impl with Derives -> "derives" | Inherits -> "inherits from its trait"));
        ]
  | Recursion_through_supply (Named_function path) ->
      say
        (Printf.sprintf
           "Naming `%s` as a value reaches back here, and such a use passes no arguments the \
            prover can compare, so the recursion cannot be shown to end: write it as a direct call \
            on a part."
           (Path.show path))
  | Recursion_through_supply (Bound_through_call { call; owner }) ->
      capitalize (describe_call call)
      @ [
          Text
            (Printf.sprintf
               " uses `%s` where a bound needs it, and its methods reach back here. Such a use \
                passes no arguments the prover can compare, so the recursion cannot be shown to \
                end: write it as a direct call on a part."
               (Path.show owner));
        ]
  | Recursion_through_supply (Bound_through_name { path; owner }) ->
      say
        (Printf.sprintf
           "Naming `%s` as a value uses `%s` where a bound needs it, and its methods reach back \
            here. Such a use passes no arguments the prover can compare, so the recursion cannot \
            be shown to end."
           (Path.show path) (Path.show owner))
  | Recursion_through_supply (Provided owner) ->
      say
        (Printf.sprintf
           "This `provide` gives `%s`, whose methods call back here, so the prover cannot show \
            that the recursion ends."
           (Path.show owner))
  | Constant_cycle { cyclic; dependency } -> say (describe_constant_cycle ~cyclic dependency)
  | Circular_proof circular -> say (describe_circular_proof circular)
  | Precondition_may_fail { clause; call } ->
      tick clause @ (Description.Text " may not hold for " :: describe_call call) @ [ Text "." ]
  | Precondition_may_panic { clause; call } ->
      tick clause
      @ (Description.Text " may not hold for " :: describe_call call)
      @ [ Text ", so the call may panic." ]
  | Panics_where_ruled_out { call; condition } ->
      capitalize (describe_call call)
      @ Description.Text " may panic where `"
        :: join " && " (List.map (fun part -> [ quote_in part ]) condition)
      @ [ Text "` holds, which the function's `uses Panic unless` rules out." ]
  | Upper_bound_in_exact_cost { metric; call } ->
      Description.Text
        (Printf.sprintf "Only an upper bound is known for the `%s` of "
           (Language.Metric.show metric))
      :: describe_call call
      @ [
          Text
            ", which may spend less, so no `==` bound can count it. State the cost with `<=`, or \
             give the type of the function called an `==` bound.";
        ]
  | Out_of_bounds { at } -> tick at @ [ Text " may not be within the collection." ]
  | Intrinsic_requirement { at; requirement } ->
      tick at @ [ Text (Printf.sprintf " may not %s." (show_requirement requirement)) ]
  | Invariant_may_fail { type_; moment } ->
      Description.Text (Printf.sprintf "The invariant of `%s` may not hold " (Types.show type_))
      :: describe_invariant_moment moment
      @ [ Text "." ]
  | Preserved_invariant { type_; value } ->
      Description.Text (Printf.sprintf "The invariant of `%s` may not hold for " (Types.show type_))
      :: describe_value value
      @ [ Text " after an iteration." ]
  | Derived_default_invariant ->
      say
        "The value that the derived `Default` builds from the fields' defaults may not meet this \
         type's invariant."
  | Loop_invariant { clause; moment } ->
      [
        Text "The loop invariant `";
        quote_in clause;
        Text (Printf.sprintf "` may not hold %s." (show_moment moment));
      ]
  | Lambda_promise { promise } ->
      tick promise
      @ [
          Text
            " may not hold of a result of this lambda, and the type of the parameter it is passed \
             for promises it.";
        ]
  | Lambda_cost { counting; type_ } ->
      let difference, verb = describe_difference counting in
      say
        (Printf.sprintf "This lambda may spend %s its type, `%s`, %s." difference (Types.show type_)
           verb)
  | Lambda_call_above_bound { metric } ->
      say
        (Printf.sprintf
           "The prover cannot show that a call of this lambda %s than the bound it found for every \
            call, which a cost here relies on."
           (match metric with
           | Time -> "takes no more time"
           | Allocations -> "makes no more allocations"
           | Allocated_bytes -> "allocates no more bytes"))
  | Callback_precondition { clause; call; name } ->
      tick clause
      @ (Description.Text " may not hold for " :: describe_call call)
      @ [ Text (Printf.sprintf " through `%s`." name) ]
  | Loop_cost_clause { clause; moment } ->
      [
        Text "The loop's `";
        quote_in clause;
        Text (Printf.sprintf "` may not hold %s." (show_moment moment));
      ]
  | Iteration_above_inferred_bound ->
      say
        "The prover cannot show that this iteration of the loop costs no more than the \
         per-iteration bound it inferred from the values the loop does not mutate: give the loop a \
         `cost` clause."
  | Unbounded_iteration_cost unbounded -> describe_unbounded unbounded
  | Visited_out_of_order ->
      say
        "This loop names `visited`, and the `next` of its cursor may not give the values of the \
         cursor's `model()` in order."
  | Loop_measure_may_not_decrease -> say "This loop's measure may not decrease."
  | Element_count_changes ->
      say
        "An iteration of this loop may change how many elements the collection has. The \
         collection's `element(mut self)` must leave its `count` as it was."
  | Out_of_range { at; type_ } ->
      tick at @ [ Text (Printf.sprintf " may not fit in `%s`." (Types.show type_)) ]
  | Divisor_may_be_zero { at } -> [ Text "The divisor in `"; quote_in at; Text "` may be zero." ]
  | Division_overflow { at; type_ } ->
      tick at
      @ [ Text (Printf.sprintf " may overflow `%s`: the least value over -1." (Types.show type_)) ]
  | Overflow { at; type_ } ->
      tick at @ [ Text (Printf.sprintf " may overflow `%s`." (Types.show type_)) ]
  | Shift_amount { amount; is_operand; bits } ->
      [
        Text (if is_operand then "The shift amount `" else "The shift amount in `");
        quote_in amount;
        Text (Printf.sprintf "` may not be less than %d." bits);
      ]
  | Float_conversion { at; target } ->
      tick at
      @ [
          Text
            (Printf.sprintf
               " may not fit `%s`: it must be a number that, cut toward zero, is in its range."
               (Types.show target));
        ]
  | Not_a_scalar_value { at } ->
      tick at @ [ Text " may not be a Unicode scalar value, which a `Character` must be." ]
  | Unreachable_reached -> say "This `unreachable` may be reached."
  | May_not_return_under_no_allocation { function_ } ->
      say
        ((match function_ with
           | Some function_ -> Printf.sprintf "`%s`" (Build.show_callee function_)
           | None -> "This method")
        ^ " may not return: its code, or a function it calls, may run out of memory. `cost \
           allocations == 0` is stated for it, and a call through a bound, or of a function value, \
           takes that clause to mean that the function returns.")
  | Cost_promise promise -> describe_promise promise
  | Impl_precondition { clause } ->
      tick clause
      @ [
          Text
            " may not follow from the trait's precondition, which callers through the trait show, \
             and an `impl`'s precondition must.";
        ]
  | Impl_panic_condition { clause } ->
      tick clause
      @ [
          Text
            " may not follow from the trait's condition after `Panic unless`. A caller without \
             `Panic` proves only the trait's condition, so this `impl` could panic in code that \
             has no `Panic`.";
        ]
  | Postcondition { clause; promiser; moment } -> (
      let failure =
        match (moment, promiser) with
        | Where_lent, _ -> " may not hold for the part lent here."
        | At_lend_end, _ -> " may not hold when the method ends here."
        | At_return, None -> " may not hold when the function returns here."
        | At_return, Some _ -> " may not hold when the method returns here."
      in
      match promiser with
      | None -> tick clause @ [ Text failure ]
      | Some promiser ->
          [
            Text (Printf.sprintf "The %s's `" (show_promiser promiser));
            quote_in clause;
            Text ("`" ^ failure);
          ])
  | Law_may_fail { trait; law; for_type } ->
      say
        (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (Types.show_trait trait) law
           (Types.show for_type))
  | Restated_contract { for_type; name; clause; trait; declared } ->
      [
        Text
          (Printf.sprintf "The contract of `%s`'s `%s` may not imply `" (Types.show for_type) name);
        quote_in clause;
        Text
          (Printf.sprintf "`, which `%s` adds to `%s.%s`." (Types.show_trait trait)
             (Types.show_trait declared) name);
      ]
  | Negative_potential { type_ } ->
      say
        (Printf.sprintf
           "The potential of `%s` may be below zero for a value that meets its invariants."
           (Types.show type_))
  | May_alias { first; second } ->
      [
        Text "`";
        quote_in first;
        Text "` and `";
        quote_in second;
        Text "` may reach the same elements, which are used together.";
      ]
  | Function_requirement { function_; use; clause } ->
      [
        Text
          (Printf.sprintf "`%s` is %s, so its `"
             (match function_ with
             | Named_function path -> Path.show path
             | Callback_parameter name -> name)
             (match use with
             | Used_as_value type_ ->
                 Printf.sprintf "used as a value of `%s`, a type that states no `requires`"
                   (Types.show type_)
             | Passed_for_parameter ->
                 "passed for a parameter whose type may not imply its `requires`"));
        quote_in clause;
        Text "` may not hold.";
      ]
  | Callback_promise { promise; unpromised } ->
      [
        Text "This argument's parameter promises `";
        quote_in promise;
        Text
          ("` of each result of the function passed for it, "
          ^
          match unpromised with
          | Nothing_promises -> "and nothing promises it of the function passed here."
          | Type_may_not_promise name ->
              Printf.sprintf "and the type of `%s` may not promise it." name
          | Ensures_may_not_promise path ->
              Printf.sprintf "and the `ensures` of `%s` may not promise it." (Path.show path));
      ]
  | Duplicate_key { key } ->
      [
        Text "The key `";
        (match key with Some key -> quote_in key | None -> Text "this key");
        Text "` may equal an earlier key of this map.";
      ]

let find_code : Prover.obligation -> Diagnostic.Code.prover = function
  | Assertion_may_fail _ | Bit_vector_assertion_may_fail _ | Desugared_assertion_may_fail _ ->
      Assertion
  | Recursion_not_on_part _ | Recursion_may_not_end _ | Uncompared_recursion _
  | Measure_may_not_decrease _ | Recursion_through_impl _ | Recursion_through_supply _
  | Loop_measure_may_not_decrease ->
      Termination
  | Constant_cycle _ -> Constant_cycle
  | Circular_proof _ -> Circular_proof
  | Precondition_may_fail _ | Intrinsic_requirement _ | Callback_precondition _ | Float_conversion _
  | Not_a_scalar_value _ | Impl_precondition _ | Impl_panic_condition _ | Function_requirement _ ->
      Requires
  | Precondition_may_panic _ | Panics_where_ruled_out _ -> Panic
  | Upper_bound_in_exact_cost _ | Lambda_cost _ | Lambda_call_above_bound _ | Loop_cost_clause _
  | May_not_return_under_no_allocation _ | Iteration_above_inferred_bound
  | Unbounded_iteration_cost _ | Cost_promise _ | Negative_potential _ ->
      Cost
  | Out_of_bounds _ -> Out_of_bounds
  | Invariant_may_fail _ | Preserved_invariant _ | Derived_default_invariant | Loop_invariant _
  | Visited_out_of_order | Element_count_changes ->
      Invariant
  | Lambda_promise _ | Postcondition _ | Restated_contract _ | Callback_promise _ -> Ensures
  | Out_of_range _ -> Out_of_range
  | Divisor_may_be_zero _ -> Division
  | Division_overflow _ | Overflow _ -> Overflow
  | Shift_amount _ -> Shift
  | Unreachable_reached -> Unreachable
  | Law_may_fail _ -> Law
  | May_alias _ | Duplicate_key _ -> Disjoint

let locate : Prover.location -> _ = function
  | Node origin -> Build.at origin
  | Whole_definition -> At Definition

let describe_stop = Codegen_description.describe_stop ~show_file:Path.show_file

let describe_stop_sentence stop =
  let sentence =
    String.concat " "
      (List.map String.trim (String.split_on_char '\n' (String.trim (describe_stop stop))))
  in
  if String.ends_with ~suffix:"." sentence then sentence else sentence ^ "."

let describe_failed_runs failed_runs =
  List.map
    (function
      | Prover.Constant_run { path; stop } ->
          Description.Text
            (Printf.sprintf " The evaluation of `%s` stopped, so its value is not known: %s"
               (Path.show path) (describe_stop_sentence stop))
      | Assertion_run stop ->
          Text
            (Printf.sprintf " Its evaluation stopped, so its result is not known: %s"
               (describe_stop_sentence stop)))
    failed_runs

let describe_failure = function
  | Prover.Refuted -> say " This fails every time the code reaches it."
  | Falsifiable { failed_runs } -> describe_failed_runs failed_runs
  | Undecided { unknown; has_untriggered_fact; failed_runs } ->
      Text
        ((match unknown with
           | Out_of_steps ->
               " The solver reached its step limit before it decided whether this holds."
           | Incomplete reason ->
               Printf.sprintf
                 " The solver's decision procedures are incomplete for this query, so it stopped \
                  without deciding whether this holds. Z3 gives the reason `%s`."
                 reason)
        ^ " If the code is correct, a `proof` block or a theorem can lead the solver to the proof."
        ^
        if has_untriggered_fact then
          " A quantified fact in the query has no trigger, so an `assert` of that fact at the term \
           the proof needs may be enough."
        else "")
      :: describe_failed_runs failed_runs

let describe_withheld = function
  | [] -> []
  | callees ->
      Description.Text " A specification learns nothing here from the contract of "
      :: join_with_and
           (List.map
              (fun callee -> [ Description.Text ("`" ^ Build.show_callee callee ^ "`") ])
              callees)
      @ say
          ", since the call may not return: the function, or code supplied to it, may run out of \
           memory."

let advise_other_ways : Diagnostic.Code.prover -> _ = function
  | Overflow | Division | Shift ->
      say " It can also be checked first with an `if`, or done with the checked operation."
  | Out_of_bounds ->
      say " It can also be checked first with an `if`, or, for one element, read with `get`."
  | _ -> []

let show_comparison : Language.Comparison.t -> string = function
  | Equal -> "=="
  | Not_equal -> "!="
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="

let negate : Language.Comparison.t -> Language.Comparison.t = function
  | Equal -> Not_equal
  | Not_equal -> Equal
  | Less -> Greater_equal
  | Less_equal -> Greater
  | Greater -> Less_equal
  | Greater_equal -> Less

let is_negation (first : Code.t) (second : Code.t) =
  match (first, second) with
  | Compared first, Compared second ->
      first.left = second.left && first.right = second.right
      && negate first.comparison = second.comparison
  | Not negated, other | other, Not negated -> negated = other
  | _ -> false

let rec show_value level (code : Code.t) =
  let parenthesize inner text = if inner < level then "(" ^ text ^ ")" else text in
  match code with
  | Name name -> name
  | Integer value when Z.sign value < 0 && level > 0 -> "(" ^ Z.to_string value ^ ")"
  | Integer value -> Z.to_string value
  | Boolean value -> if value then "true" else "false"
  | Field { receiver; field } -> show_value 4 receiver ^ "." ^ field
  | Limit { type_; limit } -> (
      Types.show type_ ^ match limit with Minimum -> ".minimum" | Maximum -> ".maximum")
  | Negated inner -> parenthesize 3 ("-" ^ show_value 4 inner)
  | Sum parts -> parenthesize 1 (String.concat " + " (List.map (show_value 1) parts))
  | Product parts -> parenthesize 2 (String.concat " * " (List.map (show_value 2) parts))
  | Difference (left, right) -> parenthesize 1 (show_value 1 left ^ " - " ^ show_value 2 right)
  | Quotient (left, right) -> parenthesize 2 (show_value 2 left ^ " / " ^ show_value 3 right)
  | Compared _ | Not _ | All _ | Any _ | Implies _ -> "(" ^ show_code code ^ ")"

and show_goal ~is_nested (code : Code.t) =
  let join separator parts =
    let text = String.concat separator (List.map (show_goal ~is_nested:true) parts) in
    if is_nested then "(" ^ text ^ ")" else text
  in
  match code with
  | Compared { left; comparison; right } ->
      Printf.sprintf "%s %s %s" (show_value 0 left) (show_comparison comparison)
        (show_value 0 right)
  | Not (Compared compared) ->
      show_goal ~is_nested (Compared { compared with comparison = negate compared.comparison })
  | Not inner -> "!" ^ show_value 4 inner
  | All parts -> join " && " parts
  | Any parts -> join " || " parts
  | Implies { premise; conclusion } ->
      Printf.sprintf "(%s) ==> (%s)" (show_code premise) (show_code conclusion)
  | value -> show_value 0 value

and show_code code = show_goal ~is_nested:false code

let show_argument (code : Code.t) =
  match code with
  | Name _ | Field _ | Boolean _ | Limit _ -> show_code code
  | Integer value when Z.sign value >= 0 -> show_code code
  | _ -> "(" ^ show_code code ^ ")"

let describe_required = function
  | Prover.Clause code -> Description.Text (show_code code)
  | Substituted_clause { clause = { key; origin }; replacements; type_names } ->
      Substituted
        {
          clause = Nodes.In_definition (key, origin);
          replacements =
            List.map
              (fun (replaced, code) -> (Nodes.In_definition (key, replaced), show_argument code))
              replacements;
          type_names = List.map (fun (name, type_) -> (name, Types.show type_)) type_names;
        }

let add_clause (place : Prover.clause_place) line : _ Description.edit =
  match place with
  | Before_clause clause -> Build.insert_before clause (line @ [ Description.Text "\n  " ])
  | Before_body body -> Add_line_before (Nodes.Node body, line)

let describe_fix = function
  | Prover.Add_requires { place; required; premise; condition } ->
      let premise =
        match (premise, required) with
        | Some premise, [ Clause clause ] when is_negation premise clause -> None
        | _ -> premise
      in
      let required = List.map describe_required required in
      let required =
        match condition with
        | [] -> required
        | condition -> required @ [ Text (" when " ^ Types.show_condition condition) ]
      in
      let required =
        match premise with
        | Some premise ->
            (Description.Text ("(" ^ show_code premise ^ ") ==> (") :: required) @ [ Text ")" ]
        | None -> required
      in
      {
        Description.title = (Description.Text "Add `requires " :: required) @ [ Text "`" ];
        edits = [ add_clause place (Text "requires " :: required) ];
      }
  | Add_panic place ->
      { title = say "Add `uses Panic`"; edits = [ add_clause place [ Text "uses Panic" ] ] }
  | Add_panic_to_uses uses ->
      { title = say "Add `uses Panic`"; edits = [ Build.insert_after uses [ Text ", Panic" ] ] }

let show_construct = function
  | Prover.Potential_of_elements -> "the potential of a collection's elements"
  | Metric_of_non_trait_method metric ->
      Printf.sprintf "the %s of a function that is not a trait's method"
        (Language.Metric.show metric)
  | Calls_target -> "this `calls` target"
  | Unsolved_size -> "an unsolved size"
  | Elements_of type_ -> Printf.sprintf "the elements of `%s`" (Types.show type_)
  | Sequence_elements -> "the elements of a sequence"
  | Function_value_costs -> "a function value's costs"
  | Intrinsic_at_parameter { operation; parameter } ->
      Printf.sprintf "`intrinsic.%s` at the type parameter `%s`"
        (Intrinsic.show_operation operation)
        (Types.show parameter)
  | Negation_of type_ -> Printf.sprintf "negating a value of `%s`" (Types.show type_)
  | Shift_of type_ -> Printf.sprintf "a shift of `%s`" (Types.show type_)
  | Range_of type_ -> Printf.sprintf "a range of `%s`" (Types.show type_)
  | Unreadable_cursor type_ ->
      Printf.sprintf "a loop over `%s`, whose `next` the prover cannot read" (Types.show type_)
  | Field field -> Printf.sprintf "the field `%s`" field
  | Alternatives_binding_mut -> "a name that the alternatives of a pattern bind `mut`, here"
  | Hidden_field_of type_ ->
      Printf.sprintf "a field of `%s`, whose fields the prover does not see" (Types.show type_)
  | Fields_of type_ -> Printf.sprintf "the fields of `%s`" (Types.show type_)
  | Constant_assignment -> "assigning to a constant"
  | Float_literal_without_type -> "a float literal without a float type"
  | Lent_part_outside_lending_method -> "a lent part outside a lending method's body"
  | Hidden_variant_of type_ ->
      Printf.sprintf "a variant of `%s`, which the prover does not see" (Types.show type_)
  | Nonreturning_specification_call -> "a call in a specification that never returns"
  | Compiler_restated_method { trait; declared_by } ->
      Printf.sprintf "a method that `%s` restates from `%s`, which the compiler implements"
        (Types.show_trait trait) (Path.show declared_by)
  | Literal_of type_ -> Printf.sprintf "a literal of `%s`" (Types.show type_)
  | Unreadable_function_value -> "a function the prover cannot read, used as a value"
  | String_pattern_on type_ -> Printf.sprintf "a string pattern on `%s`" (Types.show type_)
  | Specification_function -> "this specification function"

let describe_instance = function
  | [] -> []
  | instance ->
      [
        Description.Text
          ("Where "
          ^ String.concat " and "
              (List.map
                 (fun (parameter, builtin) ->
                   Printf.sprintf "`%s` is `%s`" parameter (Language.Builtin_type.show builtin))
                 instance)
          ^ ": ");
      ]

let describe : Prover.t -> Nodes.description = function
  | Proves { location; instance; obligation } ->
      make (find_code obligation) (locate location)
        (describe_instance instance @ describe_obligation obligation)
  | Unproven { location; instance; obligation; failure; fixes; withheld; cited = _ } ->
      let code = find_code obligation in
      make code (locate location) ~fixes:(List.map describe_fix fixes)
        (describe_instance instance @ describe_obligation obligation @ describe_failure failure
       @ describe_withheld withheld @ advise_other_ways code)
  | Unreadable { location; construct; foreign } ->
      make Unsupported (locate location)
        (say
           (Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
              (match foreign with
              | Some definition ->
                  Printf.sprintf "%s, in `%s`" (show_construct construct) (Path.show definition)
              | None -> show_construct construct)))
  | Unevaluated { path; stop } ->
      make Evaluation (At Nodes.Definition)
        (say
           (Printf.sprintf "The value of `%s` cannot be computed: %s" (Path.show path)
              (describe_stop stop)))

let find_cited : Prover.t -> Prover.quoted option = function
  | Unproven { cited; _ } -> cited
  | Proves _ | Unreadable _ | Unevaluated _ -> None

let describe_cited diagnostic (citation : Prover.citation) =
  let (description : Nodes.description) = describe diagnostic in
  match (find_cited diagnostic, citation) with
  | Some { key; origin }, Cited_here ->
      {
        description with
        notes =
          description.notes
          @ [
              ( Description.At (Nodes.In_definition (key, origin)),
                say "This is the clause that must hold." );
            ];
      }
  | Some _, Cited_at { path; line } ->
      {
        description with
        message =
          description.message
          @ say (Printf.sprintf " The clause that must hold is at `%s:%d`." path line);
      }
  | None, _ -> description
