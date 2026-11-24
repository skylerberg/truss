open Description
open Nodes
open Build

type quoted = { key : Path.key; origin : Core.origin }
type location = Node of Core.origin | Whole_definition
type call = { at : location; callee : Path.t option }
type counting = Upper_bound | Exact
type moment = On_entry | After_iteration | Where_left

type value =
  | Named of string
  | Quoted of quoted
  | Temporary
  | Self_value
  | Compiler_local
  | Lent_part

type invariant_moment =
  | When_lend_ends
  | When_passed of call
  | Lambda_result
  | Lambda_mut_parameter
  | Returned_value
  | Mut_parameter_at_return of string
  | Self_at_return
  | Built_here
  | At_scope_end of value
  | Element_changed
  | Part_lent

type requirement =
  | Room_written
  | Elements_mutated
  | Elements_read
  | Ends_with_zero
  | Elements_at_both_indexes
  | Length_within_storage
  | Element_to_pop
  | Element_at_index
  | Index_within_length
  | Range_within_view
  | Count_of_array

type recursion_impl = Derives | Inherits

type supplied_recursion =
  | Named_function of Path.t
  | Bound_through_call of { call : call; owner : Path.t }
  | Bound_through_name of { path : Path.t; owner : Path.t }
  | Provided of Path.t

type dependency_kind = Reads | Calls | Uses
type omitted = Omitted_field of string | Omitted_argument of string
type dependency = { kind : dependency_kind; path : Path.t; omitted : omitted option }

type unbounded =
  | Unstated_costs of {
      metric : Language.Metric.t;
      callees : Path.t list;
      editable : Path.t list;
      counts_units : bool;
    }
  | Changing_cost of { is_amortized : bool; call : quoted; values : value list }
  | Unbounded_iteration

type promiser = Trait_promiser | Capability_promiser

type promise =
  | Own_promise of { counting : counting; clause : quoted }
  | Inherited_promise of { counting : counting; promiser : promiser; clause : quoted }
  | Restated_promise of {
      counting : counting;
      for_type : Types.ty;
      name : string;
      clause : quoted;
      trait : Types.trait_reference;
      declared : Types.trait_reference;
    }

type callback_reason = Used_as_unpromising_value | Passed_for_unpromising_parameter

type unpromised =
  | Nothing_promises
  | Type_may_not_promise of string
  | Type_promises_nothing of string
  | Ensures_may_not_promise of Path.t

type obligation =
  | Assertion_may_fail of { clause : quoted }
  | Bit_vector_assertion_may_fail of { clause : quoted }
  | Desugared_assertion_may_fail of { call : call }
  | Recursion_not_on_part of { call : call; compared : string list }
  | Recursion_may_not_end of { call : call; is_self_call : bool }
  | Uncompared_recursion of { call : call }
  | Measure_may_not_decrease of { call : call; measures : quoted list }
  | Recursion_through_impl of { call : call; impl : recursion_impl }
  | Recursion_through_supply of supplied_recursion
  | Constant_cycle of { cyclic : Path.t; dependency : dependency }
  | Precondition_may_fail of { clause : quoted; call : call }
  | Precondition_may_panic of { clause : quoted; call : call }
  | Panics_where_ruled_out of { call : call; condition : quoted list }
  | Upper_bound_in_exact_cost of { metric : Language.Metric.t; call : call }
  | Out_of_bounds of { at : quoted }
  | Intrinsic_requirement of { at : quoted; requirement : requirement }
  | Invariant_may_fail of { type_ : Types.ty; moment : invariant_moment }
  | Preserved_invariant of { type_ : Types.ty; value : value }
  | Derived_default_invariant
  | Loop_invariant of { clause : quoted; moment : moment }
  | Lambda_promise of { promise : quoted }
  | Lambda_cost of { counting : counting; type_ : Types.ty }
  | Lambda_call_above_bound of { metric : Language.Metric.t }
  | Callback_precondition of { clause : quoted; call : call; name : string }
  | Parameter_contract of { path : Path.t; clause : quoted }
  | Loop_cost_clause of { clause : quoted; moment : moment }
  | Iteration_above_inferred_bound
  | Unbounded_iteration_cost of unbounded
  | Visited_out_of_order
  | Loop_measure_may_not_decrease
  | Element_count_changes
  | Out_of_range of { at : quoted; type_ : Types.ty }
  | Divisor_may_be_zero of { at : quoted }
  | Division_overflow of { at : quoted; type_ : Types.ty }
  | Overflow of { at : quoted; type_ : Types.ty }
  | Shift_amount of { amount : quoted; is_operand : bool; bits : int }
  | Float_conversion of { at : quoted; target : Types.ty }
  | Not_a_scalar_value of { at : quoted }
  | Unreachable_reached
  | Lent_part_ensures of { clause : quoted }
  | Cost_promise of promise
  | Impl_precondition of { clause : quoted }
  | Impl_panic_condition of { clause : quoted }
  | Ensures_at_method_end of { clause : quoted }
  | Ensures_at_return of { clause : quoted }
  | Promiser_ensures of { promiser : promiser; clause : quoted }
  | Law_may_fail of { trait : Types.trait_reference; law : string; for_type : Types.ty }
  | Restated_contract of {
      for_type : Types.ty;
      name : string;
      clause : quoted;
      trait : Types.trait_reference;
      declared : Types.trait_reference;
    }
  | Negative_potential of { type_ : Types.ty }
  | May_alias of { first : quoted; second : quoted }
  | Callback_requirement of { name : string; reason : callback_reason; clause : quoted }
  | Callback_promise of { promise : quoted; unpromised : unpromised }
  | Duplicate_key of { key : quoted option }
  | Value_contract of { path : Path.t; type_ : Types.ty; clause : quoted }

type construct =
  | Potential_of_elements
  | Metric_of_non_trait_method of Language.Metric.t
  | Calls_target
  | Unsolved_size
  | Elements_of of Types.ty
  | Sequence_elements
  | Function_value_costs
  | Intrinsic_at_parameter of { operation : string; parameter : Types.ty }
  | Negation_of of Types.ty
  | Shift_of of Types.ty
  | Slice_of of Types.ty
  | Unreadable_parameter_type
  | Unreadable_cursor of Types.ty
  | Field of string
  | Alternatives_binding_mut
  | Hidden_field_of of Types.ty
  | Fields_of of Types.ty
  | Constant_assignment
  | Float_literal_without_type
  | Lent_part_outside_lending_method
  | Hidden_variant_of of Types.ty
  | Nonreturning_specification_call
  | Compiler_restated_method of { trait : Types.trait_reference; declared_by : Path.t }
  | Literal_of of Types.ty
  | Unreadable_function_value
  | String_pattern_on of Types.ty
  | Specification_function

type failed_run = Constant_run of { path : Path.t; report : string } | Assertion_run of string

type path_note =
  | Arm_taken of Core.origin list
  | Condition_holds of { condition : Core.origin; holds : bool }
  | Else_runs of Core.origin
  | Returns_early of Core.origin

type unknown = Out_of_steps | Incomplete of string

type failure =
  | Refuted
  | Counterexample of {
      values : (string * string) list;
      path : path_note list;
      failed_runs : failed_run list;
    }
  | Undecided of { unknown : unknown; has_untriggered_fact : bool; failed_runs : failed_run list }

type required =
  | Code of string
  | Substituted_clause of {
      clause : quoted;
      replacements : (Core.origin * string) list;
      type_names : (string * string) list;
    }

type panic_place =
  | After_uses of Core.origin
  | Before_clause of Core.origin
  | Before_body of Core.origin

type fix =
  | Add_requires of {
      body : Core.origin;
      required : required list;
      premise : string option;
      condition : Types.condition;
    }
  | Add_panic of panic_place

type citation = Cited_here | Cited_at of { path : string; line : int }
type instance = (string * Language.Builtin_type.t) list

type t =
  | Proves of { location : location; instance : instance; obligation : obligation }
  | Unproven of {
      location : location;
      instance : instance;
      obligation : obligation;
      failure : failure;
      fixes : fix list;
    }
  | Unreadable of { location : location; construct : construct; foreign : string option }
  | Unevaluated of { path : Path.t; report : string }

let make ?(fixes = []) code location message =
  { code = Prover code; severity = Error; location; message; notes = []; fixes }

let say text = [ Text text ]
let quote_in { key; origin } = Quote (In_definition (key, origin))
let tick quoted = [ Text "`"; quote_in quoted; Text "`" ]

let capitalize = function
  | Text text :: rest -> Text (String.capitalize_ascii text) :: rest
  | pieces -> pieces

let rec show_callee (path : Path.t) =
  match path with
  | Top { name; _ } -> name
  | Method { owner = Impl { for_type; _ } | Derived { type_ = for_type; _ }; name; _ }
  | Method { owner = for_type; name; _ }
  | Member_constant { owner = for_type; name } ->
      show_callee for_type ^ "." ^ name
  | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> Path.show path

let describe_call { at; callee } =
  let call =
    match callee with
    | Some callee -> Printf.sprintf "call to `%s`" (show_callee callee)
    | None -> "call"
  in
  match at with
  | Whole_definition -> [ Text ("a " ^ call) ]
  | Node (Written _) -> [ Text ("this " ^ call) ]
  | Node (Desugared { desugaring; _ } as origin) ->
      let maker =
        match desugaring with
        | For_loop -> [ Text "this `for` loop" ]
        | Quantifier -> [ Text "this quantifier" ]
        | Derived -> [ Text "the derived `"; quote origin; Text "`" ]
        | Rewrite | Try -> [ Text "`"; quote origin; Text "`" ]
      in
      (Text ("the " ^ call ^ " that ") :: maker) @ [ Text " makes" ]

let describe_recursive_call call =
  match call.at with
  | Node (Written _) -> [ Text "This recursive call" ]
  | Node (Desugared _) | Whole_definition -> capitalize (describe_call call)

let join_with_and items =
  let last = List.length items - 1 in
  List.concat
    (List.mapi
       (fun index item ->
         if index = 0 then item
         else Text (if index < last then ", " else if last = 1 then " and " else ", and ") :: item)
       items)

let join separator items =
  List.concat
    (List.mapi (fun index item -> (if index = 0 then [] else [ Text separator ]) @ item) items)

let describe_value = function
  | Named name -> [ Text (Printf.sprintf "`%s`" name) ]
  | Quoted quoted -> tick quoted
  | Temporary -> [ Text "a temporary" ]
  | Self_value -> [ Text "`self`" ]
  | Compiler_local -> [ Text "a local that the compiler introduces" ]
  | Lent_part -> [ Text "a lent part" ]

let describe_invariant_moment = function
  | When_lend_ends -> say "when the lend of this part ends"
  | When_passed call -> Text "when it is passed to " :: describe_call call
  | Lambda_result -> say "for the value this lambda returns"
  | Lambda_mut_parameter -> say "for a `mut` parameter when this lambda ends"
  | Returned_value -> say "for the value returned"
  | Mut_parameter_at_return name -> say (Printf.sprintf "for `%s` when the function returns" name)
  | Self_at_return -> say "for `self` when the method returns"
  | Built_here -> say "for the value built here"
  | At_scope_end value -> (Text "for " :: describe_value value) @ [ Text " when its scope ends" ]
  | Element_changed -> say "for the element changed here"
  | Part_lent -> say "for the part lent here"

let show_moment = function
  | On_entry -> "on entry to the loop"
  | After_iteration -> "after an iteration"
  | Where_left -> "where the loop is left"

let show_requirement = function
  | Room_written -> "have the room it writes into"
  | Elements_mutated -> "have the elements it mutates"
  | Elements_read -> "have the elements it reads"
  | Ends_with_zero -> "end with a zero, which it reads up to"
  | Elements_at_both_indexes -> "have elements at both of its indexes"
  | Length_within_storage -> "be given a length at most the storage's"
  | Element_to_pop -> "have an element to pop"
  | Element_at_index -> "have an element at its index"
  | Index_within_length -> "be given an index at most the storage's length"
  | Range_within_view -> "be given a range within the view"
  | Count_of_array -> "have as many elements as the array's count"

let describe_difference = function
  | Upper_bound -> ("more than", "allows")
  | Exact -> ("more or less than", "states")

let show_promiser = function Trait_promiser -> "trait" | Capability_promiser -> "capability"

let describe_constant_cycle ~cyclic { kind; path; omitted } =
  let cyclic_name = Path.show cyclic in
  let consequence = Printf.sprintf "so `%s` would be computed from itself." cyclic_name in
  let verb, name, part =
    match kind with
    | Reads -> ("reads", Path.show path, "value")
    | Calls -> ("calls", show_callee path, "code")
    | Uses -> ("uses", show_callee path, "code")
  in
  let describe_omitted = function
    | Omitted_field field -> Printf.sprintf "field `%s`" field
    | Omitted_argument parameter -> Printf.sprintf "argument `%s`" parameter
  in
  match (omitted, Path.equal path cyclic) with
  | None, true -> Printf.sprintf "This %s `%s` in its own value, %s" verb name consequence
  | None, false ->
      Printf.sprintf "This %s `%s`, whose %s depends on `%s`, %s" verb name part cyclic_name
        consequence
  | Some omitted, true ->
      Printf.sprintf "This leaves out the %s, whose default %s `%s`, %s" (describe_omitted omitted)
        verb name consequence
  | Some omitted, false ->
      Printf.sprintf
        "This leaves out the %s, whose default %s `%s`. The %s of `%s` depends on `%s`, %s"
        (describe_omitted omitted) verb name part name cyclic_name consequence

let describe_unbounded = function
  | Unstated_costs { metric; callees; editable; counts_units } ->
      let metric = Language.Metric.show metric in
      let quote_callees callees =
        join_with_and
          (List.map (fun callee -> [ Text (Printf.sprintf "`%s`" (show_callee callee)) ]) callees)
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
          (Text " Give " :: recipients) @ [ Text (Printf.sprintf " a %s clause%s." clause example) ]
      in
      (Text "This loop calls " :: quote_callees callees)
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
          Text (Printf.sprintf "The %s of `" cost)
          :: quote_in call
          :: Text ("` depends on " ^ dependency)
          :: join_with_and (List.map describe_value values)
          @ [
              Text
                ", which this loop changes, so the prover cannot bound the cost of an iteration by \
                 the values the loop does not mutate. Give the loop a `cost` clause.";
            ])
  | Unbounded_iteration ->
      say
        "The prover cannot bound the cost of one iteration of this loop by the values the loop \
         does not mutate, so it cannot count the loop's cost: give the loop a `cost` clause."

let describe_promise = function
  | Own_promise { counting; clause } ->
      let difference, verb = describe_difference counting in
      [
        Text (Printf.sprintf "This may spend %s `" difference);
        quote_in clause;
        Text (Printf.sprintf "` %s." verb);
      ]
  | Inherited_promise { counting; promiser; clause } ->
      let difference, verb = describe_difference counting in
      [
        Text
          (Printf.sprintf "This method may spend %s its %s's `" difference (show_promiser promiser));
        quote_in clause;
        Text (Printf.sprintf "` %s." verb);
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
  | Assertion_may_fail { clause } -> tick clause @ [ Text " may not hold." ]
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
      @ Text " may not decrease `"
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
  | Precondition_may_fail { clause; call } ->
      tick clause @ (Text " may not hold for " :: describe_call call) @ [ Text "." ]
  | Precondition_may_panic { clause; call } ->
      tick clause
      @ (Text " may not hold for " :: describe_call call)
      @ [ Text ", so the call may panic." ]
  | Panics_where_ruled_out { call; condition } ->
      capitalize (describe_call call)
      @ Text " may panic where `"
        :: join " && " (List.map (fun part -> [ quote_in part ]) condition)
      @ [ Text "` holds, which the function's `uses Panic unless` rules out." ]
  | Upper_bound_in_exact_cost { metric; call } ->
      Text
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
      Text (Printf.sprintf "The invariant of `%s` may not hold " (Types.show type_))
      :: describe_invariant_moment moment
      @ [ Text "." ]
  | Preserved_invariant { type_; value } ->
      Text (Printf.sprintf "The invariant of `%s` may not hold for " (Types.show type_))
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
      @ (Text " may not hold for " :: describe_call call)
      @ [ Text (Printf.sprintf " through `%s`." name) ]
  | Parameter_contract { path; clause } ->
      [
        Text
          (Printf.sprintf
             "`%s` may not accept every argument this parameter's type promises it: its `"
             (Path.show path));
        quote_in clause;
        Text "` may not hold.";
      ]
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
  | Lent_part_ensures { clause } -> tick clause @ [ Text " may not hold for the part lent here." ]
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
  | Ensures_at_method_end { clause } -> tick clause @ [ Text " may not hold when the method ends." ]
  | Ensures_at_return { clause } ->
      tick clause @ [ Text " may not hold when the function returns." ]
  | Promiser_ensures { promiser; clause } ->
      [
        Text (Printf.sprintf "The %s's `" (show_promiser promiser));
        quote_in clause;
        Text "` may not hold when this method returns.";
      ]
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
  | Callback_requirement { name; reason; clause } ->
      [
        Text
          (Printf.sprintf "`%s` %s, so its `" name
             (match reason with
             | Used_as_unpromising_value ->
                 "is used as a value whose type promises nothing of its arguments"
             | Passed_for_unpromising_parameter ->
                 "is passed for a parameter that may not promise its `requires`"));
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
          | Type_promises_nothing name ->
              Printf.sprintf "and the type of `%s` promises nothing of its results." name
          | Ensures_may_not_promise path ->
              Printf.sprintf "and the `ensures` of `%s` may not promise it." (Path.show path));
      ]
  | Duplicate_key { key } ->
      [
        Text "The key `";
        (match key with Some key -> quote_in key | None -> Text "this key");
        Text "` may equal an earlier key of this map.";
      ]
  | Value_contract { path; type_; clause } ->
      [
        Text
          (Printf.sprintf
             "`%s` is used as a value of `%s`, which promises nothing of its arguments, so its `"
             (Path.show path) (Types.show type_));
        quote_in clause;
        Text "` may not hold.";
      ]

let find_code : obligation -> Diagnostic.Code.prover = function
  | Assertion_may_fail _ | Bit_vector_assertion_may_fail _ | Desugared_assertion_may_fail _ ->
      Assertion
  | Recursion_not_on_part _ | Recursion_may_not_end _ | Uncompared_recursion _
  | Measure_may_not_decrease _ | Recursion_through_impl _ | Recursion_through_supply _
  | Loop_measure_may_not_decrease ->
      Termination
  | Constant_cycle _ -> Constant_cycle
  | Precondition_may_fail _ | Intrinsic_requirement _ | Callback_precondition _
  | Parameter_contract _ | Float_conversion _ | Not_a_scalar_value _ | Impl_precondition _
  | Impl_panic_condition _ | Callback_requirement _ | Value_contract _ ->
      Requires
  | Precondition_may_panic _ | Panics_where_ruled_out _ -> Panic
  | Upper_bound_in_exact_cost _ | Lambda_cost _ | Lambda_call_above_bound _ | Loop_cost_clause _
  | Iteration_above_inferred_bound | Unbounded_iteration_cost _ | Cost_promise _
  | Negative_potential _ ->
      Cost
  | Out_of_bounds _ -> Out_of_bounds
  | Invariant_may_fail _ | Preserved_invariant _ | Derived_default_invariant | Loop_invariant _
  | Visited_out_of_order | Element_count_changes ->
      Invariant
  | Lambda_promise _ | Lent_part_ensures _ | Ensures_at_method_end _ | Ensures_at_return _
  | Promiser_ensures _ | Restated_contract _ | Callback_promise _ ->
      Ensures
  | Out_of_range _ -> Out_of_range
  | Divisor_may_be_zero _ -> Division
  | Division_overflow _ | Overflow _ -> Overflow
  | Shift_amount _ -> Shift
  | Unreachable_reached -> Unreachable
  | Law_may_fail _ -> Law
  | May_alias _ | Duplicate_key _ -> Disjoint

let locate : location -> _ = function Node origin -> at origin | Whole_definition -> At Definition

let describe_path_note = function
  | Arm_taken patterns ->
      (Text "the arm `" :: join ", " (List.map (fun pattern -> [ quote pattern ]) patterns))
      @ [ Text "` is taken" ]
  | Condition_holds { condition; holds } ->
      [ Text "`"; quote condition; Text (Printf.sprintf "` is %b" holds) ]
  | Else_runs pattern -> [ Text "`"; quote pattern; Text "` does not match, so the `else` runs" ]
  | Returns_early tried -> [ Text "`"; quote tried; Text "` returns early" ]

let describe_failed_runs failed_runs =
  List.map
    (function
      | Constant_run { path; report } ->
          Text
            (Printf.sprintf " The evaluation of `%s` stopped, so its value is not known: %s"
               (Path.show path) report)
      | Assertion_run report ->
          Text (Printf.sprintf " Its evaluation stopped, so its result is not known: %s" report))
    failed_runs

let describe_failure = function
  | Refuted -> say " This fails every time the code reaches it."
  | Counterexample { values; path; failed_runs } ->
      (match values with
        | [] -> []
        | values ->
            [
              Text
                (" For example, when "
                ^ String.concat ", "
                    (List.map (fun (name, value) -> Printf.sprintf "`%s` is %s" name value) values)
                ^ ".");
            ])
      @ (match path with
        | [] -> []
        | path ->
            (Text " On that path, " :: join ", " (List.map describe_path_note path)) @ [ Text "." ])
      @ describe_failed_runs failed_runs
  | Undecided { unknown; has_untriggered_fact; failed_runs } ->
      Text
        ((match unknown with
           | Out_of_steps ->
               " The solver reached its step limit before it found a proof or a counterexample."
           | Incomplete reason ->
               Printf.sprintf
                 " The solver's decision procedures are incomplete for this query, so it stopped \
                  without a proof or a counterexample. Z3 gives the reason `%s`."
                 reason)
        ^ " If the code is correct, a `proof` block or a theorem can lead the solver to the proof."
        ^
        if has_untriggered_fact then
          " A quantified fact in the query has no trigger, so an `assert` of that fact at the term \
           the proof needs may be enough."
        else "")
      :: describe_failed_runs failed_runs

let advise_other_ways : Diagnostic.Code.prover -> _ = function
  | Overflow | Division | Shift ->
      say " It can also be checked first with an `if`, or done with the checked operation."
  | Out_of_bounds ->
      say " It can also be checked first with an `if`, or, for one element, read with `get`."
  | _ -> []

let describe_required = function
  | Code code -> Text code
  | Substituted_clause { clause = { key; origin }; replacements; type_names } ->
      Substituted
        {
          clause = In_definition (key, origin);
          replacements =
            List.map (fun (replaced, code) -> (In_definition (key, replaced), code)) replacements;
          type_names;
        }

let describe_fix = function
  | Add_requires { body; required; premise; condition } ->
      let required = List.map describe_required required in
      let required =
        match condition with
        | [] -> required
        | condition -> required @ [ Text (" when " ^ Types.show_condition condition) ]
      in
      let required =
        match premise with
        | Some premise -> (Text ("(" ^ premise ^ ") ==> (") :: required) @ [ Text ")" ]
        | None -> required
      in
      {
        title = (Text "Add `requires " :: required) @ [ Text "`" ];
        edits = [ Add_line_before (Nodes.Node body, Text "requires " :: required) ];
      }
  | Add_panic place ->
      {
        title = say "Add `uses Panic`";
        edits =
          [
            (match place with
            | After_uses uses -> insert_after uses [ Text ", Panic" ]
            | Before_clause first -> insert_before first [ Text "uses Panic\n  " ]
            | Before_body body -> Add_line_before (Nodes.Node body, [ Text "uses Panic" ]));
          ];
      }

let show_construct = function
  | Potential_of_elements -> "the potential of a collection's elements"
  | Metric_of_non_trait_method metric ->
      Printf.sprintf "the %s of a function that is not a trait's method"
        (Language.Metric.show metric)
  | Calls_target -> "this `calls` target"
  | Unsolved_size -> "an unsolved size"
  | Elements_of type_ -> Printf.sprintf "the elements of `%s`" (Types.show type_)
  | Sequence_elements -> "the elements of a sequence"
  | Function_value_costs -> "a function value's costs"
  | Intrinsic_at_parameter { operation; parameter } ->
      Printf.sprintf "`intrinsic.%s` at the type parameter `%s`" operation (Types.show parameter)
  | Negation_of type_ -> Printf.sprintf "negating a value of `%s`" (Types.show type_)
  | Shift_of type_ -> Printf.sprintf "a shift of `%s`" (Types.show type_)
  | Slice_of type_ -> Printf.sprintf "a slice of `%s`" (Types.show type_)
  | Unreadable_parameter_type ->
      "a function passed for a parameter whose type the prover cannot read"
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
        Text
          ("Where "
          ^ String.concat " and "
              (List.map
                 (fun (parameter, builtin) ->
                   Printf.sprintf "`%s` is `%s`" parameter (Language.Builtin_type.show builtin))
                 instance)
          ^ ": ");
      ]

let describe = function
  | Proves { location; instance; obligation } ->
      make (find_code obligation) (locate location)
        (describe_instance instance @ describe_obligation obligation)
  | Unproven { location; instance; obligation; failure; fixes } ->
      let code = find_code obligation in
      make code (locate location) ~fixes:(List.map describe_fix fixes)
        (describe_instance instance @ describe_obligation obligation @ describe_failure failure
       @ advise_other_ways code)
  | Unreadable { location; construct; foreign } ->
      make Unsupported (locate location)
        (say
           (Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
              (match foreign with
              | Some name -> Printf.sprintf "%s, in `%s`" (show_construct construct) name
              | None -> show_construct construct)))
  | Unevaluated { path; report } ->
      make Evaluation (At Definition)
        (say (Printf.sprintf "The value of `%s` cannot be computed: %s" (Path.show path) report))

let describe_citation = function
  | Cited_here -> "This is the clause that must hold."
  | Cited_at { path; line } -> Printf.sprintf " The clause that must hold is at `%s:%d`." path line

let examples : t list =
  [
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Assertion_may_fail { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Bit_vector_assertion_may_fail
            { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Desugared_assertion_may_fail
            { call = { at = Node (example "at"); callee = Some example_path } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_not_on_part
            {
              call = { at = Node (example "at"); callee = Some example_path };
              compared = [ "‹compared›" ];
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_may_not_end
            {
              call = { at = Node (example "at"); callee = Some example_path };
              is_self_call = false;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_may_not_end
            { call = { at = Node (example "at"); callee = Some example_path }; is_self_call = true };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Uncompared_recursion { call = { at = Node (example "at"); callee = Some example_path } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Measure_may_not_decrease
            {
              call = { at = Node (example "at"); callee = Some example_path };
              measures = [ { key = example_key; origin = example "measures" } ];
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_through_impl
            { call = { at = Node (example "at"); callee = Some example_path }; impl = Derives };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_through_impl
            { call = { at = Node (example "at"); callee = Some example_path }; impl = Inherits };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Recursion_through_supply (Named_function example_path);
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_through_supply
            (Bound_through_call
               {
                 call = { at = Node (example "at"); callee = Some example_path };
                 owner = example_path;
               });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Recursion_through_supply
            (Bound_through_name { path = example_path; owner = example_path });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Recursion_through_supply (Provided example_path);
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Constant_cycle
            {
              cyclic = example_path;
              dependency =
                { kind = Reads; path = example_path; omitted = Some (Omitted_field "‹omitted›") };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Precondition_may_fail
            {
              clause = { key = example_key; origin = example "clause" };
              call = { at = Node (example "at"); callee = Some example_path };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Precondition_may_panic
            {
              clause = { key = example_key; origin = example "clause" };
              call = { at = Node (example "at"); callee = Some example_path };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Panics_where_ruled_out
            {
              call = { at = Node (example "at"); callee = Some example_path };
              condition = [ { key = example_key; origin = example "condition" } ];
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Upper_bound_in_exact_cost
            {
              metric = Language.Metric.Time;
              call = { at = Node (example "at"); callee = Some example_path };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Out_of_bounds { at = { key = example_key; origin = example "at" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Room_written };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Elements_mutated };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Elements_read };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Ends_with_zero };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            {
              at = { key = example_key; origin = example "at" };
              requirement = Elements_at_both_indexes;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            {
              at = { key = example_key; origin = example "at" };
              requirement = Length_within_storage;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Element_to_pop };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Element_at_index };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Index_within_length };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Range_within_view };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Intrinsic_requirement
            { at = { key = example_key; origin = example "at" }; requirement = Count_of_array };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = When_lend_ends };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Invariant_may_fail
            {
              type_ = example_type;
              moment = When_passed { at = Node (example "at"); callee = Some example_path };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Lambda_result };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Lambda_mut_parameter };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Returned_value };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Invariant_may_fail { type_ = example_type; moment = Mut_parameter_at_return "‹moment›" };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Self_at_return };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Built_here };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Invariant_may_fail { type_ = example_type; moment = At_scope_end (Named "‹moment›") };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Element_changed };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Invariant_may_fail { type_ = example_type; moment = Part_lent };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Preserved_invariant { type_ = example_type; value = Named "‹value›" };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Preserved_invariant
            { type_ = example_type; value = Quoted { key = example_key; origin = example "value" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Preserved_invariant { type_ = example_type; value = Temporary };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Preserved_invariant { type_ = example_type; value = Self_value };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Preserved_invariant { type_ = example_type; value = Compiler_local };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Preserved_invariant { type_ = example_type; value = Lent_part };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Derived_default_invariant;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_invariant
            { clause = { key = example_key; origin = example "clause" }; moment = On_entry };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_invariant
            { clause = { key = example_key; origin = example "clause" }; moment = After_iteration };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_invariant
            { clause = { key = example_key; origin = example "clause" }; moment = Where_left };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Lambda_promise { promise = { key = example_key; origin = example "promise" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Lambda_cost { counting = Upper_bound; type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Lambda_cost { counting = Exact; type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Lambda_call_above_bound { metric = Language.Metric.Time };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_precondition
            {
              clause = { key = example_key; origin = example "clause" };
              call = { at = Node (example "at"); callee = Some example_path };
              name = "‹name›";
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Parameter_contract
            { path = example_path; clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_cost_clause
            { clause = { key = example_key; origin = example "clause" }; moment = On_entry };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_cost_clause
            { clause = { key = example_key; origin = example "clause" }; moment = After_iteration };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Loop_cost_clause
            { clause = { key = example_key; origin = example "clause" }; moment = Where_left };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Iteration_above_inferred_bound;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Unbounded_iteration_cost
            (Unstated_costs
               {
                 metric = Language.Metric.Time;
                 callees = [ example_path ];
                 editable = [ example_path ];
                 counts_units = false;
               });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Unbounded_iteration_cost
            (Changing_cost
               {
                 is_amortized = false;
                 call = { key = example_key; origin = example "call" };
                 values = [ Named "‹values›" ];
               });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Unbounded_iteration_cost Unbounded_iteration;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Visited_out_of_order;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Loop_measure_may_not_decrease;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Element_count_changes;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Out_of_range { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Divisor_may_be_zero { at = { key = example_key; origin = example "at" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Division_overflow
            { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Overflow { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Shift_amount
            {
              amount = { key = example_key; origin = example "amount" };
              is_operand = false;
              bits = 64;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Shift_amount
            {
              amount = { key = example_key; origin = example "amount" };
              is_operand = true;
              bits = 64;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Float_conversion
            { at = { key = example_key; origin = example "at" }; target = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Not_a_scalar_value { at = { key = example_key; origin = example "at" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Unreachable_reached;
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Lent_part_ensures { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Cost_promise
            (Own_promise
               { counting = Upper_bound; clause = { key = example_key; origin = example "clause" } });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Cost_promise
            (Inherited_promise
               {
                 counting = Upper_bound;
                 promiser = Trait_promiser;
                 clause = { key = example_key; origin = example "clause" };
               });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Cost_promise
            (Restated_promise
               {
                 counting = Upper_bound;
                 for_type = example_type;
                 name = "‹name›";
                 clause = { key = example_key; origin = example "clause" };
                 trait = example_trait;
                 declared = example_trait;
               });
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Impl_precondition { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Impl_panic_condition { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Ensures_at_method_end { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Ensures_at_return { clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Promiser_ensures
            { promiser = Trait_promiser; clause = { key = example_key; origin = example "clause" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Promiser_ensures
            {
              promiser = Capability_promiser;
              clause = { key = example_key; origin = example "clause" };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Law_may_fail { trait = example_trait; law = "‹law›"; for_type = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Restated_contract
            {
              for_type = example_type;
              name = "‹name›";
              clause = { key = example_key; origin = example "clause" };
              trait = example_trait;
              declared = example_trait;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Negative_potential { type_ = example_type };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          May_alias
            {
              first = { key = example_key; origin = example "first" };
              second = { key = example_key; origin = example "second" };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_requirement
            {
              name = "‹name›";
              reason = Used_as_unpromising_value;
              clause = { key = example_key; origin = example "clause" };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_requirement
            {
              name = "‹name›";
              reason = Passed_for_unpromising_parameter;
              clause = { key = example_key; origin = example "clause" };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_promise
            {
              promise = { key = example_key; origin = example "promise" };
              unpromised = Nothing_promises;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_promise
            {
              promise = { key = example_key; origin = example "promise" };
              unpromised = Type_may_not_promise "‹unpromised›";
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_promise
            {
              promise = { key = example_key; origin = example "promise" };
              unpromised = Type_promises_nothing "‹unpromised›";
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Callback_promise
            {
              promise = { key = example_key; origin = example "promise" };
              unpromised = Ensures_may_not_promise example_path;
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Duplicate_key { key = Some { key = example_key; origin = example "key" } };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Duplicate_key { key = None };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Value_contract
            {
              path = example_path;
              type_ = example_type;
              clause = { key = example_key; origin = example "clause" };
            };
        failure =
          Counterexample
            {
              values = [ ("‹name›", "‹value›") ];
              path = [ Condition_holds { condition = example "condition"; holds = true } ];
              failed_runs = [];
            };
        fixes = [];
      };
    Unreadable { location = Node (example "at"); construct = Potential_of_elements; foreign = None };
    Unreadable
      {
        location = Node (example "at");
        construct = Metric_of_non_trait_method Language.Metric.Time;
        foreign = None;
      };
    Unreadable { location = Node (example "at"); construct = Calls_target; foreign = None };
    Unreadable { location = Node (example "at"); construct = Unsolved_size; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Elements_of example_type; foreign = None };
    Unreadable { location = Node (example "at"); construct = Sequence_elements; foreign = None };
    Unreadable { location = Node (example "at"); construct = Function_value_costs; foreign = None };
    Unreadable
      {
        location = Node (example "at");
        construct = Intrinsic_at_parameter { operation = "‹operation›"; parameter = example_type };
        foreign = None;
      };
    Unreadable
      { location = Node (example "at"); construct = Negation_of example_type; foreign = None };
    Unreadable { location = Node (example "at"); construct = Shift_of example_type; foreign = None };
    Unreadable { location = Node (example "at"); construct = Slice_of example_type; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Unreadable_parameter_type; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Unreadable_cursor example_type; foreign = None };
    Unreadable { location = Node (example "at"); construct = Field "‹field›"; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Alternatives_binding_mut; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Hidden_field_of example_type; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Fields_of example_type; foreign = None };
    Unreadable { location = Node (example "at"); construct = Constant_assignment; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Float_literal_without_type; foreign = None };
    Unreadable
      {
        location = Node (example "at");
        construct = Lent_part_outside_lending_method;
        foreign = None;
      };
    Unreadable
      { location = Node (example "at"); construct = Hidden_variant_of example_type; foreign = None };
    Unreadable
      {
        location = Node (example "at");
        construct = Nonreturning_specification_call;
        foreign = None;
      };
    Unreadable
      {
        location = Node (example "at");
        construct = Compiler_restated_method { trait = example_trait; declared_by = example_path };
        foreign = None;
      };
    Unreadable
      { location = Node (example "at"); construct = Literal_of example_type; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Unreadable_function_value; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = String_pattern_on example_type; foreign = None };
    Unreadable
      { location = Node (example "at"); construct = Specification_function; foreign = None };
    Unreadable
      { location = Whole_definition; construct = Calls_target; foreign = Some "‹definition›" };
    Unevaluated { path = example_path; report = "‹report›" };
    Proves
      {
        location = Node (example "at");
        instance = [ ("‹parameter›", Language.Builtin_type.Int64) ];
        obligation = Unreachable_reached;
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Overflow { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure = Refuted;
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Overflow { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Counterexample
            {
              values = [];
              path =
                [
                  Arm_taken [ example "pattern" ];
                  Else_runs (example "pattern");
                  Returns_early (example "tried");
                ];
              failed_runs =
                [
                  Constant_run { path = example_path; report = "‹report›" };
                  Assertion_run "‹report›";
                ];
            };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Overflow { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Undecided { unknown = Out_of_steps; has_untriggered_fact = true; failed_runs = [] };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation =
          Overflow { at = { key = example_key; origin = example "at" }; type_ = example_type };
        failure =
          Undecided
            { unknown = Incomplete "‹reason›"; has_untriggered_fact = false; failed_runs = [] };
        fixes = [];
      };
    Unproven
      {
        location = Node (example "at");
        instance = [];
        obligation = Divisor_may_be_zero { at = { key = example_key; origin = example "at" } };
        failure = Refuted;
        fixes =
          [
            Add_requires
              {
                body = example "body";
                required =
                  [
                    Code "‹code›";
                    Substituted_clause
                      {
                        clause = { key = example_key; origin = example "clause" };
                        replacements = [ (example "argument", "‹code›") ];
                        type_names = [];
                      };
                  ];
                premise = Some "‹premise›";
                condition = example_condition;
              };
            Add_panic (After_uses (example "uses"));
            Add_panic (Before_clause (example "clause"));
            Add_panic (Before_body (example "body"));
          ];
      };
  ]

let list_examples code =
  List.filter (fun example -> (describe example).code = Diagnostic.Code.Prover code) examples
