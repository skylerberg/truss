(* Tests of the core form. Each test checks a program and matches the core
   form of one of its definitions against the property that the test names.
   Every core form a test reads also passes [check_core_invariants], which
   holds the properties that every core form has. *)

open Harness
open Support

(* A core form, with the name that each of its locals is declared with. *)
type form = { core : Core.t; names : (Core.local, string) Hashtbl.t }

let form_of (core : Core.t) = { core; names = Core_walk.local_names core.definition }

let calls_visited walk =
  let calls = ref [] in
  walk
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match node.kind with Call call -> calls := call :: !calls | _ -> ());
    };
  List.rev !calls

(* Every call of a definition, in evaluation order. *)
let calls form = calls_visited (fun visit -> Core_walk.definition visit form.core.definition)

(* Every call in a block, in evaluation order. *)
let block_calls block = calls_visited (fun visit -> Core_walk.block (Core_walk.deep visit) block)
let callees calls = List.map (fun (call : Core.call) -> callee_name call.callee) calls

(* Fails the running test, printing the core form, unless it has the
   property. *)
let check form property =
  if not (property form) then
    fail "found:\n%s\ncallees: %s" (Core_print.show form.core)
      (String.concat ", " (callees (calls form)))

let expect_form test_name load property = test test_name (fun () -> check (load ()) property)

(* The core form of the definition [name] of the program [text], which must
   check without a diagnostic and satisfy the core form's invariants. *)
let definition_form text name =
  let database = setup [ ("app::main", text) ] in
  let file = file_of "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.span 0 0) message)
       (parse_errors database file)
     @ Resolve.diagnostics database file
     @ Interface.diagnostics database file
     @ Infer.diagnostics database file
   with
  | [] -> ()
  | reported ->
      failwith
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)));
  let definition =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if Path.show key.path = "app::main::" ^ name then
          Option.map (fun form -> (key, form)) (Query.demand database Infer.core key)
        else None)
      (Query.demand database Resolve.Names.declarations_in file)
  in
  match definition with
  | Some (key, form) ->
      check_core_invariants database key form;
      form_of form
  | None -> failwith (Printf.sprintf "`%s` has no core form" name)

let expect ?(definition = "g") test_name text property =
  expect_form test_name (fun () -> definition_form text definition) property

(* Parts of a definition *)

let body form : Core.block =
  match form.core.definition with
  | Function { body = Some body; _ } | Law_proof { body; _ } -> body
  | _ -> failwith "the definition has no body"

let contract form : Core.contract =
  match form.core.definition with
  | Function { contract; _ } -> contract
  | _ -> failwith "the definition is not a function"

(* Whether the body's final expression has the property: its value, or the
   last statement of a body that has no value. *)
let ends_with property form =
  match body form with
  | { value = Some value; _ } -> property value
  | { value = None; statements } -> (
      match List.rev statements with
      | { kind = Evaluate value; _ } :: _ -> property value
      | _ -> false)

let name form (local : Core.local) =
  match local with
  | Self -> "self"
  | Named _ | Synthetic _ -> Option.value ~default:"" (Hashtbl.find_opt form.names local)

(* A place written as a local and fields, such as [self.books]. *)
let rec access_path form (place : Core.place) =
  match place with
  | Local { local; _ } -> Some (name form local)
  | Field { base; field; _ } -> Option.map (fun base -> base ^ "." ^ field) (access_path form base)
  | Constant { path; _ } -> Some (Path.show path)
  | Lent _ | Temporary _ -> None

(* Properties of nodes *)

let is_place form path (operand : Core.operand) =
  match operand with Place place -> access_path form place = Some path | Value _ -> false

let is_lent property (operand : Core.operand) =
  match operand with Place (Lent call) -> property call | _ -> false

let is_value property (operand : Core.operand) =
  match operand with Value value -> property value | Place _ -> false

let is_use form path (expression : Core.expression) =
  match expression.kind with Use place -> access_path form place = Some path | _ -> false

let is_use_of local (expression : Core.expression) =
  match expression.kind with Use (Local { local = used; _ }) -> used = local | _ -> false

let is_integer number (expression : Core.expression) =
  match expression.kind with Integer value -> Z.equal value (Z.of_int number) | _ -> false

let is_boolean expected (expression : Core.expression) =
  match expression.kind with Boolean value -> value = expected | _ -> false

let is_string expected (expression : Core.expression) =
  match expression.kind with String text -> text = expected | _ -> false

let is_result (expression : Core.expression) =
  match expression.kind with Result -> true | _ -> false

let is_todo (expression : Core.expression) = match expression.kind with Todo -> true | _ -> false

let is_to_integer property (expression : Core.expression) =
  match expression.kind with
  | Convert { conversion = To_integer; value } -> property value
  | _ -> false

let is_slice property (expression : Core.expression) =
  match expression.kind with Slice { call } -> property call | _ -> false

let is_operator (operation : Intrinsic.operation) operands (expression : Core.expression) =
  match expression.kind with
  | Operator { operation = applied; arguments } ->
      applied = operation
      && List.length arguments = List.length operands
      && List.for_all2 (fun property argument -> property argument) operands arguments
  | _ -> false

let is_compare (comparison : Core.comparison) left right (expression : Core.expression) =
  match expression.kind with
  | Compare { comparison = applied; left = compared; right = against } ->
      applied = comparison && left compared && right against
  | _ -> false

(* An argument passed with the mode, if one is given, whose operand has the
   property. *)
let passed ?mode property (argument : Core.argument) =
  match argument with
  | Passed { mode = parameter; value; _ } ->
      Option.fold ~none:true ~some:(fun mode -> mode = parameter) mode && property value
  | Default -> false

let is_default (argument : Core.argument) =
  match argument with Default -> true | Passed _ -> false

(* A call of the callee [name] with one argument for each property. *)
let call_is name arguments (call : Core.call) =
  callee_name call.callee = name
  && List.length arguments = List.length call.arguments
  && List.for_all2 (fun property argument -> property argument) arguments call.arguments

let is_call name arguments (expression : Core.expression) =
  match expression.kind with Call call -> call_is name arguments call | _ -> false

let lends (mode : Types.mode) (expression : Core.expression) =
  match expression.kind with Call { lends = Some lent; _ } -> lent = mode | _ -> false

let has_evidence (property : Core.evidence -> bool) (expression : Core.expression) =
  match expression.kind with
  | Call { callee = Trait_method { evidence; _ }; _ } -> property evidence
  | _ -> false

let by_impl = has_evidence (function Impl _ -> true | Bound | Dynamic -> false)
let by_bound = has_evidence (function Bound -> true | Impl _ | Dynamic -> false)
let each = "standard::list::impl Iterable for List[Element].each"

(* A call of the [mut self] version of [Index.at] on [collection], which
   lends the element [mut]. *)
let is_mut_index form collection index (expression : Core.expression) =
  is_call "standard::core::Index.at"
    [ passed ~mode:Mut (is_place form collection); passed index ]
    expression
  && lends Mut expression
  &&
  match expression.kind with
  | Call { callee = Trait_method { receiver = Mut; _ }; _ } -> true
  | _ -> false

let is_variant_arm variant (arm : Core.arm) =
  match arm.patterns with
  | [ { kind = Variant { variant = matched; _ }; _ } ] -> matched = variant
  | _ -> false

let is_wildcard_arm (arm : Core.arm) =
  match arm.patterns with [ { kind = Wildcard; _ } ] -> true | _ -> false

let arm_value property (arm : Core.arm) =
  match arm.body.value with Some value -> property value | None -> false

(* The name and mode of every binding of a definition, in evaluation
   order. *)
let bindings form =
  let bound = ref [] in
  Core_walk.definition
    {
      Core_walk.ignore_all with
      pattern =
        (fun (node : Core.pattern) ->
          match node.kind with Bind { name; mode; _ } -> bound := (name, mode) :: !bound | _ -> ());
    }
    form.core.definition;
  List.rev !bound

let capabilities (set : Types.capability_set) =
  List.map
    (function Types.Capability path -> Path.show path | _ -> "a capability that is not named")
    (set :> Types.capability list)

let meters = Fixtures.Core.meters
let shape = Fixtures.Core.shape

(* Operators *)

let () =
  expect "an operator and a method call on built-in integers both become an Operator"
    Fixtures.Core.operator_and_a_method_call_on_built_in_integers (fun form ->
      calls form = []
      && ends_with
           (is_operator Add
              [ is_use form "left"; is_operator Multiply [ is_use form "right"; is_integer 2 ] ])
           form);
  expect "a comparison of built-in integers becomes a Compare"
    Fixtures.Core.comparison_of_built_in_integers_becomes_a_compare (fun form ->
      calls form = []
      && ends_with
           (fun value ->
             match value.kind with
             | And (ordered, nonzero) ->
                 is_compare Less_equal (is_use form "left") (is_use form "right") ordered
                 && is_compare Not_equal (is_use form "left") (is_integer 0) nonzero
             | _ -> false)
           form);
  expect "`<=` on a user type tests the result of `compare`, and `!=` negates a call of `equal`"
    (meters ^ Fixtures.Core.on_a_user_type_tests_the_result_of_compare_and) (fun form ->
      let operands = [ passed (is_place form "first"); passed (is_place form "second") ] in
      ends_with
        (fun value ->
          match value.kind with
          | Or
              ( {
                  kind =
                    Not
                      {
                        kind =
                          Matches
                            {
                              value = Value compare;
                              pattern = { kind = Variant { variant = "Greater"; fields = [] }; _ };
                            };
                        _;
                      };
                  _;
                },
                { kind = Not equal; _ } ) ->
              is_call "standard::core::Ordered.compare" operands compare
              && by_impl compare
              && is_call "standard::core::Equal.equal" operands equal
              && by_impl equal
          | _ -> false)
        form);
  expect "a compound assignment binds its operand, and evaluates its target once"
    Fixtures.Core.compound_assignment_binds_its_operand_and (fun form ->
      List.length (calls form) = 1
      &&
      match (body form).statements with
      | [
       {
         kind =
           Compound_assign
             {
               target = Lent target;
               operand = Value operand;
               bound;
               value =
                 {
                   kind =
                     Operator
                       { operation = Add; arguments = [ { kind = Current_target; _ }; bound_use ] };
                   _;
                 };
             };
         _;
       };
      ] ->
          is_mut_index form "items" (is_value (is_integer 0)) target
          && is_integer 2 operand && is_use_of bound bound_use
      | _ -> false);
  expect ~definition:"g" "arithmetic in a specification converts its operands to Integer"
    Fixtures.Core.arithmetic_in_a_specification_converts_its (fun form ->
      match (contract form).ensures with
      | [ ensured ] ->
          is_compare Greater
            (is_operator Add [ is_to_integer is_result; is_to_integer (is_integer 1) ])
            (is_to_integer (is_use form "count"))
            ensured
      | _ -> false)

(* Calls *)

let () =
  expect "a call has one argument per parameter, in parameter order"
    Fixtures.Core.call_has_one_argument_per_parameter_in_parameter (fun form ->
      ends_with
        (is_call "app::main::connect"
           [ passed (is_value (is_integer 1)); is_default; passed (is_value (is_boolean false)) ])
        form);
  expect "a read-only parameter receives a place, and an `own` parameter receives a value"
    Fixtures.Core.read_only_parameter_receives_a_place_and_an_own (fun form ->
      ends_with
        (is_call "app::main::keep"
           [
             passed ~mode:Own (is_value (is_use form "items"));
             passed ~mode:Read (is_place form "limit");
           ])
        form);
  expect "the first argument of a method call is the receiver"
    Fixtures.Core.first_argument_of_a_method_call_is_the_receiver (fun form ->
      match body form with
      | { statements = [ { kind = Evaluate push; _ } ]; value = Some length } ->
          is_call "standard::list::List.push(mut self)"
            [ passed ~mode:Mut (is_place form "items"); passed ~mode:Own (is_value (is_integer 4)) ]
            push
          && is_call "standard::list::List.length"
               [ passed ~mode:Read (is_place form "items") ]
               length
      | _ -> false);
  expect "a String passed as a StringSlice becomes a call of `slice`"
    Fixtures.Core.string_passed_as_a_stringslice_becomes_a_call_of (fun form ->
      ends_with
        (is_call "app::main::greet"
           [
             passed
               (is_value (is_call "standard::text::String.slice" [ passed (is_place form "name") ]));
           ])
        form);
  expect "a capability method call, and a built-in copy"
    Fixtures.Core.capability_method_call_and_a_built_in_copy (fun form ->
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 {
                   pattern = { kind = Wildcard; _ };
                   value = Value ({ kind = Call { callee = Capability_method _; _ }; _ } as now);
                   _;
                 };
             _;
           };
         ];
       value = Some { kind = Copy copied; _ };
      } ->
          is_call "standard::capabilities::Clock.now" [] now && is_place form "count" copied
      | _ -> false);
  expect "a lambda lists its parameters and its captures"
    Fixtures.Core.lambda_lists_its_parameters_and_its_captures (fun form ->
      let is_lambda (value : Core.expression) =
        match value.kind with
        | Lambda
            {
              parameters = [ { kind = Bind { name = "item"; _ }; _ } ];
              captures = [ { local; _ } ];
              body = { statements = []; value = Some sum };
              _;
            } ->
            name form local = "step"
            && is_operator Add [ is_use form "item"; is_use form "step" ] sum
        | _ -> false
      in
      ends_with
        (is_call "standard::core::Iterable.map"
           [ passed (is_place form "items"); passed (is_value is_lambda) ])
        form)

(* Values *)

let () =
  expect "a constructor lists every field, and marks an omitted field as default"
    (shape ^ Fixtures.Core.constructor_lists_every_field_and_marks_an_omitted)
    (ends_with (fun value ->
         match value.kind with
         | Construct { variant = Some "Square"; fields = [ ("side", Some side); ("label", None) ] }
           ->
             is_value (is_integer 2) side
         | _ -> false));
  expect "a range expression becomes a Range record"
    Fixtures.Core.range_expression_becomes_a_range_record
    (ends_with (fun value ->
         match value.kind with
         | Construct
             {
               variant = None;
               fields =
                 [ ("start", Some start); ("stop", Some stop); ("inclusive", Some inclusive) ];
             } ->
             Types.show value.type_ = "Range[Int64]"
             && is_value (is_integer 1) start
             && is_value (is_integer 5) stop
             && is_value (is_boolean false) inclusive
         | _ -> false));
  expect "an interpolated string becomes a text builder, a call for each piece, and `finish`"
    Fixtures.Core.interpolated_string_becomes_a_text_builder_a_call (fun form ->
      let to_builder = passed ~mode:Mut (is_place form "builder") in
      ends_with
        (fun value ->
          match value.kind with
          | Block
              {
                statements =
                  [
                    {
                      kind =
                        Let
                          {
                            pattern = { kind = Bind { name = "builder"; _ }; _ };
                            value = Value create;
                            _;
                          };
                      _;
                    };
                    { kind = Evaluate name_piece; _ };
                    { kind = Evaluate text_piece; _ };
                    { kind = Evaluate count_piece; _ };
                  ];
                value = Some finish;
              } ->
              is_call "standard::text::TextBuilder.new" [] create
              && is_call "standard::core::Display.display"
                   [ passed (is_place form "name"); to_builder ]
                   name_piece
              && is_call "standard::text::TextBuilder.write(mut self)"
                   [ to_builder; passed (is_value (is_string ": ")) ]
                   text_piece
              && is_call "standard::core::Display.display"
                   [ passed (is_place form "count"); to_builder ]
                   count_piece
              && is_call "standard::text::TextBuilder.finish(own self)"
                   [ passed ~mode:Own (is_value (is_use form "builder")) ]
                   finish
          | _ -> false)
        form);
  expect "a list literal, a slice, and an index" Fixtures.Core.list_literal_a_slice_and_an_index
    (fun form ->
      let pushes_storage element (call : Core.call) =
        call_is "intrinsic::storage_push"
          [
            passed ~mode:Mut (is_place form "storage");
            passed ~mode:Own (is_value (is_integer element));
          ]
          call
      in
      match body form with
      | {
       statements =
         [
           { kind = Let { value = Value { kind = Block literal; _ }; _ }; _ };
           { kind = Let { value = Value slice; _ }; _ };
         ];
       value = Some { kind = Use (Lent index); _ };
      } -> (
          is_slice
            (is_call "standard::list::List.slice_from"
               [ passed (is_place form "numbers"); passed (is_value (is_integer 1)) ])
            slice
          && is_call "standard::core::Index.at"
               [ passed (is_place form "numbers"); passed (is_value (is_integer 0)) ]
               index
          &&
          match block_calls literal with
          | [ capacity; first; second; third; list ] ->
              call_is "intrinsic::storage_with_capacity"
                [ passed (is_value (is_integer 3)) ]
                capacity
              && pushes_storage 1 first && pushes_storage 2 second && pushes_storage 3 third
              && call_is "standard::list::List.from_storage"
                   [ passed ~mode:Own (is_value (is_use form "storage")) ]
                   list
          | _ -> false)
      | _ -> false);
  let expect_inserts test_name text ~collection ~create ~insert entries =
    expect test_name text (fun form ->
        ends_with
          (fun value ->
            match value.kind with
            | Block
                {
                  statements =
                    {
                      kind =
                        Let
                          {
                            pattern = { kind = Bind { name; is_var = true; _ }; _ };
                            value = Value created;
                            _;
                          };
                      _;
                    }
                    :: inserted;
                  value = Some result;
                } ->
                name = collection
                && is_call create [ passed (is_value (is_integer (List.length entries))) ] created
                && List.length inserted = List.length entries
                && List.for_all2
                     (fun (statement : Core.statement) entry ->
                       match statement.kind with
                       | Evaluate call ->
                           is_call insert
                             (passed ~mode:Mut (is_place form collection)
                             :: List.map
                                  (fun element -> passed ~mode:Own (is_value (element form)))
                                  entry)
                             call
                       | _ -> false)
                     inserted entries
                && is_use form collection result
            | _ -> false)
          form)
  in
  expect_inserts "a set literal becomes `with_capacity` and one `insert` per element"
    Fixtures.Core.set_literal_becomes_with_capacity_and_one_insert ~collection:"set"
    ~create:"standard::set::Set.with_capacity" ~insert:"standard::set::Set.insert(mut self)"
    [ [ (fun form -> is_use form "first") ]; [ (fun form -> is_use form "second") ] ];
  expect_inserts "a map literal becomes `with_capacity` and one `insert_absent` per entry"
    Fixtures.Core.map_literal_becomes_with_capacity_and_one_insert ~collection:"map"
    ~create:"standard::map::Map.with_capacity" ~insert:"standard::map::Map.insert_absent(mut self)"
    [
      [ (fun _ -> is_integer 1); (fun _ -> is_integer 2) ];
      [ (fun _ -> is_integer 3); (fun _ -> is_integer 4) ];
    ];
  expect "an empty set literal is the call of `with_capacity`"
    Fixtures.Core.empty_set_literal_is_the_call_of_with_capacity
    (ends_with (is_call "standard::set::Set.with_capacity" [ passed (is_value (is_integer 0)) ]));
  expect "a slice holds the call of `slice_range`, with an inclusive stop as `stop + 1`"
    Fixtures.Core.slice_holds_the_call_of_slice_range_with_an (fun form ->
      ends_with
        (is_slice
           (is_call "standard::list::List.slice_range"
              [
                passed (is_place form "items");
                passed (is_value (is_integer 0));
                passed (is_value (is_operator Add [ is_use form "last"; is_integer 1 ]));
              ]))
        form);
  expect "a slice of a slice calls the slice's `slice_range`"
    Fixtures.Core.slice_of_a_slice_calls_the_slices_slice_range (fun form ->
      ends_with
        (is_slice
           (is_call "standard::list::Slice.slice_range"
              [
                passed (is_place form "items");
                passed (is_value (is_integer 1));
                passed (is_value (is_integer 3));
              ]))
        form);
  expect "a record update lists the replaced fields, and expands the shorthand"
    Fixtures.Core.record_update_lists_the_replaced_fields_and (fun form ->
      ends_with
        (fun value ->
          match value.kind with
          | Record_update { base; updates = [ ([ "port" ], port) ] } ->
              is_use form "config" base && is_use form "port" port
          | _ -> false)
        form)

(* Control flow *)

let () =
  expect "`?` becomes a match that returns the error"
    Fixtures.Core.becomes_a_match_that_returns_the_error (fun form ->
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 {
                   pattern = { kind = Bind { name = "value"; _ }; _ };
                   value =
                     Value
                       { kind = Match { scrutinees = [ Value parsed ]; arms = [ ok; error ] }; _ };
                   _;
                 };
             _;
           };
         ];
       value = Some _;
      } -> (
          is_call "app::main::parse" [ passed (is_place form "text") ] parsed
          && ok.guard = None && error.guard = None
          && (match ok with
            | {
             patterns =
               [
                 {
                   kind =
                     Variant
                       { variant = "Ok"; fields = [ ("value", { kind = Bind { local; _ }; _ }) ] };
                   _;
                 };
               ];
             body = { statements = []; value = Some success };
             _;
            } ->
                is_use_of local success
            | _ -> false)
          &&
          match error with
          | {
           patterns =
             [
               {
                 kind =
                   Variant
                     { variant = "Err"; fields = [ ("error", { kind = Bind { local; _ }; _ }) ] };
                 _;
               };
             ];
           body =
             {
               statements = [];
               value =
                 Some
                   {
                     kind =
                       Return
                         (Some
                            {
                              kind =
                                Construct
                                  {
                                    variant = Some "Err";
                                    fields = [ ("error", Some (Value returned)) ];
                                  };
                              _;
                            });
                     _;
                   };
             };
           _;
          } ->
              is_use_of local returned
          | _ -> false)
      | _ -> false);
  expect "a match on a place borrows the place"
    (shape ^ Fixtures.Core.match_on_a_place_borrows_the_place) (fun form ->
      bindings form = [ ("radius", Read); ("side", Read) ]
      && ends_with
           (fun value ->
             match value.kind with
             | Match { scrutinees = [ scrutinee ]; arms = [ circle; square; rest ] } -> (
                 is_place form "shape" scrutinee && is_variant_arm "Circle" circle
                 && is_variant_arm "Square" square && is_wildcard_arm rest
                 &&
                 match square.guard with
                 | Some guard -> is_compare Greater (is_use form "side") (is_integer 2) guard
                 | None -> false)
             | _ -> false)
           form);
  expect "a `match` or `is` on a value binds `own`, even if the receiver of the call is marked"
    Fixtures.Core.match_or_is_on_a_value_binds_own_even_if_the (fun form ->
      let take =
        is_call "app::main::Queue.take(mut self)" [ passed ~mode:Mut (is_place form "queue") ]
      in
      bindings form = [ ("first", Own); ("second", Own) ]
      &&
      match body form with
      | {
       statements =
         [
           {
             kind =
               Evaluate
                 {
                   kind = If { condition = { kind = Matches { value = Value tested; _ }; _ }; _ };
                   _;
                 };
             _;
           };
         ];
       value = Some { kind = Match { scrutinees = [ Value matched ]; _ }; _ };
      } ->
          take tested && take matched
      | _ -> false);
  expect "`is` becomes a Matches" (shape ^ Fixtures.Core.is_becomes_a_matches) (fun form ->
      match body form with
      | {
       statements =
         [
           {
             kind =
               Evaluate
                 {
                   kind =
                     If
                       {
                         condition =
                           {
                             kind =
                               Matches
                                 {
                                   value;
                                   pattern =
                                     {
                                       kind =
                                         Variant
                                           {
                                             variant = "Circle";
                                             fields = [ ("radius", { kind = Bind _; _ }) ];
                                           };
                                       _;
                                     };
                                 };
                             _;
                           };
                         _;
                       };
                   _;
                 };
             _;
           };
         ];
       value = Some zero;
      } ->
          is_place form "shape" value && is_integer 0 zero
      | _ -> false);
  expect "a `for` loop over a collection calls `each`, and one over a range is an Integer_range"
    Fixtures.Core.for_loop_over_a_collection_calls_each_and_one_over (fun form ->
      match (body form).statements with
      | [
       _;
       { kind = For { iteration = Yielding_call items; mode = Sequential; _ }; _ };
       { kind = For { iteration = Integer_range { start; stop; inclusive = true }; _ }; _ };
       { kind = While _; _ };
      ] ->
          is_call each [ passed ~mode:Read (is_place form "items") ] items
          && is_integer 0 start && is_use form "total" stop
      | _ -> false);
  expect "a `for` loop over the result of a call calls `each` on the result"
    Fixtures.Core.for_loop_over_the_result_of_a_call_calls_each_on (fun form ->
      match (body form).statements with
      | [ { kind = For { iteration = Yielding_call items; _ }; _ } ] ->
          is_call each [ passed (is_value (is_call "app::main::make" [])) ] items
      | _ -> false)

(* Specifications *)

let () =
  expect "a `requires` clause with a quantifier is not executable"
    Fixtures.Core.requires_clause_with_a_quantifier_is_not (fun form ->
      let contract = contract form in
      (match contract.requires with
        | [
         { value = positive; executable = true };
         {
           value = { kind = Quantified { quantifier = Forall; binder = Over_range _; _ }; _ };
           executable = false;
         };
        ] ->
            is_compare Greater (is_use form "limit") (is_integer 0) positive
        | _ -> false)
      && (match contract.ensures with
        | [ ensured ] -> is_compare Greater_equal is_result (is_integer 0) ensured
        | _ -> false)
      &&
      match (body form).statements with
      | [
       {
         kind =
           Proof
             {
               statements = [ { kind = Assert { condition = { executable = true; _ }; _ }; _ } ];
               _;
             };
         _;
       };
      ] ->
          true
      | _ -> false)

(* Other constructs *)

let () =
  expect "a tagged string becomes a call of `from_template`"
    Fixtures.Core.tagged_string_becomes_a_call_of_from_template (fun form ->
      let is_template (value : Core.expression) =
        match value.kind with
        | Construct
            {
              variant = None;
              fields = [ ("literals", Some _); ("parts", Some (Value { kind = Block parts; _ })) ];
            } -> (
            match
              List.filter
                (fun (call : Core.call) -> callee_name call.callee = "intrinsic::storage_push")
                (block_calls parts)
            with
            | [ part ] ->
                call_is "intrinsic::storage_push"
                  [ passed (fun _ -> true); passed ~mode:Own (is_value (is_use form "name")) ]
                  part
            | _ -> false)
        | _ -> false
      in
      ends_with
        (fun value ->
          match value.kind with
          | Template { literals = [ "hey "; "!" ]; call } ->
              is_call "standard::text::FromTemplate.from_template"
                [ passed (is_value is_template) ]
                call
          | _ -> false)
        form);
  expect "a cursor is advanced by a `for` loop or by a call of `next`"
    Fixtures.Core.cursor_is_advanced_by_a_for_loop_or_by_a_call_of (fun form ->
      match (body form).statements with
      | [
       {
         kind =
           Let
             {
               pattern = { kind = Bind { name = "first"; is_var = true; _ }; _ };
               value = Value created;
               _;
             };
         _;
       };
       {
         kind =
           While
             {
               condition =
                 { kind = Matches { value = Value { kind = Cursor_next advanced; _ }; _ }; _ };
               _;
             };
         _;
       };
       { kind = For { iteration = Yielding_call counted; _ }; _ };
       { kind = For { iteration = Cursor { cursor; next = None }; _ }; _ };
      ] ->
          is_call "app::main::count_to" [ passed (is_value (is_integer 3)) ] created
          && access_path form advanced = Some "first"
          && is_call "app::main::count_to" [ passed (is_value (is_integer 2)) ] counted
          && access_path form cursor = Some "first"
      | _ -> false);
  expect "a conversion to `any` records the impl, and a method call on `any` is dynamic"
    Fixtures.Core.conversion_to_any_records_the_impl_and_a_method (fun form ->
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 { value = Value { kind = To_any { value; evidence = Impl { impl; _ }; _ }; _ }; _ };
             _;
           };
         ];
       value = Some first;
      } ->
          is_use form "numbers" value
          && Path.show impl = "app::main::impl Source for Numbers"
          && is_call "app::main::Source.first" [ passed (is_place form "source") ] first
          && has_evidence (function Dynamic -> true | Impl _ | Bound -> false) first
      | _ -> false);
  expect "the result of a `lends mut` method is a place that can be assigned"
    Fixtures.Core.result_of_a_lends_mut_method_is_a_place_that_can (fun form ->
      match (body form).statements with
      | [ { kind = Assign { target = Field { base = Lent cell; field = "state"; _ }; value }; _ } ]
        ->
          is_call "app::main::Grid.cell(mut self)"
            [ passed ~mode:Mut (is_place form "grid"); passed (is_value (is_integer 0)) ]
            cell
          && lends Mut cell && is_integer 4 value
      | _ -> false);
  expect
    "a `mut self` method called on an indexed element indexes with the `mut self` version of `at`"
    Fixtures.Core.mut_self_method_called_on_an_indexed_element (fun form ->
      ends_with
        (is_call "app::main::Worker.reset(mut self)"
           [ passed ~mode:Mut (is_lent (is_mut_index form "workers" (is_place form "index"))) ])
        form);
  expect "a `for` loop over a `mut` element indexes with the `mut self` version of `at`"
    Fixtures.Core.for_loop_over_a_mut_element_indexes_with_the_mut (fun form ->
      match (body form).statements with
      | [
       {
         kind =
           For
             {
               pattern = { kind = Bind { name = "cell"; mode = Mut; _ }; _ };
               iteration = Yielding_call cells;
               _;
             };
         _;
       };
      ] ->
          is_call "standard::list::List.each(mut self)"
            [ passed ~mode:Mut (is_lent (is_mut_index form "rows" (is_value (is_integer 0)))) ]
            cells
      | _ -> false);
  expect ~definition:"Grid.cell(mut self)" "a `lends mut` method yields a mutable place"
    Fixtures.Core.lends_mut_method_yields_a_mutable_place (fun form ->
      match (body form).statements with
      | [ { kind = Yield { mode = Mut; part }; _ } ] ->
          is_lent (is_mut_index form "self.cells" (is_place form "index")) part
      | _ -> false);
  expect ~definition:"Shelf.first" "a yielded constructor lends the places among its fields"
    Fixtures.Core.yielded_constructor_lends_the_places_among_its (fun form ->
      ends_with
        (fun value ->
          match value.kind with
          | If { else_ = Some { statements = [ { kind = Yield { mode = Read; part }; _ } ]; _ }; _ }
            -> (
              List.length (Core_walk.lent_places part) = 1
              &&
              match part with
              | Value
                  {
                    kind =
                      Construct
                        {
                          variant = Some "Some";
                          fields =
                            [
                              ( "value",
                                Some
                                  (Value
                                     {
                                       kind =
                                         Construct
                                           {
                                             variant = None;
                                             fields =
                                               [
                                                 ("title", Some title); ("rest", Some (Value rest));
                                               ];
                                           };
                                       _;
                                     }) );
                            ];
                        };
                    _;
                  } ->
                  is_lent
                    (is_call "standard::core::Index.at"
                       [ passed (is_place form "self.books"); passed (is_value (is_integer 0)) ])
                    title
                  && is_slice (fun _ -> true) rest
              | _ -> false)
          | _ -> false)
        form);
  expect ~definition:"Shelf.numbered(mut self)"
    "a constructor yielded `mut` lends the places that are marked `mut`"
    Fixtures.Core.constructor_yielded_mut_lends_the_places_that_are (fun form ->
      match (body form).statements with
      | [
       _;
       {
         kind =
           While
             {
               body =
                 {
                   statements =
                     [
                       {
                         kind =
                           Yield
                             {
                               mode = Mut;
                               part =
                                 Value
                                   {
                                     kind =
                                       Construct
                                         {
                                           fields =
                                             [
                                               ("index", Some (Value index)); ("title", Some title);
                                             ];
                                           _;
                                         };
                                     _;
                                   };
                             };
                         _;
                       };
                       _;
                     ];
                   _;
                 };
               _;
             };
         _;
       };
      ] ->
          is_use form "index" index
          && is_lent (is_mut_index form "self.books" (is_place form "index")) title
      | _ -> false);
  expect "a quantifier over a collection calls `each` in code, and not in a contract"
    Fixtures.Core.quantifier_over_a_collection_calls_each_in_code (fun form ->
      (match (contract form).ensures with
        | [
         {
           kind =
             Compare
               {
                 comparison = Equal;
                 left;
                 right =
                   {
                     kind =
                       Quantified
                         { quantifier = Exists; binder = Over_collection { collection; _ }; _ };
                     _;
                   };
               };
           _;
         };
        ] ->
            is_result left && is_use form "items" collection
        | _ -> false)
      && ends_with
           (fun value ->
             match value.kind with
             | Quantified { quantifier = Exists; binder = Over_each { call; _ }; _ } ->
                 is_call each [ passed (is_place form "items") ] call
             | _ -> false)
           form);
  expect "a method of `Cursor` on a yielding method's cursor is a call, and `next` is not"
    Fixtures.Core.method_of_cursor_on_a_yielding_methods_cursor_is_a (fun form ->
      let items = is_call each [ passed (is_place form "items") ] in
      (not (List.mem "standard::core::Cursor.next" (callees (calls form))))
      &&
      match body form with
      | {
       statements =
         [
           { kind = Let { value = Value created; _ }; _ };
           { kind = Let { value = Value { kind = Cursor_next cursor; _ }; _ }; _ };
         ];
       value = Some count;
      } ->
          items created
          && access_path form cursor = Some "cursor"
          && is_call "standard::core::Cursor.count"
               [
                 passed ~mode:Own
                   (is_value
                      (is_call "standard::core::Cursor.skip"
                         [ passed ~mode:Own (is_value items); passed (is_value (is_integer 1)) ]));
               ]
               count
      | _ -> false);
  expect "an assignment through an index calls `assign` where the type has it"
    Fixtures.Core.assignment_through_an_index_calls_assign_where_the (fun form ->
      match (body form).statements with
      | [
       _; _; { kind = Evaluate assigned; _ }; { kind = Assign { target = Lent indexed; value }; _ };
      ] ->
          is_call "standard::core::IndexAssign.assign"
            [
              passed ~mode:Mut (is_place form "ports");
              passed ~mode:Own (is_value (is_use form "name"));
              passed ~mode:Own (is_value (is_integer 8080));
            ]
            assigned
          && is_mut_index form "scores" (is_value (is_integer 0)) indexed
          && is_integer 5 value
      | _ -> false);
  expect "patterns of constants, ranges, and strings"
    Fixtures.Core.patterns_of_constants_ranges_and_strings (fun form ->
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 {
                   value =
                     Value
                       {
                         kind =
                           Match
                             {
                               scrutinees = [ count ];
                               arms = [ constant; range; alternatives; rest ];
                             };
                         _;
                       };
                   _;
                 };
             _;
           };
         ];
       value = Some { kind = Match { scrutinees = [ name ]; arms = [ yes; other ] }; _ };
      } -> (
          is_place form "count" count && is_place form "name" name
          && (match constant.patterns with
            | [ { kind = Literal limit; _ } ] -> is_use form "app::main::limit" limit
            | _ -> false)
          && (match range.patterns with
            | [ { kind = Range { start; stop; inclusive = false }; _ } ] ->
                is_integer 0 start && is_integer 5 stop
            | _ -> false)
          && (match alternatives.patterns with
            | [
             { kind = Alternatives [ { kind = Literal seven; _ }; { kind = Literal eight; _ } ]; _ };
            ] ->
                is_integer 7 seven && is_integer 8 eight
            | _ -> false)
          && is_wildcard_arm rest && is_wildcard_arm other
          &&
          match yes.patterns with
          | [ { kind = Equal_to { value; equal }; _ } ] ->
              is_string "yes" value && callee_name equal = "standard::core::Equal.equal"
          | _ -> false)
      | _ -> false);
  expect "a quantifier over a type, and old" Fixtures.Core.quantifier_over_a_type_and_old
    (fun form ->
      match (contract form).ensures with
      | [
       {
         kind =
           Compare
             {
               comparison = Equal;
               left = result;
               right =
                 {
                   kind =
                     Quantified
                       {
                         quantifier = Forall;
                         binder = Over_type { name = "value"; type_; _ };
                         body;
                       };
                   _;
                 };
             };
         _;
       };
       { kind = Compare { comparison = Equal; left = { kind = Old old; _ }; right = current }; _ };
      ] ->
          is_result result
          && Types.show type_ = "Int64"
          && is_compare Equal
               (is_operator Add
                  [ is_to_integer (is_use form "value"); is_to_integer (is_integer 0) ])
               (is_to_integer (is_use form "value"))
               body
          && is_use form "count" old && is_use form "count" current
      | _ -> false)

let () =
  expect "a `mut` parameter receives a slice of a place"
    Fixtures.Core.mut_parameter_receives_a_slice_of_a_place (fun form ->
      ends_with
        (is_call "app::main::sort_part"
           [
             passed ~mode:Mut
               (is_value
                  (is_slice
                     (is_call "standard::list::List.slice_range"
                        [
                          passed (is_place form "items");
                          passed (is_value (is_integer 0));
                          passed (is_value (is_integer 2));
                        ])));
           ])
        form)

(* Holes *)

let () =
  let is_discarded property (statement : Core.statement) =
    match statement.kind with
    | Let { pattern = { kind = Wildcard; _ }; value; else_ = None } -> property value
    | _ -> false
  in
  expect "a use of a local whose type is a hole is a Todo, and a pattern on a hole is a Wildcard"
    Fixtures.Core.use_of_a_local_whose_type_is_a_hole_is_a_todo_and (fun form ->
      match body form with
      | { statements = [ hole ]; value = Some value } ->
          is_discarded (is_value is_todo) hole && is_todo value
      | _ -> false);
  expect "an operation on a hole evaluates its operands and ends in a Todo"
    Fixtures.Core.operation_on_a_hole_evaluates_its_operands_and (fun form ->
      match body form with
      | {
       statements = [ hole ];
       value =
         Some { kind = Block { statements = [ receiver; argument; added ]; value = Some value }; _ };
      } ->
          is_discarded (is_value is_todo) hole
          && is_discarded (is_value is_todo) receiver
          && is_discarded (is_place form "count") argument
          && is_discarded (is_value (is_integer 1)) added
          && is_todo value
      | _ -> false);
  List.iter
    (fun statement ->
      test (Printf.sprintf "`%s` on a hole has a core form" statement) (fun () ->
          no_diagnostics
            ~check:(fun database module_ ->
              Resolve.diagnostics database module_
              @ Interface.diagnostics database module_
              @ Infer.diagnostics database module_)
            [
              ( "app::main",
                "type Config(port: Int64)\n\n\
                 fn take(count: Int64) -> Int64 {\n\
                \  count\n\
                 }\n\n\
                 fn g(items: List[Int64], config: Config) -> Int64 {\n\
                \  var hole = todo\n\
                \  " ^ statement ^ "\n  config.port\n}\n" );
            ]))
    [
      "let member = hole.field";
      "let called = hole(1, items)";
      "let result = hole.method(items)";
      "let mapped = items.map(fn(item) { item + hole })";
      "let indexed = hole[0]";
      "let sliced = hole[1..]";
      "let sum = hole + 1";
      "let negated = -hole";
      "let same = hole == 1";
      "let less = 1 < hole";
      "let tried = hole?";
      "let updated = hole with (port: 1)";
      "let text = \"${hole} and ${items.length()}\"";
      "let listed = [hole, hole]";
      "let passed = take(hole)";
      "let chosen = if hole is Some(inner) { inner } else { 0 }";
      "let matched = match hole {\n    Some(inner) if inner > 0 => inner\n    _ => 0\n  }";
      "let Some(bound) = hole else { return 0 }";
      "for item in hole {\n    let _ = item\n  }";
      "hole.field = 1";
      "hole += 1";
      "hole = 2";
      "while hole is Some(inner) {\n    let _ = inner\n  }";
      "let shown = echo hole";
      "let field = Config(port: hole)";
    ]

(* Capabilities *)

let () =
  let apply = Fixtures.Core.apply in
  (* A call of [apply] whose capability argument is [{Console}], and whose
     argument has the property. *)
  let applies property (value : Core.expression) =
    match value.kind with
    | Call { callee = Function { type_arguments = [ Capabilities granted ]; _ }; _ } ->
        capabilities granted = [ "standard::capabilities::Console" ]
        && is_call "app::main::apply" [ passed (is_value property) ] value
    | _ -> false
  in
  expect "a capability parameter is inferred as the set of capabilities the argument uses"
    (apply ^ Fixtures.Core.capability_parameter_is_inferred_as_the_set_of)
    (ends_with
       (applies (fun lambda ->
            match lambda.kind with
            | Lambda { body; _ } ->
                callees (block_calls body)
                = [ "standard::capabilities::Console.print_line"; "standard::text::String.slice" ]
            | _ -> false)));
  expect "a named function passed for a capability-generic parameter is a Function_value"
    (apply ^ Fixtures.Core.named_function_passed_for_a_capability_generic)
    (ends_with
       (applies (fun shout ->
            match shout.kind with
            | Function_value { path; _ } -> Path.show path = "app::main::shout"
            | _ -> false)));
  test "a call's `uses` and a lambda's type contain the inferred set, not the callee's parameter"
    (fun () ->
      let text = apply ^ Fixtures.Core.calls_uses_and_a_lambdas_type_contain_the_inferred in
      let database = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = Function { path; _ }; uses; _ }
                          when Path.show path = "app::main::apply" ->
                            actual :=
                              ("needs " ^ Types.show_argument (Capabilities uses)) :: !actual
                        | Lambda _ -> actual := Types.show node.type_ :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !actual <> [ "(fn() uses Console)"; "needs {Console}" ] then
        fail "found [%s]" (String.concat "; " !actual));
  test "a capability parameter in a result type is inferred separately for each call" (fun () ->
      let text = Fixtures.Core.capability_parameter_in_a_result_type_is_inferred in
      let database = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    pattern =
                      (fun (node : Core.pattern) ->
                        match node.kind with
                        | Bind { name; _ } ->
                            actual := (name ^ ": " ^ Types.show node.type_) :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !actual <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then fail "found [%s]" (String.concat "; " !actual))

(* Origins *)

let () =
  test "a node's origin gives its source span" (fun () ->
      let text = Fixtures.Core.nodes_origin_gives_its_source_span in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | Some form, Some spans, Some written ->
              let actual = ref [] in
              Core_walk.definition
                {
                  Core_walk.ignore_all with
                  statement =
                    (fun (node : Core.statement) ->
                      match node.kind with
                      | Compound_assign _ ->
                          let span = spans.(node.origin) in
                          actual :=
                            String.sub written span.start (span.stop - span.start) :: !actual
                      | _ -> ());
                }
                form.definition;
              if !actual <> [ "total += item" ] then fail "found [%s]" (String.concat "; " !actual)
          | _ -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

let () =
  expect "a cost clause names its resource" Fixtures.Core.cost_clause_names_its_resource
    (fun form ->
      let length = is_call "standard::list::List.length" [ passed (is_place form "items") ] in
      match (contract form).costs with
      | [
       { resource = Calls (Function_parameter visit); bound = Exactly calls_of_visit; _ };
       { resource = Calls (Capability_method (clock, "now")); bound = At_most most; _ };
       { resource = Time; bound = Order_of time; _ };
      ] ->
          name form visit = "visit"
          && length calls_of_visit
          && Path.show clock = "standard::capabilities::Clock"
          && is_integer 1 most
          && is_operator Multiply
               [
                 is_to_integer length;
                 (fun (visited : Core.expression) ->
                   match visited.kind with
                   | Specification_function { function_ = Time; arguments = [ function_value ] } ->
                       is_use form "visit" function_value
                   | _ -> false);
               ]
               time
      | _ -> false)

let () =
  let is_specification_function (function_ : Core.specification_function) arguments
      (expression : Core.expression) =
    match expression.kind with
    | Specification_function { function_ = applied; arguments = given } ->
        applied = function_
        && List.length given = List.length arguments
        && List.for_all2 (fun property argument -> property argument) arguments given
    | _ -> false
  in
  expect "`log` and `power` are specification functions outside a cost bound too"
    Fixtures.Core.log_and_power_are_specification_functions_outside (fun form ->
      match (contract form).ensures with
      | [ logarithm; exponential ] ->
          is_compare Less_equal (is_to_integer is_result)
            (is_operator Add
               [ is_specification_function Log [ is_use form "value" ]; is_integer 1 ])
            logarithm
          && is_compare Greater_equal
               (is_specification_function Power [ is_integer 2; is_result ])
               (is_integer 1) exponential
      | _ -> false);
  expect "a function of the file named `power` is called in a specification"
    Fixtures.Core.function_of_the_file_named_power_is_called_in_a (fun form ->
      match (contract form).ensures with
      | [ ensured ] ->
          is_compare Equal is_result
            (is_call "app::main::power"
               [ passed (is_place form "value"); passed (is_value (is_integer 1)) ])
            ensured
      | _ -> false);
  expect "the time of a method of a type parameter's bound names the trait method"
    Fixtures.Core.time_of_a_method_of_a_type_parameters_bound_names (fun form ->
      match (contract form).costs with
      | [ { resource = Time; bound = Order_of time; _ } ] ->
          is_operator Multiply
            [
              (fun _ -> true);
              (fun (method_time : Core.expression) ->
                match method_time.kind with
                | Method_time
                    (Trait_method
                       {
                         name = "equal";
                         evidence = Bound;
                         self_type = Parameter { name = "Element"; _ };
                         _;
                       }) ->
                    true
                | _ -> false);
            ]
            time
      | _ -> false);
  test "in a trait, `time(Self.method)` names the trait's own method" (fun () ->
      no_diagnostics
        ~check:(fun database module_ ->
          Resolve.diagnostics database module_
          @ Interface.diagnostics database module_
          @ Infer.diagnostics database module_)
        [ ("app::main", Fixtures.Core.in_a_trait_time_self_method_names_the_traits_own) ])

let () =
  test "the origin of a cost is its cost clause" (fun () ->
      let text = Fixtures.Core.origin_of_a_cost_is_its_cost_clause in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | ( Some { definition = Function { contract = { costs = [ cost ]; _ }; _ }; _ },
              Some spans,
              Some written ) ->
              let span = spans.(cost.origin) in
              let quoted = String.sub written span.start (span.stop - span.start) in
              if quoted <> "cost time O(items.length())" then fail "found `%s`" quoted
          | _ -> fail "no core form with exactly one cost")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

(* The standard library's core forms satisfy the invariants. *)

let () =
  let database = setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      test
        (Printf.sprintf "%s's core forms satisfy the invariants" (Path.show_file file))
        (fun () -> forms := !forms + check_file_core_invariants database file))
    Standard_library.files;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

(* Derived methods *)

(* The core form of the method [name] of the derived impl of [trait] for
   the type [type_name] of [app::main]. *)
let derived_method text type_name trait name receiver () =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  let path : Path.t =
    Method
      {
        owner =
          Derived
            {
              type_ = Top { module_; name = type_name };
              trait =
                List.find
                  (fun (path : Path.t) ->
                    match path with Top { name; _ } -> name = trait | _ -> false)
                  (List.map Well_known.path Well_known.For_testing.all);
            };
        name;
        receiver;
      }
  in
  match Query.demand database Infer.derived path with
  | Some form ->
      check_core_invariants database { module_; path; ordinal = 0 } form;
      form_of form
  | None -> failwith "the derived method has no core form"

let expect_derived test_name text type_name trait name receiver property =
  expect_form test_name (derived_method text type_name trait name receiver) property

let pair =
  "type Pair[Second](first: Int64, second: Second)\n  derives Equal, Hash, Ordered, Default\n\n"

let light = Fixtures.Core.light
let reading = Fixtures.Core.reading
let signal = Fixtures.Core.signal

(* The arms of a [match] on [self], one for each variant of [Light] in
   declaration order. *)
let light_arms form =
  match (body form).value with
  | Some { kind = Match { scrutinees = [ scrutinee ]; arms = [ off; dim; on ] }; _ }
    when is_place form "self" scrutinee && is_variant_arm "Off" off && is_variant_arm "Dim" dim
         && is_variant_arm "On" on ->
      Some (off, dim, on)
  | _ -> None

let () =
  expect_derived "a record's derived equal compares each field" pair "Pair" "Equal" "equal" Read
    (fun form ->
      let compares field =
        is_call "standard::core::Equal.equal"
          [ passed (is_place form ("self." ^ field)); passed (is_place form ("other." ^ field)) ]
      in
      ends_with
        (fun value ->
          match value.kind with
          | And (first, second) ->
              compares "first" first && by_impl first && compares "second" second && by_bound second
          | _ -> false)
        form);
  expect_derived
    "a sum type's derived equal compares the fields of matching variants, and is false for \
     different variants"
    light "Light" "Equal" "equal" Read (fun form ->
      let tests_other variant =
        arm_value (fun value ->
            match value.kind with
            | Matches { value; pattern = { kind = Variant { variant = tested; fields = [] }; _ } }
              ->
                tested = variant && is_place form "other" value
            | _ -> false)
      in
      match light_arms form with
      | Some (off, dim, on) ->
          tests_other "Off" off && tests_other "On" on
          && arm_value
               (fun value ->
                 match value.kind with
                 | Match { scrutinees = [ other ]; arms = [ same; different ] } ->
                     is_place form "other" other && is_variant_arm "Dim" same
                     && arm_value
                          (is_call "standard::core::Equal.equal"
                             [
                               passed (is_place form "level"); passed (is_place form "other_level");
                             ])
                          same
                     && is_wildcard_arm different
                     && arm_value (is_boolean false) different
                 | _ -> false)
               dim
      | None -> false);
  expect_derived "a derived hash writes the variant's index and then each field" light "Light"
    "Hash" "hash" Read (fun form ->
      let hasher = passed ~mode:Mut (is_place form "hasher") in
      let writes index =
        call_is "standard::core::Hasher.write(mut self)"
          [ hasher; passed (is_value (is_integer index)) ]
      in
      match light_arms form with
      | Some (off, dim, on) -> (
          (match block_calls off.body with [ write ] -> writes 0 write | _ -> false)
          && (match block_calls on.body with [ write ] -> writes 2 write | _ -> false)
          &&
          match block_calls dim.body with
          | [ write; level ] ->
              writes 1 write
              && call_is "standard::core::Hash.hash"
                   [ passed (is_place form "level"); hasher ]
                   level
          | _ -> false)
      | None -> false);
  expect_derived
    "a record's derived compare compares the next field only if the previous fields are equal" pair
    "Pair" "Ordered" "compare" Read (fun form ->
      let compares field =
        is_call "standard::core::Ordered.compare"
          [ passed (is_place form ("self." ^ field)); passed (is_place form ("other." ^ field)) ]
      in
      ends_with
        (fun value ->
          match value.kind with
          | Match { scrutinees = [ Value first ]; arms = [ equal; decided ] } -> (
              compares "first" first && by_impl first && is_variant_arm "Equal" equal
              && arm_value (fun next -> compares "second" next && by_bound next) equal
              &&
              match decided with
              | {
               patterns = [ { kind = Bind { local; mode = Own; _ }; _ } ];
               body = { statements = []; value = Some result };
               _;
              } ->
                  is_use_of local result
              | _ -> false)
          | _ -> false)
        form);
  expect_derived "a sum type's derived compare orders by variant index, then by fields" light
    "Light" "Ordered" "compare" Read (fun form ->
      let variants = [ (0, "Off"); (1, "Dim"); (2, "On") ] in
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 {
                   pattern = { kind = Bind { local = theirs; _ }; _ };
                   value = Value { kind = Match { scrutinees = [ other ]; arms = indices }; _ };
                   _;
                 };
             _;
           };
         ];
       value = Some { kind = Match { scrutinees = [ self ]; arms }; _ };
      }
        when List.length indices = 3 && List.length arms = 3 ->
          is_place form "other" other && is_place form "self" self
          && List.for_all2
               (fun (index, variant) arm ->
                 is_variant_arm variant arm && arm_value (is_integer index) arm)
               variants indices
          && List.for_all2
               (fun (index, variant) arm ->
                 is_variant_arm variant arm
                 && arm_value
                      (fun value ->
                        match value.kind with
                        | Match { scrutinees = [ other ]; arms = [ same; different ] } ->
                            is_place form "other" other && is_variant_arm variant same
                            && arm_value
                                 (fun ordered ->
                                   if variant = "Dim" then
                                     is_call "standard::core::Ordered.compare"
                                       [
                                         passed (is_place form "level");
                                         passed (is_place form "other_level");
                                       ]
                                       ordered
                                   else
                                     match ordered.kind with
                                     | Construct { variant = Some "Equal"; fields = [] } -> true
                                     | _ -> false)
                                 same
                            && is_wildcard_arm different
                            && arm_value
                                 (fun ordered ->
                                   match ordered.kind with
                                   | If { condition; _ } ->
                                       is_compare Less (is_integer index) (is_use_of theirs)
                                         condition
                                   | _ -> false)
                                 different
                        | _ -> false)
                      arm)
               variants arms
      | _ -> false);
  expect_derived "a derived default calls `default` for each field" pair "Pair" "Default" "default"
    Static
    (ends_with (fun value ->
         match value.kind with
         | Construct
             {
               variant = None;
               fields = [ ("first", Some (Value first)); ("second", Some (Value second)) ];
             } ->
             is_call "standard::core::Default.default" [] first
             && by_impl first
             && is_call "standard::core::Default.default" [] second
             && by_bound second
         | _ -> false));
  expect_derived "a record's derived serialize writes each field by name, in declaration order"
    reading "Reading" "Serialize" "serialize" Read (fun form ->
      let sink = passed ~mode:Mut (is_place form "sink") in
      let serializer method_ = "standard::serialization::Serializer." ^ method_ in
      match calls form with
      | [ begin_record; sensor_field; sensor; value_field; value; end_record ] ->
          call_is (serializer "begin_record")
            [ sink; passed (is_value (is_integer 2)) ]
            begin_record
          && call_is (serializer "field")
               [ sink; passed (is_value (is_string "sensor")) ]
               sensor_field
          && call_is "standard::serialization::Serialize.serialize"
               [ passed (is_place form "self.sensor"); sink ]
               sensor
          && call_is (serializer "field")
               [ sink; passed (is_value (is_string "value")) ]
               value_field
          && call_is "standard::serialization::Serialize.serialize"
               [ passed (is_place form "self.value"); sink ]
               value
          && call_is (serializer "end_record") [ sink ] end_record
      | _ -> false);
  expect_derived "a record's derived deserialize reads a field with a default only if it is present"
    reading "Reading" "Deserialize" "deserialize" Static (fun form ->
      let reads function_ field =
        match
          List.filter (fun (call : Core.call) -> callee_name call.callee = function_) (calls form)
        with
        | [ read ] ->
            call_is function_
              [ passed ~mode:Mut (is_place form "source"); passed (is_value (is_string field)) ]
              read
        | _ -> false
      in
      reads "standard::serialization::required" "sensor"
      && reads "standard::serialization::optional" "value"
      && Core_walk.block_exists
           ~expression:(fun (node : Core.expression) ->
             match node.kind with
             | Construct { variant = None; fields = [ ("sensor", Some _); ("value", None) ] } ->
                 true
             | _ -> false)
           (body form)
      && Core_walk.block_exists
           ~statement:(fun (node : Core.statement) ->
             match node.kind with
             | Assign { target; _ } -> access_path form target = Some "built.value"
             | _ -> false)
           (body form));
  expect_derived "a sum type's derived serialize writes the variant's name, then its fields" signal
    "Signal" "Serialize" "serialize" Read (fun form ->
      let sink = passed ~mode:Mut (is_place form "sink") in
      let serializer method_ = "standard::serialization::Serializer." ^ method_ in
      let begins variant index =
        call_is (serializer "begin_variant")
          [ sink; passed (is_value (is_string variant)); passed (is_value (is_integer index)) ]
      in
      ends_with
        (fun value ->
          match value.kind with
          | Match { scrutinees = [ self ]; arms = [ off; level ] } -> (
              is_place form "self" self && is_variant_arm "Off" off && is_variant_arm "Level" level
              && (match block_calls off.body with
                | [ begin_variant; end_variant ] ->
                    begins "Off" 0 begin_variant
                    && call_is (serializer "end_variant") [ sink ] end_variant
                | _ -> false)
              &&
              match block_calls level.body with
              | [ begin_variant; field; serialized; end_variant ] ->
                  begins "Level" 1 begin_variant
                  && call_is (serializer "field")
                       [ sink; passed (is_value (is_string "value")) ]
                       field
                  && call_is "standard::serialization::Serialize.serialize"
                       [ passed (is_place form "value"); sink ]
                       serialized
                  && call_is (serializer "end_variant") [ sink ] end_variant
              | _ -> false)
          | _ -> false)
        form);
  expect_derived "a sum type's derived deserialize reads the variant by its name" signal "Signal"
    "Deserialize" "deserialize" Static (fun form ->
      let source = passed ~mode:Mut (is_place form "source") in
      let ends_variant (arm : Core.arm) =
        List.mem "standard::serialization::Deserializer.end_variant"
          (callees (block_calls arm.body))
      in
      let is_name_arm variant (arm : Core.arm) =
        match arm.patterns with
        | [ { kind = Equal_to { value; _ }; _ } ] -> is_string variant value && ends_variant arm
        | _ -> false
      in
      match body form with
      | {
       statements =
         [
           {
             kind =
               Let
                 {
                   pattern = { kind = Bind { name = "name"; _ }; _ };
                   value = Value { kind = Match { scrutinees = [ Value variant ]; _ }; _ };
                   _;
                 };
             _;
           };
         ];
       value = Some { kind = Match { scrutinees = [ name ]; arms = [ off; level; unknown ] }; _ };
      } ->
          is_call "standard::serialization::Deserializer.variant" [ source ] variant
          && is_place form "name" name && is_name_arm "Off" off && is_name_arm "Level" level
          && is_wildcard_arm unknown
          && callees (block_calls unknown.body) = [ "standard::serialization::unknown_variant" ]
      | _ -> false);
  test "a `todo` type has no derived core form" (fun () ->
      let database = setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
      let path : Path.t =
        Method
          {
            owner =
              Derived
                {
                  type_ = Top { module_ = module_of "app::main"; name = "Later" };
                  trait = Well_known.path Equal;
                };
            name = "equal";
            receiver = Read;
          }
      in
      if Query.demand database Infer.derived path <> None then fail "it has a core form");
  test
    "every method of a derived impl in the standard library has a core form that satisfies the \
     invariants" (fun () ->
      let database = setup [] in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (Query.demand database Interface.Impls.index Path.standard_package)
      in
      if derived = [] then fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Impls.impl_interface database impl with
          | None -> fail "`%s` has no interface" (Path.show impl)
          | Some interface ->
              let provided =
                match
                  Query.demand database Interface.Environment.trait_interface
                    interface.implements.trait
                with
                | Some trait ->
                    List.filter_map
                      (fun (method_ : Types.trait_method) ->
                        if method_.provided then Some method_.method_name else None)
                      trait.methods
                | None -> []
              in
              List.iter
                (fun (name, receiver, _) ->
                  let path : Path.t = Method { owner = impl; name; receiver } in
                  match Query.demand database Infer.derived path with
                  | Some form -> (
                      match impl with
                      | Derived { type_ = Top { module_; _ }; _ } ->
                          check_core_invariants database { module_; path; ordinal = 0 } form
                      | _ -> fail "`%s` is not derived for a top-level type" (Path.show impl))
                  | None ->
                      if not (List.mem name provided) then
                        fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      fail "`%s`, `%s`: %s" (Path.show impl) name (Compiler_bug.to_string bug))
                interface.impl_methods)
        derived)

(* [Infer.core_of_path] *)

let () =
  let text = Fixtures.Core.described_both in
  let both : Path.t = Top { module_ = module_of "app::main"; name = "Both" } in
  let described : Types.trait_reference =
    {
      trait = Top { module_ = module_of "app::main"; name = "Described" };
      trait_arguments = [];
      associated = [];
    }
  in
  let core_of_method name =
    let database = setup [ ("app::main", text) ] in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let bounds (actual : Types.parameter) = if actual = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.implements database ~bounds
          (Types.named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match Query.demand database Infer.core_of_path (Method { owner; name; receiver = Read }) with
    | Some (form, substitution) ->
        ( form_of form,
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            substitution )
    | None -> failwith "no core form"
  in
  (* A call of [Described.describe] through the bound on [self_type]. *)
  let describes self_type receiver (call : Core.expression) =
    is_call "app::main::Described.describe" [ passed receiver ] call
    &&
    match call.kind with
    | Call { callee = Trait_method { evidence = Bound; self_type = Parameter { name; _ }; _ }; _ }
      ->
        name = self_type
    | _ -> false
  in
  test "a method defined in an impl has its own core form" (fun () ->
      let form, substitution = core_of_method "describe" in
      if substitution <> [] then
        fail "found the substitution [%s]" (String.concat "; " substitution);
      check form (fun form -> ends_with (describes "Value" (is_place form "self.first")) form));
  test
    "a method inherited from a trait has the default method's core form and a substitution for Self"
    (fun () ->
      let form, substitution = core_of_method "twice" in
      if substitution <> [ "Self = Both[Value]" ] then
        fail "found the substitution [%s]" (String.concat "; " substitution);
      check form (fun form ->
          let describes_self = describes "Self" (is_place form "self") in
          ends_with (is_operator Add [ describes_self; describes_self ]) form));
  test "a method of a derived impl has the generated core form" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let owner : Path.t = Derived { type_ = both; trait = Well_known.path Equal } in
      match
        ( Query.demand database Infer.core_of_path
            (Method { owner; name = "equal"; receiver = Read }),
          Query.demand database Infer.core_of_path
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, []), Some (_, [ _ ]) -> ()
      | _ ->
          fail "expected the derived method with no substitution and the inherited method with one")

(* A law's proof *)

let () =
  expect ~definition:"proof Ordered.agrees_with_equal for Pair"
    "a law's proof has the law's parameters, with the proof's type for Self"
    (Fixtures.Core.pair_ordering
   ^ "proof Ordered.agrees_with_equal for Pair {\n  only_equal(first, second: second)\n}\n")
    (fun form ->
      match form.core.definition with
      | Law_proof { parameters = [ first; second ]; _ } ->
          first.local = Synthetic 0 && second.local = Synthetic 1 && first.name = "first"
          && second.name = "second"
          && Types.show first.type_ = "Pair"
          && Types.show second.type_ = "Pair"
          && ends_with
               (is_call "app::main::only_equal"
                  [ passed (is_place form "first"); passed (is_place form "second") ])
               form
      | _ -> false)

(* [Infer.For_testing.specification] *)

let () =
  let specification text name =
    let database = setup [ ("app::main", text) ] in
    let actual =
      List.find_map
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::" ^ name then
            Option.map
              (fun form -> (database, key, form))
              (Query.demand database Infer.For_testing.specification key)
          else None)
        (Query.demand database Resolve.Names.declarations (module_of "app::main"))
    in
    match actual with
    | Some actual -> actual
    | None -> failwith (Printf.sprintf "`%s` has no specification" name)
  in
  let equal first second name =
    let _, _, first = specification first name and _, _, second = specification second name in
    first = second
  in
  let bump body =
    "fn bump(counter: mut Int64, by: Int64)\n  requires by > 0\n  cost time O(1)\n{\n  " ^ body
    ^ "\n}\n"
  in
  let double body = "fn double(value: Int64) -> Int64\n  cost time O(1)\n{\n  " ^ body ^ "\n}\n" in
  test "editing the body of a function that mutates an argument leaves its specification equal"
    (fun () ->
      if not (equal (bump "counter += by") (bump "counter = counter + by + 0") "bump") then
        fail "the specification changed");
  test "editing the body of a function without a time clause leaves its specification equal"
    (fun () ->
      let slow body = "fn slow(value: Int64) -> Int64 {\n  " ^ body ^ "\n}\n" in
      if not (equal (slow "value") (slow "let same = value\n  same") "slow") then
        fail "the specification changed");
  test "editing a clause changes the specification" (fun () ->
      if
        equal (bump "counter += by") Fixtures.Core.editing_a_clause_changes_the_specification "bump"
      then fail "the specification did not change");
  test "editing the body of a function leaves its specification equal" (fun () ->
      if not (equal (double "value + value") (double "value * 2") "double") then
        fail "the specification changed");
  test "a specification without its body meets the core form's invariants" (fun () ->
      let database, key, form = specification (bump "counter += by") "bump" in
      (match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
      check_core_invariants database key form);
  test "the specification that other packages read has no function's body" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "public fn double(value: Int64) -> Int64\n  cost time O(1)\n{\n  value + value\n}\n"
            );
          ]
      in
      match
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            Query.demand database Infer.For_testing.exported_specification
              (Resolve.Names.key_of declaration))
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      with
      | Some { definition = Function { body = None; _ }; _ } -> ()
      | _ -> fail "the body of a function is in the exported specification");
  test "a theorem's specification has no body" (fun () ->
      let _, _, form = specification Fixtures.Core.theorems_specification_has_no_body "doubled" in
      match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
  test "the body that a trait provides for a method is in the method's specification" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Core.body_that_a_trait_provides_for_a_method_is_in_the) ]
      in
      let actual =
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            match declaration.path with
            | Method { name = "bump"; _ } ->
                Query.demand database Infer.For_testing.specification
                  (Resolve.Names.key_of declaration)
            | _ -> None)
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      in
      match actual with
      | Some { definition = Function { body = Some _; _ }; _ } -> ()
      | _ -> fail "the provided body is not in the specification")
