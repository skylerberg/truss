let find_core packages key =
  Option.map
    (fun (checked : Infer.checked) -> checked.form)
    (Database.read_checked_body (Support.make_database packages) key)

let list_expressions (form : Core.t) =
  let found = ref [] in
  Core_walk.walk_definition
    { Core_walk.ignore_all with expression = (fun node -> found := node :: !found) }
    form.definition;
  List.rev !found

let list_calls form =
  List.filter_map
    (fun (node : Core.expression) -> match node.kind with Call call -> Some call | _ -> None)
    (list_expressions form)

let name (local : Core.local) =
  match local with
  | Self -> "self"
  | Declared { name; _ } | Trait_parameter { name; _ } -> name
  | Synthetic index -> Printf.sprintf "synthetic %d" index

let rec show_access_path (place : Core.place) =
  match place with
  | Local { local; _ } -> name local
  | Field { base; field; _ } -> show_access_path base ^ "." ^ field
  | Constant { path; _ } -> Path.show path
  | Lent call -> "lent " ^ show_expression call
  | Temporary value -> "temporary " ^ show_expression value

and show_expression (node : Core.expression) =
  let list describe items = String.concat ", " (List.map describe items) in
  match node.kind with
  | Integer number -> Z.to_string number
  | Use place -> "use " ^ show_access_path place
  | Slice { base; callee; bounds } ->
      Printf.sprintf "slice %s(%s)"
        (Core_lint.show_target callee.target)
        (list show_argument (Passed { mode = Read; value = Place base } :: bounds))
  | Operator { operation; arguments } ->
      Printf.sprintf "%s(%s)"
        (Intrinsic.show_operation (Scalar operation))
        (list show_expression arguments)
  | Call { callee; arguments; _ } ->
      let dispatch =
        match callee.target with
        | Trait_method { self_type; evidence; _ } ->
            Printf.sprintf " for %s by %s" (Types.show self_type)
              (match evidence with
              | Impl { impl; _ } -> Path.show impl
              | Bound -> "a bound"
              | Dynamic -> "any")
        | _ -> ""
      in
      Printf.sprintf "%s%s(%s)"
        (Core_lint.show_target callee.target)
        dispatch (list show_argument arguments)
  | _ -> "a value of the type " ^ Types.show node.type_

and show_operand (value : Core.operand) =
  match value with
  | Place place -> "place " ^ show_access_path place
  | Value value -> show_expression value

and show_argument (passed : Core.argument) =
  match passed with
  | Passed { mode; value; _ } -> Types.show_mode mode ^ show_operand value
  | Default -> "default"

let make_definition_form text (path : Path.t) =
  let packages = Support.setup [ ("app::main", text) ] in
  let file = Support.parse_file "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.make_span 0 0) message)
       (Support.parse_errors packages file)
     @ Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
         (Support.make_database packages) file
   with
  | [] -> ()
  | reported ->
      failwith
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)));
  let definition =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.make_key declaration in
        if Path.equal key.path path then
          Option.map (fun core -> (key, core)) (find_core packages key)
        else None)
      ((Support.make_names packages).list_declarations_in file)
  in
  match definition with
  | Some (key, core) ->
      Core_lint.check (Database.make_interface_lookups (Support.make_database packages)) key core;
      core
  | None -> failwith (Printf.sprintf "`%s` has no core form" (Path.show path))

let expect_observed expected observed =
  if observed <> expected then
    Harness.fail "expected [%s], found [%s]" (String.concat "; " expected)
      (String.concat "; " observed)

let expect ?(definition = Support.make_top_path "app::main" "g") test_name text observe expected =
  Harness.test test_name (fun () ->
      expect_observed expected (observe (make_definition_form text definition)))

let read_contract (form : Core.t) : Core.contract =
  match form.definition with
  | Function { contract; _ } -> contract
  | _ -> failwith "the definition is not a function"

let list_final_expressions (form : Core.t) =
  let of_block (block : Core.block) =
    match (block.value, List.rev block.statements) with
    | Some value, _ -> [ show_expression value ]
    | None, { kind = Evaluate value; _ } :: _ -> [ show_expression value ]
    | None, _ -> []
  in
  match form.definition with
  | Function { body = Some body; _ } | Law_proof { body = Some body; _ } -> of_block body
  | _ -> []

let list_capabilities (set : Types.capability_set) =
  List.map
    (function Types.Capability path -> Path.show path | _ -> "a capability that is not named")
    (Types.list_capabilities set)

let shape = Fixtures.Core.shape

let () =
  expect "a match on a local views the local: its scrutinee is a place"
    (shape ^ Fixtures.Core.match_on_a_shape_parameter)
    (fun form ->
      List.concat_map
        (fun (node : Core.expression) ->
          match node.kind with
          | Match { scrutinees; _ } -> List.map show_operand scrutinees
          | _ -> [])
        (list_expressions form))
    [ "place shape" ];
  expect "a list passed to a `mut` slice parameter is passed as a mutable view of all of it"
    Fixtures.Core.list_passed_to_a_mut_slice_parameter
    (fun form ->
      List.filter_map
        (fun (call : Core.call) ->
          if Core_lint.show_target call.callee.target = "app::main::clear" then
            Some (String.concat ", " (List.map show_argument call.arguments))
          else None)
        (list_calls form))
    [ "mut slice standard::list::List.slice_from(place items, 0)" ]

let () =
  List.iter
    (fun statement ->
      Harness.test (Printf.sprintf "`%s` on a hole has a core form" statement) (fun () ->
          Support.expect_no_diagnostics
            ~check:(fun packages module_ ->
              Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
                (Support.make_database packages) module_)
            [
              ( "app::main",
                "type Config(port: Int64)\n\n\
                 fn take(count: Int64) -> Int64 {\n\
                \  count\n\
                 }\n\n\
                 fn g(items: List[Int64], config: Config) -> Int64\n\
                \  uses RunForever\n\
                 {\n\
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

let () =
  let apply = Fixtures.Core.apply in
  let list_granted form =
    List.concat_map
      (fun (call : Core.call) ->
        match call.callee.target with
        | Function { path; instantiation }
          when Path.equal path (Support.make_top_path "app::main" "apply") ->
            List.concat_map
              (fun (_, argument) -> list_capabilities argument)
              instantiation.capability_arguments
        | _ -> [])
      (list_calls form)
  in
  expect "a capability parameter is inferred as the set of capabilities that a lambda uses"
    (apply ^ Fixtures.Core.lambda_using_console_passed_to_apply)
    list_granted
    [ "standard::capabilities::Console" ];
  expect "a capability parameter is inferred as the set of capabilities that a named function uses"
    (apply ^ Fixtures.Core.named_function_passed_for_a_capability_generic)
    list_granted
    [ "standard::capabilities::Console" ];
  Harness.test
    "a call's `uses` and a lambda's type contain the inferred set, not the callee's parameter"
    (fun () ->
      let text = apply ^ Fixtures.Core.lambda_using_console_passed_to_apply in
      let packages = Support.setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.make_key declaration in
          if Path.equal key.path (Support.make_top_path "app::main" "g") then
            match find_core packages key with
            | Some form ->
                Core_walk.walk_definition
                  {
                    Core_walk.ignore_all with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = { target = Function { path; _ }; uses }; _ }
                          when Path.equal path (Support.make_top_path "app::main" "apply") ->
                            actual := ("needs " ^ Types.show_capabilities uses) :: !actual
                        | Lambda _ -> actual := Types.show node.type_ :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> Harness.fail "no core form")
        (Support.list_declarations packages (Support.parse_module "app::main"));
      if List.sort compare !actual <> [ "(fn() uses Console)"; "needs {Console}" ] then
        Harness.fail "found [%s]" (String.concat "; " !actual));
  Harness.test "a capability parameter in a result type is inferred separately for each call"
    (fun () ->
      let text = Fixtures.Core.two_calls_of_later_with_different_capabilities in
      let packages = Support.setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.make_key declaration in
          if Path.equal key.path (Support.make_top_path "app::main" "g") then
            match find_core packages key with
            | Some form ->
                Core_walk.walk_definition
                  {
                    Core_walk.ignore_all with
                    pattern =
                      (fun (node : Core.pattern) ->
                        match node.kind with
                        | Bind { local = Declared { name; _ }; _ } ->
                            actual := (name ^ ": " ^ Types.show node.type_) :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> Harness.fail "no core form")
        (Support.list_declarations packages (Support.parse_module "app::main"));
      if List.sort compare !actual <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then Harness.fail "found [%s]" (String.concat "; " !actual))

let () =
  Harness.test "a node's origin gives its source span" (fun () ->
      let text = Fixtures.Core.loop_summing_a_list in
      let packages = Support.setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.make_key declaration in
          match
            ( find_core packages key,
              (Support.make_names packages).read_spans key,
              (Support.make_names packages).read_text key )
          with
          | Some form, spans, written ->
              let actual = ref [] in
              Core_walk.walk_definition
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
              if !actual <> [ "total += item" ] then
                Harness.fail "found [%s]" (String.concat "; " !actual)
          | _ -> Harness.fail "no core form")
        (Support.list_declarations packages (Support.parse_module "app::main")))

let () =
  let list_applied form =
    List.filter_map
      (fun (node : Core.expression) ->
        match node.kind with
        | Specification_function { function_; _ } ->
            Some
              (match function_ with
              | Log -> "log"
              | Power -> "power"
              | Callback_cost metric -> Metric.show metric
              | Calls -> "calls")
        | Call call -> Some ("call " ^ Core_lint.show_target call.callee.target)
        | _ -> None)
      (list_expressions form)
  in
  expect "a cost clause names its resource" Fixtures.Core.cost_clauses_of_calls_and_time
    (fun form ->
      List.map
        (fun (cost : Core.cost) ->
          let resource =
            match cost.resource with
            | Metric metric -> Metric.show metric
            | Calls (Function_parameter local) -> "calls through " ^ name local
            | Calls (Capability path) -> "calls of " ^ Path.show path
            | Calls (Capability_method (path, method_)) ->
                "calls of " ^ Path.show path ^ "." ^ method_
          in
          resource ^ " "
          ^
          match cost.bound with
          | Order_of _ -> "of an order"
          | At_most _ -> "at most"
          | Exactly _ -> "exactly")
        (read_contract form).costs)
    [
      "calls through visit exactly";
      "calls of standard::capabilities::Clock.now at most";
      "time of an order";
    ];
  expect "`log` and `power` are specification functions outside a cost bound too"
    Fixtures.Core.ensures_with_log_and_power list_applied [ "log"; "power" ];
  expect "a function of the file named `power` is called in a specification"
    Fixtures.Core.function_named_power list_applied [ "call app::main::power" ];
  let list_method_costs form =
    List.filter_map
      (fun (node : Core.expression) ->
        match node.kind with
        | Method_cost { metric; method_ = Trait_method { self_type; evidence; _ } as method_ } ->
            Some
              (Printf.sprintf "%s(%s) for %s by %s" (Metric.show metric)
                 (Core_lint.show_target method_) (Types.show self_type)
                 (match evidence with Bound -> "a bound" | Impl _ -> "an impl" | Dynamic -> "any"))
        | Method_cost { metric; method_ } ->
            Some (Printf.sprintf "%s(%s)" (Metric.show metric) (Core_lint.show_target method_))
        | _ -> None)
      (list_expressions form)
  in
  expect "the time of a method of a type parameter's bound names the trait method"
    Fixtures.Core.cost_naming_time_of_a_bounds_method list_method_costs
    [ "time(standard::core::Equal.equal) for Element by a bound" ];
  expect "the allocations of a method of a bound name the trait method and the resource"
    Fixtures.Core.cost_naming_allocations_of_a_callback_and_a_bounds_method list_method_costs
    [
      "allocations(standard::core::Equal.equal) for Element by a bound";
      "allocated_bytes(standard::core::Equal.equal) for Element by a bound";
    ];
  expect "the allocations of a callback are a specification function of the resource"
    Fixtures.Core.cost_naming_allocations_of_a_callback_and_a_bounds_method list_applied
    [ "call standard::list::List.length"; "allocations"; "allocated_bytes" ];
  Harness.test "in a trait, `time(Self.method)` names the trait's own method" (fun () ->
      Support.expect_no_diagnostics
        ~check:(fun packages module_ ->
          Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
            (Support.make_database packages) module_)
        [ ("app::main", Fixtures.Core.trait_method_costing_time_of_self_size) ])

let () =
  Harness.test "the origin of a cost is its cost clause" (fun () ->
      let text = Fixtures.Core.cost_linear_in_a_lists_length in
      let packages = Support.setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.make_key declaration in
          match
            ( find_core packages key,
              (Support.make_names packages).read_spans key,
              (Support.make_names packages).read_text key )
          with
          | ( Some { definition = Function { contract = { costs = [ cost ]; _ }; _ }; _ },
              spans,
              written ) ->
              let span = spans.(cost.origin) in
              let quoted = String.sub written span.start (span.stop - span.start) in
              if quoted <> "cost time O(items.length())" then Harness.fail "found `%s`" quoted
          | _ -> Harness.fail "no core form with exactly one cost")
        (Support.list_declarations packages (Support.parse_module "app::main")))

let () =
  let packages = Support.setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      Harness.test
        (Printf.sprintf "%s's core forms satisfy the invariants" (Path.show_file file))
        (fun () ->
          forms :=
            !forms
            + Core_lint.check_file
                (Database.make_interface_lookups (Support.make_database packages))
                ~find_core:(find_core packages) file))
    Standard_library.files;
  Harness.test "the standard library has core forms" (fun () ->
      if !forms < 500 then Harness.fail "only %d of its definitions have one" !forms)

let () =
  Harness.test "a `todo` type has no derived core form" (fun () ->
      let packages = Support.setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
      let path : Path.t =
        Method
          {
            owner =
              Derived
                {
                  type_ = Top { module_ = Support.parse_module "app::main"; name = "Later" };
                  trait = Well_known.make_path Equal;
                };
            name = "equal";
            receiver = Read;
          }
      in
      if Database.For_testing.read_derived_form (Support.make_database packages) path <> None then
        Harness.fail "it has a core form");
  Harness.test
    "every method of a derived impl in the standard library has a core form that satisfies the \
     invariants" (fun () ->
      let packages = Support.setup [] in
      let interface = Database.make_interface_lookups (Support.make_database packages) in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (interface.names.list_impls Path.standard_package)
      in
      if derived = [] then Harness.fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Definition.find_impl_interface interface impl with
          | None -> Harness.fail "`%s` has no interface" (Path.show impl)
          | Some impl_interface ->
              let provided =
                match
                  Interface.Definition.find_trait_interface interface
                    impl_interface.implements.trait
                with
                | Some trait ->
                    List.filter_map
                      (fun (method_ : Types.trait_method) ->
                        if method_.provided then Some method_.method_name else None)
                      trait.methods
                | None -> []
              in
              List.iter
                (fun (name, receiver) ->
                  let path : Path.t = Method { owner = impl; name; receiver } in
                  match
                    Database.For_testing.read_derived_form (Support.make_database packages) path
                  with
                  | Some form -> Core_lint.check_derived interface path form
                  | None ->
                      if not (List.mem name provided) then
                        Harness.fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      Harness.fail "`%s`, `%s`: %s" (Path.show impl) name
                        (Compiler_bug.to_string bug))
                impl_interface.impl_methods)
        derived)

let () =
  let text = Fixtures.Core.described_both in
  let both : Path.t = Top { module_ = Support.parse_module "app::main"; name = "Both" } in
  let described : Types.trait_reference =
    {
      trait = Top { module_ = Support.parse_module "app::main"; name = "Described" };
      trait_arguments = [];
      associated = [];
    }
  in
  let read_method_core name =
    let packages = Support.setup [ ("app::main", text) ] in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let list_bounds (actual : Types.parameter) = if actual = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.find_evidence
          (Database.make_interface_lookups (Support.make_database packages))
          ~list_bounds
          (Types.make_named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match
      Database.For_testing.read_core (Support.make_database packages)
        (Method { owner; name; receiver = Read })
    with
    | Some (form, substitution) ->
        ( form,
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            (Types.For_testing.list_arguments substitution) )
    | None -> failwith "no core form"
  in
  let list_observed name =
    let form, substitution = read_method_core name in
    list_final_expressions form @ substitution
  in
  Harness.test "a method defined in an impl has its own core form" (fun () ->
      expect_observed
        [ "app::main::Described.describe for Value by a bound(place self.first)" ]
        (list_observed "describe"));
  Harness.test
    "a method inherited from a trait has the default method's core form and a substitution for Self"
    (fun () ->
      let describe = "app::main::Described.describe for Self by a bound(place self)" in
      expect_observed
        [ Printf.sprintf "add(%s, %s)" describe describe; "Self = Both[Value]" ]
        (list_observed "twice"));
  Harness.test "a method of a derived impl has the generated core form" (fun () ->
      let packages = Support.setup [ ("app::main", text) ] in
      let owner : Path.t = Derived { type_ = both; trait = Well_known.make_path Equal } in
      match
        ( Database.For_testing.read_core (Support.make_database packages)
            (Method { owner; name = "equal"; receiver = Read }),
          Database.For_testing.read_core (Support.make_database packages)
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, derived), Some (_, inherited)
        when Types.For_testing.list_arguments derived = []
             && List.length (Types.For_testing.list_arguments inherited) = 1 ->
          ()
      | _ ->
          Harness.fail
            "expected the derived method with no substitution and the inherited method with one")

let () =
  expect
    ~definition:
      (Law_proof
         {
           module_ = Support.parse_module "app::main";
           trait =
             {
               path = Support.make_top_path "standard::core" "Ordered";
               arguments = [];
               associated = [];
             };
           law = "agrees_with_equal";
           for_type = Support.make_top_path "app::main" "Pair";
         })
    "a law's proof has the law's parameters, with the proof's type for Self"
    (Fixtures.Core.pair_ordering
   ^ "proof Ordered.agrees_with_equal for Pair {\n  only_equal(first, second: second)\n}\n")
    (fun form ->
      (match form.definition with
        | Law_proof { parameters; _ } ->
            List.map
              (fun (parameter : Core.parameter) ->
                match parameter.local with
                | Trait_parameter { index; name } ->
                    Printf.sprintf "%s: %s, trait parameter %d" name (Types.show parameter.type_)
                      index
                | Declared _ | Self | Synthetic _ -> "not a trait parameter")
              parameters
        | _ -> [ "not a law's proof" ])
      @ list_final_expressions form)
    [
      "first: Pair, trait parameter 0";
      "second: Pair, trait parameter 1";
      "app::main::only_equal(place first, place second)";
    ]

let () =
  let show_callee (callee : Core.callee) =
    Printf.sprintf "%s uses [%s]"
      (Core_lint.show_target callee.target)
      (String.concat ", " (list_capabilities callee.uses))
  in
  let text = Fixtures.Core.slice_match_on_a_constant_and_loop_over_a_ticking_countdown in
  expect
    "a slice, a pattern that compares with a constant, and a loop over a cursor each hold their \
     callee with the capability set that the callee gives"
    text
    (fun form ->
      let held = ref [] in
      Core_walk.walk_definition
        {
          Core_walk.ignore_all with
          expression =
            (fun node ->
              match node.kind with
              | Slice { callee; _ } -> held := ("a slice holds " ^ show_callee callee) :: !held
              | _ -> ());
          statement =
            (fun node ->
              match node.kind with
              | For { iteration = Cursor { next; _ }; _ } ->
                  held := ("a loop holds " ^ show_callee next) :: !held
              | _ -> ());
          pattern =
            (fun node ->
              match node.kind with
              | Equal_to { equal; _ } -> held := ("a pattern holds " ^ show_callee equal) :: !held
              | _ -> ());
        }
        form.definition;
      List.rev !held)
    [
      "a loop holds standard::core::Cursor.next uses [app::main::Meter]";
      "a slice holds standard::list::List.slice_from uses []";
      "a pattern holds standard::core::Equal.equal uses []";
    ];
  expect "the walker hands every callee that a body invokes to its callee hook" text
    (fun form ->
      let invoked = ref [] in
      Core_walk.walk_definition
        {
          Core_walk.ignore_all with
          callee = (fun callee -> invoked := show_callee callee :: !invoked);
        }
        form.definition;
      List.rev !invoked)
    [
      "standard::core::Cursor.next uses [app::main::Meter]";
      "standard::list::List.slice_from uses []";
      "standard::core::Equal.equal uses []";
      "standard::list::Slice.length uses []";
    ];
  Harness.test "the callee of an intrinsic holds the capabilities that the intrinsic uses"
    (fun () ->
      let probe = Support.parse_file "standard::probe" in
      let database =
        Support.extend_standard_library
          [
            {
              name = Path.standard_package;
              dependencies = [];
              files = [ (probe, Fixtures.Capabilities.shared_count_updated_using_tasks) ];
            };
          ]
      in
      let key : Resolve.Names.key =
        {
          module_ = probe.module_;
          path = Top { module_ = probe.module_; name = "add" };
          ordinal = 0;
        }
      in
      match Database.read_checked_body database key with
      | Some { form; _ } ->
          Core_lint.check (Database.make_interface_lookups database) key form;
          expect_observed
            [ "intrinsic::shared_update uses [standard::capabilities::Tasks]" ]
            (List.filter_map
               (fun (call : Core.call) ->
                 match call.callee.target with
                 | Intrinsic _ -> Some (show_callee call.callee)
                 | Function _ | Trait_method _ | Capability_method _ | Indirect _ -> None)
               (list_calls form))
      | None -> Harness.fail "`add` has no core form")
