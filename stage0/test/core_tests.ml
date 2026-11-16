open Harness
open Support

let core_of packages key =
  Option.map
    (fun (checked : Infer.checked) -> checked.form)
    (Database.read_checked_body (database packages) key)

type form = { core : Core.t; names : (Core.local, string) Hashtbl.t }

let form_of (core : Core.t) = { core; names = Core_walk.For_testing.local_names core.definition }

let expressions form =
  let found = ref [] in
  Core_walk.definition
    { Core_walk.ignore_all with expression = (fun node -> found := node :: !found) }
    form.core.definition;
  List.rev !found

let calls form =
  List.filter_map
    (fun (node : Core.expression) -> match node.kind with Call call -> Some call | _ -> None)
    (expressions form)

let name form (local : Core.local) =
  match local with
  | Self -> "self"
  | Named _ | Synthetic _ -> Option.value ~default:"" (Hashtbl.find_opt form.names local)

let rec access_path form (place : Core.place) =
  match place with
  | Local { local; _ } -> name form local
  | Field { base; field; _ } -> access_path form base ^ "." ^ field
  | Constant { path; _ } -> Path.show path
  | Lent call -> "lent " ^ expression form call
  | Temporary value -> "temporary " ^ expression form value

and expression form (node : Core.expression) =
  let list describe items = String.concat ", " (List.map describe items) in
  match node.kind with
  | Integer number -> Z.to_string number
  | Use place -> "use " ^ access_path form place
  | Slice { base; callee; bounds } ->
      Printf.sprintf "slice %s(%s)" (Core_lint.callee_name callee)
        (list (argument form)
           (Passed { mode = Read; value = Place base; mode_keyword = None } :: bounds))
  | Operator { operation; arguments } ->
      Printf.sprintf "%s(%s)"
        (Intrinsic.operation_name operation)
        (list (expression form) arguments)
  | Call { callee; arguments; _ } ->
      let dispatch =
        match callee with
        | Trait_method { self_type; evidence; _ } ->
            Printf.sprintf " for %s by %s" (Types.show self_type)
              (match evidence with
              | Impl { impl; _ } -> Path.show impl
              | Bound -> "a bound"
              | Dynamic -> "any")
        | _ -> ""
      in
      Printf.sprintf "%s%s(%s)" (Core_lint.callee_name callee) dispatch
        (list (argument form) arguments)
  | _ -> "a value of the type " ^ Types.show node.type_

and operand form (value : Core.operand) =
  match value with
  | Place place -> "place " ^ access_path form place
  | Value value -> expression form value

and argument form (passed : Core.argument) =
  match passed with
  | Passed { mode; value; _ } -> Types.show_mode mode ^ operand form value
  | Default -> "default"

let definition_form text (path : Path.t) =
  let packages = setup [ ("app::main", text) ] in
  let file = file_of "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.span 0 0) message)
       (parse_errors packages file)
     @ Database.For_testing.(list_diagnostics [ Resolve; Interface; Infer ])
         (Support.database packages) file
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
        if Path.equal key.path path then Option.map (fun core -> (key, core)) (core_of packages key)
        else None)
      ((Support.names packages file.module_.package).declarations_in file)
  in
  match definition with
  | Some (key, core) ->
      Core_lint.check
        (Database.make_interface_lookups (database packages) [ key.module_.package ])
        key core;
      form_of core
  | None -> failwith (Printf.sprintf "`%s` has no core form" (Path.show path))

let expect_observed expected observed =
  if observed <> expected then
    fail "expected [%s], found [%s]" (String.concat "; " expected) (String.concat "; " observed)

let expect ?(definition = Support.top "app::main" "g") test_name text observe expected =
  test test_name (fun () -> expect_observed expected (observe (definition_form text definition)))

let contract form : Core.contract =
  match form.core.definition with
  | Function { contract; _ } -> contract
  | _ -> failwith "the definition is not a function"

let final_expression form =
  let of_block (block : Core.block) =
    match (block.value, List.rev block.statements) with
    | Some value, _ -> [ expression form value ]
    | None, { kind = Evaluate value; _ } :: _ -> [ expression form value ]
    | None, _ -> []
  in
  match form.core.definition with
  | Function { body = Some body; _ } | Law_proof { body = Some body; _ } -> of_block body
  | _ -> []

let capabilities (set : Types.capability_set) =
  List.map
    (function Types.Capability path -> Path.show path | _ -> "a capability that is not named")
    (set :> Types.capability list)

let shape = Fixtures.Core.shape

let () =
  expect "a match on a local borrows the local: its scrutinee is a place"
    (shape ^ Fixtures.Core.match_on_a_place_borrows_the_place)
    (fun form ->
      List.concat_map
        (fun (node : Core.expression) ->
          match node.kind with
          | Match { scrutinees; _ } -> List.map (operand form) scrutinees
          | _ -> [])
        (expressions form))
    [ "place shape" ];
  expect "a list passed to a `mut` slice parameter is passed as a mutable view of all of it"
    Fixtures.Core.list_passed_to_a_mut_slice_parameter
    (fun form ->
      List.filter_map
        (fun (call : Core.call) ->
          if Core_lint.callee_name call.callee = "app::main::clear" then
            Some (String.concat ", " (List.map (argument form) call.arguments))
          else None)
        (calls form))
    [ "mut slice standard::list::List.slice_from(place items, 0)" ]

let () =
  List.iter
    (fun statement ->
      test (Printf.sprintf "`%s` on a hole has a core form" statement) (fun () ->
          no_diagnostics
            ~check:(fun packages module_ ->
              Database.For_testing.(list_diagnostics [ Resolve; Interface; Infer ])
                (Support.database packages) module_)
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

let () =
  let apply = Fixtures.Core.apply in
  let granted form =
    List.concat_map
      (fun (call : Core.call) ->
        match call.callee with
        | Function { path; type_arguments } when Path.equal path (Support.top "app::main" "apply")
          ->
            List.concat_map
              (function
                | Types.Capabilities set -> capabilities set
                | other -> [ Types.show_argument other ])
              type_arguments
        | _ -> [])
      (calls form)
  in
  expect "a capability parameter is inferred as the set of capabilities that a lambda uses"
    (apply ^ Fixtures.Core.capability_parameter_is_inferred_as_the_set_of)
    granted
    [ "standard::capabilities::Console" ];
  expect "a capability parameter is inferred as the set of capabilities that a named function uses"
    (apply ^ Fixtures.Core.named_function_passed_for_a_capability_generic)
    granted
    [ "standard::capabilities::Console" ];
  test "a call's `uses` and a lambda's type contain the inferred set, not the callee's parameter"
    (fun () ->
      let text = apply ^ Fixtures.Core.calls_uses_and_a_lambdas_type_contain_the_inferred in
      let packages = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.equal key.path (Support.top "app::main" "g") then
            match core_of packages key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = Function { path; _ }; uses; _ }
                          when Path.equal path (Support.top "app::main" "apply") ->
                            actual :=
                              ("needs " ^ Types.show_argument (Capabilities uses)) :: !actual
                        | Lambda _ -> actual := Types.show node.type_ :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Support.declarations packages (Support.module_of "app::main"));
      if List.sort compare !actual <> [ "(fn() uses Console)"; "needs {Console}" ] then
        fail "found [%s]" (String.concat "; " !actual));
  test "a capability parameter in a result type is inferred separately for each call" (fun () ->
      let text = Fixtures.Core.capability_parameter_in_a_result_type_is_inferred in
      let packages = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.equal key.path (Support.top "app::main" "g") then
            match core_of packages key with
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
        (Support.declarations packages (Support.module_of "app::main"));
      if List.sort compare !actual <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then fail "found [%s]" (String.concat "; " !actual))

let () =
  test "a node's origin gives its source span" (fun () ->
      let text = Fixtures.Core.nodes_origin_gives_its_source_span in
      let packages = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( core_of packages key,
              (Support.names packages key.module_.package).spans key,
              (Support.names packages key.module_.package).text key )
          with
          | Some form, spans, written ->
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
        (Support.declarations packages (Support.module_of "app::main")))

let () =
  let applied form =
    List.filter_map
      (fun (node : Core.expression) ->
        match node.kind with
        | Specification_function { function_; _ } ->
            Some
              (match function_ with
              | Log -> "log"
              | Power -> "power"
              | Time -> "time"
              | Calls -> "calls")
        | Call call -> Some ("call " ^ Core_lint.callee_name call.callee)
        | _ -> None)
      (expressions form)
  in
  expect "a cost clause names its resource" Fixtures.Core.cost_clause_names_its_resource
    (fun form ->
      List.map
        (fun (cost : Core.cost) ->
          let resource =
            match cost.resource with
            | Time -> "time"
            | Allocations -> "allocations"
            | Allocated_bytes -> "allocated bytes"
            | Calls (Function_parameter local) -> "calls through " ^ name form local
            | Calls (Capability path) -> "calls of " ^ Path.show path
            | Calls (Capability_method (path, method_)) ->
                "calls of " ^ Path.show path ^ "." ^ method_
          in
          resource ^ " "
          ^
          match cost.bound with
          | Finite -> "finite"
          | Order_of _ -> "of an order"
          | At_most _ -> "at most"
          | Exactly _ -> "exactly")
        (contract form).costs)
    [
      "calls through visit exactly";
      "calls of standard::capabilities::Clock.now at most";
      "time of an order";
    ];
  expect "`log` and `power` are specification functions outside a cost bound too"
    Fixtures.Core.log_and_power_are_specification_functions_outside applied [ "log"; "power" ];
  expect "a function of the file named `power` is called in a specification"
    Fixtures.Core.function_of_the_file_named_power_is_called_in_a applied
    [ "call app::main::power" ];
  expect "the time of a method of a type parameter's bound names the trait method"
    Fixtures.Core.time_of_a_method_of_a_type_parameters_bound_names
    (fun form ->
      List.filter_map
        (fun (node : Core.expression) ->
          match node.kind with
          | Method_time (Trait_method { self_type; evidence; _ } as callee) ->
              Some
                (Printf.sprintf "time(%s) for %s by %s" (Core_lint.callee_name callee)
                   (Types.show self_type)
                   (match evidence with
                   | Bound -> "a bound"
                   | Impl _ -> "an impl"
                   | Dynamic -> "any"))
          | Method_time callee -> Some ("time(" ^ Core_lint.callee_name callee ^ ")")
          | _ -> None)
        (expressions form))
    [ "time(standard::core::Equal.equal) for Element by a bound" ];
  test "in a trait, `time(Self.method)` names the trait's own method" (fun () ->
      no_diagnostics
        ~check:(fun packages module_ ->
          Database.For_testing.(list_diagnostics [ Resolve; Interface; Infer ])
            (Support.database packages) module_)
        [ ("app::main", Fixtures.Core.in_a_trait_time_self_method_names_the_traits_own) ])

let () =
  test "the origin of a cost is its cost clause" (fun () ->
      let text = Fixtures.Core.origin_of_a_cost_is_its_cost_clause in
      let packages = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( core_of packages key,
              (Support.names packages key.module_.package).spans key,
              (Support.names packages key.module_.package).text key )
          with
          | ( Some { definition = Function { contract = { costs = [ cost ]; _ }; _ }; _ },
              spans,
              written ) ->
              let span = spans.(cost.origin) in
              let quoted = String.sub written span.start (span.stop - span.start) in
              if quoted <> "cost time O(items.length())" then fail "found `%s`" quoted
          | _ -> fail "no core form with exactly one cost")
        (Support.declarations packages (Support.module_of "app::main")))

let () =
  let packages = setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      test
        (Printf.sprintf "%s's core forms satisfy the invariants" (Path.show_file file))
        (fun () ->
          forms :=
            !forms
            + Core_lint.check_file
                (Database.make_interface_lookups (database packages) [ file.module_.package ])
                ~core:(core_of packages) file))
    Standard_library.files;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

let () =
  test "a `todo` type has no derived core form" (fun () ->
      let packages = setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
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
      if Database.For_testing.read_derived_form (database packages) path <> None then
        fail "it has a core form");
  test
    "every method of a derived impl in the standard library has a core form that satisfies the \
     invariants" (fun () ->
      let packages = setup [] in
      let interface =
        Database.make_interface_lookups (database packages) [ Path.standard_package ]
      in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (interface.names.impls Path.standard_package)
      in
      if derived = [] then fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Impls.impl_interface interface impl with
          | None -> fail "`%s` has no interface" (Path.show impl)
          | Some impl_interface ->
              let provided =
                match
                  Interface.Definition.trait_interface interface impl_interface.implements.trait
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
                  match Database.For_testing.read_derived_form (database packages) path with
                  | Some form -> Core_lint.check_derived interface path form
                  | None ->
                      if not (List.mem name provided) then
                        fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      fail "`%s`, `%s`: %s" (Path.show impl) name (Compiler_bug.to_string bug))
                impl_interface.impl_methods)
        derived)

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
    let packages = setup [ ("app::main", text) ] in
    let both_package = Path.package both in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let bounds (actual : Types.parameter) = if actual = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.implements
          (Database.make_interface_lookups (database packages) [ both_package ])
          ~bounds
          (Types.named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match
      Database.For_testing.read_core (database packages) (Method { owner; name; receiver = Read })
    with
    | Some (form, substitution) ->
        ( form_of form,
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            substitution )
    | None -> failwith "no core form"
  in
  let observed name =
    let form, substitution = core_of_method name in
    final_expression form @ substitution
  in
  test "a method defined in an impl has its own core form" (fun () ->
      expect_observed
        [ "app::main::Described.describe for Value by a bound(place self.first)" ]
        (observed "describe"));
  test
    "a method inherited from a trait has the default method's core form and a substitution for Self"
    (fun () ->
      let describe = "app::main::Described.describe for Self by a bound(place self)" in
      expect_observed
        [ Printf.sprintf "add(%s, %s)" describe describe; "Self = Both[Value]" ]
        (observed "twice"));
  test "a method of a derived impl has the generated core form" (fun () ->
      let packages = setup [ ("app::main", text) ] in
      let owner : Path.t = Derived { type_ = both; trait = Well_known.path Equal } in
      match
        ( Database.For_testing.read_core (database packages)
            (Method { owner; name = "equal"; receiver = Read }),
          Database.For_testing.read_core (database packages)
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, []), Some (_, [ _ ]) -> ()
      | _ ->
          fail "expected the derived method with no substitution and the inherited method with one")

let () =
  expect
    ~definition:
      (Law_proof
         {
           module_ = Support.module_of "app::main";
           trait =
             { path = Support.top "standard::core" "Ordered"; arguments = []; associated = [] };
           law = "agrees_with_equal";
           for_type = Support.top "app::main" "Pair";
         })
    "a law's proof has the law's parameters, with the proof's type for Self"
    (Fixtures.Core.pair_ordering
   ^ "proof Ordered.agrees_with_equal for Pair {\n  only_equal(first, second: second)\n}\n")
    (fun form ->
      (match form.core.definition with
        | Law_proof { parameters; _ } ->
            List.map
              (fun (parameter : Core.parameter) ->
                Printf.sprintf "%s: %s, %s" parameter.name (Types.show parameter.type_)
                  (match parameter.local with
                  | Synthetic index -> Printf.sprintf "synthetic local %d" index
                  | Named _ | Self -> "not synthetic"))
              parameters
        | _ -> [ "not a law's proof" ])
      @ final_expression form)
    [
      "first: Pair, synthetic local 0";
      "second: Pair, synthetic local 1";
      "app::main::only_equal(place first, place second)";
    ]
