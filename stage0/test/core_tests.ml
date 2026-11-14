(* Tests of the core form's decisions that no run of a program shows, but
   ownership checking or the prover reads: whether an operand is a place,
   the capabilities a call is inferred to use, the resource a cost clause
   names, and which calls a specification makes. Each test checks one such
   fact about one definition.

   The rest of the core form is tested elsewhere. [Core_lint] holds the
   invariants of every core form, and runs on every core form that a test
   produces. The codegen suites run programs, which test what each
   desugaring means. *)

open Harness
open Support

(* A core form, with the name that each of its locals is declared with. *)
type form = { core : Core.t; names : (Core.local, string) Hashtbl.t }

let form_of (core : Core.t) = { core; names = Core_walk.local_names core.definition }

(* Every expression of a definition, in evaluation order. *)
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

(* A place written as a local and fields, such as [self.first]. *)
let rec access_path form (place : Core.place) =
  match place with
  | Local { local; _ } -> name form local
  | Field { base; field; _ } -> access_path form base ^ "." ^ field
  | Constant { path; _ } -> Path.show path
  | Lent call -> "lent " ^ expression form call
  | Temporary value -> "temporary " ^ expression form value

(* The parts of an expression that the tests observe, written briefly: a
   call with its callee and arguments, an operator, a slice, a use, and a
   literal. *)
and expression form (node : Core.expression) =
  let list describe items = String.concat ", " (List.map describe items) in
  match node.kind with
  | Integer number -> Z.to_string number
  | Use place -> "use " ^ access_path form place
  | Slice { call } -> "slice " ^ expression form call
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

(* The core form of the definition [name] of the program [text], which must
   check without a diagnostic and pass the lint. *)
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
          Option.map (fun core -> (key, core)) (Query.demand database Infer.core key)
        else None)
      (Query.demand database Resolve.Names.declarations_in file)
  in
  match definition with
  | Some (key, core) ->
      Core_lint.check database key core;
      form_of core
  | None -> failwith (Printf.sprintf "`%s` has no core form" name)

(* Fails the running test unless the observations are the expected
   ones. *)
let expect_observed expected observed =
  if observed <> expected then
    fail "expected [%s], found [%s]" (String.concat "; " expected) (String.concat "; " observed)

(* [expect test_name text observe expected]: what [observe] reports of the
   definition [g], or of [definition], of the program [text]. *)
let expect ?(definition = "g") test_name text observe expected =
  test test_name (fun () -> expect_observed expected (observe (definition_form text definition)))

let contract form : Core.contract =
  match form.core.definition with
  | Function { contract; _ } -> contract
  | _ -> failwith "the definition is not a function"

(* The body's final expression: its value, or the last statement of a body
   that has no value. *)
let final_expression form =
  let of_block (block : Core.block) =
    match (block.value, List.rev block.statements) with
    | Some value, _ -> [ expression form value ]
    | None, { kind = Evaluate value; _ } :: _ -> [ expression form value ]
    | None, _ -> []
  in
  match form.core.definition with
  | Function { body = Some body; _ } | Law_proof { body; _ } -> of_block body
  | _ -> []

let capabilities (set : Types.capability_set) =
  List.map
    (function Types.Capability path -> Path.show path | _ -> "a capability that is not named")
    (set :> Types.capability list)

let shape = Fixtures.Core.shape

(* Operands *)

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

(* Holes *)

let () =
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
  (* The capabilities that the call of [apply] is inferred to grant. *)
  let granted form =
    List.concat_map
      (fun (call : Core.call) ->
        match call.callee with
        | Function { path; type_arguments } when Path.show path = "app::main::apply" ->
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

(* Specifications *)

let () =
  (* The specification functions that a definition applies, and the
     functions it calls, in order. *)
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
        (fun () -> forms := !forms + Core_lint.check_file database file))
    Standard_library.files;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

(* Derived methods *)

let () =
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
                          Core_lint.check database { module_; path; ordinal = 0 } form
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
  (* The method's final expression, and then its substitution. *)
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
      Core_lint.check database key form);
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
