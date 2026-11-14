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

let callees form =
  List.map (fun (call : Core.call) -> Core_lint.callee_name call.callee) (calls form)

(* Fails the running test, printing the core form, unless it has the
   property. *)
let check form property =
  if not (property form) then
    fail "found:\n%s\ncallees: %s" (Core_print.show form.core) (String.concat ", " (callees form))

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

let expect ?(definition = "g") test_name text property =
  test test_name (fun () -> check (definition_form text definition) property)

let contract form : Core.contract =
  match form.core.definition with
  | Function { contract; _ } -> contract
  | _ -> failwith "the definition is not a function"

(* Whether the body's final expression has the property: its value, or the
   last statement of a body that has no value. *)
let ends_with property form =
  match form.core.definition with
  | Function { body = Some { value = Some value; _ }; _ }
  | Law_proof { body = { value = Some value; _ }; _ } ->
      property value
  | Function { body = Some { value = None; statements }; _ }
  | Law_proof { body = { value = None; statements }; _ } -> (
      match List.rev statements with
      | { kind = Evaluate value; _ } :: _ -> property value
      | _ -> false)
  | _ -> false

let name form (local : Core.local) =
  match local with
  | Self -> "self"
  | Named _ | Synthetic _ -> Option.value ~default:"" (Hashtbl.find_opt form.names local)

(* A place written as a local and fields, such as [self.first]. *)
let rec access_path form (place : Core.place) =
  match place with
  | Local { local; _ } -> Some (name form local)
  | Field { base; field; _ } -> Option.map (fun base -> base ^ "." ^ field) (access_path form base)
  | Constant { path; _ } -> Some (Path.show path)
  | Lent _ | Temporary _ -> None

let is_place form path (operand : Core.operand) =
  match operand with Place place -> access_path form place = Some path | Value _ -> false

let passed property (argument : Core.argument) =
  match argument with Passed { value; _ } -> property value | Default -> false

(* A call of the callee [name] with one argument for each property. *)
let is_call name arguments (expression : Core.expression) =
  match expression.kind with
  | Call call ->
      Core_lint.callee_name call.callee = name
      && List.length arguments = List.length call.arguments
      && List.for_all2 (fun property argument -> property argument) arguments call.arguments
  | _ -> false

let is_operator (operation : Intrinsic.operation) operands (expression : Core.expression) =
  match expression.kind with
  | Operator { operation = applied; arguments } ->
      applied = operation
      && List.length arguments = List.length operands
      && List.for_all2 (fun property argument -> property argument) operands arguments
  | _ -> false

let capabilities (set : Types.capability_set) =
  List.map
    (function Types.Capability path -> Path.show path | _ -> "a capability that is not named")
    (set :> Types.capability list)

let shape = Fixtures.Core.shape

(* Operands *)

let () =
  expect "a match on a local borrows the local: its scrutinee is a place"
    (shape ^ Fixtures.Core.match_on_a_place_borrows_the_place) (fun form ->
      ends_with
        (fun value ->
          match value.kind with
          | Match { scrutinees = [ scrutinee ]; _ } -> is_place form "shape" scrutinee
          | _ -> false)
        form)

let () =
  expect "a list passed to a `mut` slice parameter is passed as a mutable view of all of it"
    Fixtures.Core.list_passed_to_a_mut_slice_parameter (fun form ->
      match calls form with
      | [
       { arguments = [ Passed { mode = Mut; value = Value { kind = Slice { call }; _ }; _ } ]; _ };
       _;
      ] ->
          is_call "standard::list::List.slice_from"
            [
              passed (is_place form "items");
              passed (fun (start : Core.operand) ->
                  match start with
                  | Value { kind = Integer zero; _ } -> Z.equal zero Z.zero
                  | _ -> false);
            ]
            call
      | _ -> false)

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
    match
      List.filter
        (fun (call : Core.call) -> Core_lint.callee_name call.callee = "app::main::apply")
        (calls form)
    with
    | [ { callee = Function { type_arguments = [ Capabilities set ]; _ }; _ } ] -> capabilities set
    | _ -> []
  in
  expect "a capability parameter is inferred as the set of capabilities that a lambda uses"
    (apply ^ Fixtures.Core.capability_parameter_is_inferred_as_the_set_of) (fun form ->
      granted form = [ "standard::capabilities::Console" ]);
  expect "a capability parameter is inferred as the set of capabilities that a named function uses"
    (apply ^ Fixtures.Core.named_function_passed_for_a_capability_generic) (fun form ->
      granted form = [ "standard::capabilities::Console" ]);
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
  (* The specification functions that a definition applies, in order. *)
  let specification_functions form =
    List.filter_map
      (fun (node : Core.expression) ->
        match node.kind with Specification_function { function_; _ } -> Some function_ | _ -> None)
      (expressions form)
  in
  expect "a cost clause names its resource" Fixtures.Core.cost_clause_names_its_resource
    (fun form ->
      match (contract form).costs with
      | [
       { resource = Calls (Function_parameter visit); bound = Exactly _; _ };
       { resource = Calls (Capability_method (clock, "now")); bound = At_most _; _ };
       { resource = Time; bound = Order_of _; _ };
      ] ->
          name form visit = "visit" && Path.show clock = "standard::capabilities::Clock"
      | _ -> false);
  expect "`log` and `power` are specification functions outside a cost bound too"
    Fixtures.Core.log_and_power_are_specification_functions_outside (fun form ->
      specification_functions form = [ Log; Power ] && calls form = []);
  expect "a function of the file named `power` is called in a specification"
    Fixtures.Core.function_of_the_file_named_power_is_called_in_a (fun form ->
      specification_functions form = [] && callees form = [ "app::main::power" ]);
  expect "the time of a method of a type parameter's bound names the trait method"
    Fixtures.Core.time_of_a_method_of_a_type_parameters_bound_names (fun form ->
      List.exists
        (fun (node : Core.expression) ->
          match node.kind with
          | Method_time
              (Trait_method
                 {
                   name = "equal";
                   evidence = Bound;
                   self_type = Parameter { name = "Element"; _ };
                   _;
                 }) ->
              true
          | _ -> false)
        (expressions form));
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
