let make ?(notes = []) ?(fixes = []) code location message : Nodes.description =
  { code = Capabilities code; severity = Error; location; message; notes; fixes }

let capitalize = function
  | Description.Text text :: rest -> Description.Text (String.capitalize_ascii text) :: rest
  | pieces -> pieces

let describe_subject = function
  | Capabilities.Call origin -> capitalize (Build.describe_call origin)
  | Unmeasured_loop -> [ Text "This loop has no measure, so it" ]
  | Conditionally_measured_loop condition ->
      [
        Text
          (Printf.sprintf "This loop's measure holds only when %s, so the loop"
             (Types.show_condition condition));
      ]
  | Failing_operation -> [ Text "This operation may fail, so it" ]
  | Concurrent_block -> [ Text "This `concurrent` block" ]
  | Concurrent_for_loop -> [ Text "This `concurrent for` loop" ]
  | Implementation -> [ Text "This implementation" ]

let show_alternative = function
  | Capabilities.Add_decreases -> "give the loop a `decreases` clause"
  | Add_decreases_or_bound type_ ->
      Printf.sprintf "give the loop a `decreases` clause, or bound `%s` by `FiniteCursor`"
        (Types.show type_)
  | Add_decreases_or_implement type_ ->
      Printf.sprintf "give the loop a `decreases` clause, or implement `FiniteCursor` for `%s`"
        (Types.show type_)

let add_alternative ~sentence_start = function
  | Some alternative when sentence_start ->
      " " ^ String.capitalize_ascii (show_alternative alternative) ^ "."
  | Some alternative -> ", or " ^ show_alternative alternative
  | None -> ""

let value_reason =
  "Its meaning must be a value. A function that fails on some inputs says so with `requires` \
   instead."

let describe_restriction = function
  | Capabilities.Parallel_branch ->
      ("a `parallel` branch", "Parallel calls of one implementation could race.", true)
  | Parallel_for -> ("a `parallel for`", "Parallel calls of one implementation could race.", true)
  | Proof -> ("a proof", value_reason, true)
  | Specification -> ("a specification", value_reason, true)
  | Law -> ("a law", value_reason, true)
  | Quantifier_body -> ("a quantifier's body", value_reason, true)
  | Constant_expression ->
      ( "a constant expression",
        "It is evaluated when the code is checked, and a check has no capabilities.",
        false )

let show_exceptions = function
  | [] -> ""
  | allowed ->
      " except "
      ^ String.concat " and "
          (List.map
             (fun capability -> Printf.sprintf "`%s`" (Types.show_capability capability))
             allowed)

let show_declaring_clause clause capability =
  match clause with
  | Capabilities.Own_uses -> Printf.sprintf "`uses %s`" capability
  | Impl_uses -> Printf.sprintf "`uses %s` on the `impl`" capability
  | Associated_capability_set { name; is_defined; is_named } ->
      let set =
        if is_defined then Printf.sprintf "`%s` in the `impl`'s `capability %s`" capability name
        else Printf.sprintf "`capability %s = %s` in the `impl`" name capability
      in
      if is_named then set else Printf.sprintf "%s and `uses Self.%s` on the method" set name

let raise_bug format = Compiler_bug.raise_bug ~stage:"Catalog" format

let show_as_written : Path.t -> string = function
  | Top { module_; name } ->
      Grant.show_capability
        (Grant.make_capability ~module_names:(Path.list_module_parts module_) name)
  | path -> raise_bug "the capability %s is not a definition of a module" (Path.show path)

let describe_granted = function
  | Capabilities.Function path -> Printf.sprintf "`%s`" (Path.show path)
  | Trait_method { trait; name } -> Printf.sprintf "`%s.%s`" (Path.show trait) name
  | Implemented_method { implements; for_type } ->
      Printf.sprintf "The `impl` of `%s` for `%s`" (Types.show_trait implements)
        (Types.show for_type)
  | Provided_implementation { capability; for_type } ->
      Printf.sprintf "The `impl` of `%s` for `%s`" (Path.show capability) (Types.show for_type)

let write_not_granted granted package capability =
  let package = Path.show_package package and written = show_as_written capability in
  Printf.sprintf
    "%s uses `%s`, which the manifest does not grant `%s`. To grant it, add \"%s\" to the entry \
     for `%s` in `truss.toml`."
    (describe_granted granted) written package written package

let describe : Capabilities.t -> Nodes.description = function
  | Not_granted { at = origin; granted; package; capability } ->
      make Not_granted (Build.at origin) [ Text (write_not_granted granted package capability) ]
  | Lambda_uses { lambda; capability; use } ->
      let shown = Types.show_capability capability in
      make Lambda_uses (Build.at lambda)
        ~notes:
          (match use with
          | Some (origin, subject) ->
              [
                ( Build.at origin,
                  describe_subject subject @ [ Text (Printf.sprintf " uses `%s`." shown) ] );
              ]
          | None -> [])
        [
          Text
            (Printf.sprintf
               "This lambda uses `%s`, which the function type it is passed as does not allow."
               shown);
        ]
  | Must_terminate { at = origin; subject; restriction; alternative } ->
      let description, _, _ = describe_restriction restriction in
      make Not_available (Build.at origin)
        (describe_subject subject
        @ [
            Text
              (Printf.sprintf " uses `RunForever`, but %s must terminate.%s" description
                 (add_alternative ~sentence_start:true alternative));
          ])
  | Not_in_restriction { at = origin; subject; capability; restriction; allowed } ->
      let description, reason, is_within_code = describe_restriction restriction in
      make Not_available (Build.at origin)
        (describe_subject subject
        @ [
            Text
              (Printf.sprintf " uses `%s`, but %s may use no capability%s%s. %s"
                 (Types.show_capability capability)
                 description (show_exceptions allowed)
                 (if is_within_code then ", even one that is available outside it" else "")
                 reason);
          ])
  | Not_available { at = origin; subject; capability; declaration; can_provide; alternative } ->
      let shown = Types.show_capability capability in
      make Not_available (Build.at origin)
        (describe_subject subject
        @ [
            Text
              (match declaration with
              | Some (Declared_by clause) ->
                  Printf.sprintf " uses `%s`, which is not available here. Declare it with %s%s%s."
                    shown
                    (show_declaring_clause clause shown)
                    (if can_provide then ", or `provide` an implementation" else "")
                    (add_alternative ~sentence_start:false alternative)
              | Some (Fixed_by_trait { trait; method_name }) ->
                  Printf.sprintf
                    " uses `%s`, but `%s` can use only the capabilities `%s` declares for it.%s%s"
                    shown method_name (Types.show_trait trait)
                    (if can_provide then " Provide an implementation with `provide`." else "")
                    (add_alternative ~sentence_start:true alternative)
              | None ->
                  Printf.sprintf " uses `%s`, which is not available here.%s" shown
                    (add_alternative ~sentence_start:true alternative));
          ])
  | Not_an_implementation { implementation; type_ } ->
      make Not_an_implementation (Build.at implementation)
        [
          Text
            (Printf.sprintf "`%s` implements no capability, so it provides nothing."
               (Types.show type_));
        ]
  | Provide_missing_mut { implementation } ->
      make Provide_mode (Build.at implementation)
        ~fixes:
          [
            {
              title = [ Text "Provide it `mut`." ];
              edits = [ Build.insert_before implementation [ Text "mut " ] ];
            };
          ]
        [ Text "This implementation mutates its own state, so the place is provided `mut`." ]
  | Provide_needless_mut { implementation; place } ->
      make Provide_mode (Build.at implementation)
        ~fixes:
          [
            {
              title = [ Text "Remove the `mut`." ];
              edits = [ Build.delete (Start implementation) (Start place) ];
            };
          ]
        [
          Text
            "This implementation never mutates its own state, so the place is provided without \
             `mut`.";
        ]
  | Monitor_needs_tasks { implementation; type_ } ->
      make Monitor_needs_tasks (Build.at implementation)
        [
          Text
            (Printf.sprintf
               "`%s` is provided `mut`, and the body of this `provide` uses `Tasks`, so two tasks \
                could call its methods at the same time. Its methods are locked through `Tasks`, \
                but `Tasks` is provided only inside the body: it is not available at this \
                `provide`, and no implementation in it provides `Tasks`. Without the lock, the two \
                calls are a data race. Provide the implementation of `Tasks` in this `provide` or \
                in an enclosing one."
               (Types.show type_));
        ]
  | Callback_may_deadlock { implementation; capability; method_name; parameter } ->
      make Callback_may_deadlock (Build.at implementation)
        [
          Text
            (Printf.sprintf
               "The body of this `provide` can use `Tasks`, so this implementation is a monitor: \
                each call of its methods runs to completion before the next call starts. `%s.%s` \
                takes `%s`, which can call code that uses a capability. Called while the monitor \
                is held, that code could enter the monitor of a nested `provide`, and two tasks \
                could deadlock. Pass the method the values that it needs instead of a callback."
               (Path.show_name capability) method_name parameter);
        ]
