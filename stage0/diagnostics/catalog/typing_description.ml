let make ?(fixes = []) code location message : Nodes.description =
  { code = Types code; severity = Error; location; message; notes = []; fixes }

let show_property : Types.property -> string = function
  | Copyable -> "is `Copyable`"
  | Plain -> "is `Plain`"
  | View -> "is a view"
  | Holds_function -> "holds a function"

let describe_recursion ~limit = function
  | Typing.Property { type_; property } ->
      Printf.sprintf
        "Deciding whether `%s` %s needs more than %d nested types. The compiler stops there: an \
         associated type that holds a larger type can grow a type forever."
        (Types.show type_) (show_property property) limit
  | Contents { type_ } ->
      Printf.sprintf
        "Listing the types that `%s` holds needs more than %d nested types. The compiler stops \
         there: an associated type that holds a larger type can grow a type forever."
        (Types.show type_) limit
  | Evidence { type_; trait } ->
      Printf.sprintf
        "Deciding whether `%s` implements `%s` needs more than %d nested impls. The compiler stops \
         there: bounds that ask for ever larger types never finish."
        (Types.show type_) (Types.show_trait trait) limit
  | Capability_set capability ->
      Printf.sprintf
        "Finding the capabilities in `%s` needs more than %d nested capability sets. The compiler \
         stops there: capability sets defined from each other never finish."
        (Types.show_capability capability)
        limit

let say text : _ Description.piece list = [ Text text ]

let show_associated = function
  | Typing.Associated_type -> "associated type"
  | Associated_capability_set -> "associated capability set"

let show_kind : Language.Definition_kind.t -> string = function
  | Function -> "a function"
  | Type -> "a type"
  | Trait -> "a trait"
  | Capability -> "a capability"
  | Constant | Member_constant -> "a constant"
  | Theorem -> "a theorem"
  | Method -> "a method"
  | Impl -> "an `impl`"
  | Test -> "a test"
  | Law_proof -> "a law's proof"

let show_recipient = function Typing.Main -> "`main`" | Test -> "a test"

let describe : Typing.t -> Nodes.description = function
  | Recursion_limit { limit; recursion } ->
      make Recursion_limit (At Definition) [ Text (describe_recursion ~limit recursion) ]
  | Misplaced_self_type { at = origin } ->
      make Misplaced_self_type (Build.at origin)
        (say "`Self` names a type only in a type's definition, a trait, an `impl`, or a method.")
  | Self_outside_trait { at = origin; name; associated } ->
      make
        (match associated with
        | Associated_type -> Unknown_associated_type
        | Associated_capability_set -> Unknown_associated_capability)
        (Build.at origin)
        (say
           (Printf.sprintf
              "`Self.%s` names an %s of a trait, and `Self` is not in a trait or in an `impl` of \
               one here."
              name (show_associated associated)))
  | Undeclared_associated { at = origin; trait; name; associated } ->
      make
        (match associated with
        | Associated_type -> Unknown_associated_type
        | Associated_capability_set -> Unknown_associated_capability)
        (Build.at origin)
        (say
           (Printf.sprintf "`%s` declares no %s `%s`." (Types.show_trait trait)
              (show_associated associated) name))
  | Unbounded_associated { at = origin; parameter; name; associated } ->
      make
        (match associated with
        | Associated_type -> Unknown_associated_type
        | Associated_capability_set -> Unknown_associated_capability)
        (Build.at origin)
        (say
           (Printf.sprintf "No bound of `%s` declares an %s `%s`." parameter
              (show_associated associated) name))
  | Self_defined_capability_set { at = origin; name } ->
      make Unknown_associated_capability (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is defined from itself, or from a set that this `impl` defines after it." name))
  | Arity { at = origin; written; expected; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf "`%s` takes %s, and %s given." written
              (Diagnostic.show_count expected "argument" "arguments")
              (Diagnostic.show_count given "is" "are")))
  | Head_arity { at = origin; written; expected; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf "`%s` takes %s, and this head names %d." written
              (Diagnostic.show_count expected "generic parameter" "generic parameters")
              given))
  | Argument_kind { at = origin; written; parameter; mismatch } ->
      make Argument_kind (Build.at origin)
        (say
           (match mismatch with
           | Value_for_type ->
               Printf.sprintf "`%s`'s parameter `%s` is a `UInt64` value, not a type." written
                 parameter
           | Type_for_value ->
               Printf.sprintf "`%s`'s parameter `%s` is a type, not a value." written parameter))
  | Arguments_to_parameter { at = origin; written } ->
      make Arity (Build.at origin)
        (say (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." written))
  | Count_error { at = origin; written; error = Not_uint64 } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "`%s` in a type argument must be a constant of type `UInt64`." written))
  | Count_error { at = origin; written; error = Computed_from_itself } ->
      make Cyclic_count (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is computed from a constant whose value depends on itself, so its value is not \
               known."
              written))
  | Count_error { at = origin; written; error = Computed_by_call } ->
      make Count_calls_function (Build.at origin)
        (say
           (Printf.sprintf
              "The value of `%s` calls a function. A type is decided before any code is checked, \
               so a constant that a type names calls no function. Write the count as literals, \
               operators, and other such constants."
              written))
  | Trait_as_type { at = origin; written } ->
      make Not_a_type (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is a trait, not a type. A type parameter can have it as a bound, as in `[Item: \
               %s]`."
              written written))
  | Capability_as_type { at = origin; written } ->
      make Not_a_type (Build.at origin)
        (say (Printf.sprintf "`%s` is a capability, not a type." written))
  | Head_not_a_type { at = origin; written; kind } ->
      make Not_a_type (Build.at origin)
        (say
           (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
              written (show_kind kind)))
  | Not_a_trait { at = origin; written; is_parameter } ->
      make Not_a_trait (Build.at origin)
        (say
           (if is_parameter then Printf.sprintf "`%s` is a generic parameter, not a trait." written
            else Printf.sprintf "`%s` is not a trait." written))
  | Decided_condition { at = origin; subject } ->
      make Decided_condition (Build.at origin)
        (say
           (Printf.sprintf
              "A condition names a type parameter or `Self`, and `%s` is neither: whether it \
               implements a trait is decided where it is written."
              (Types.show subject)))
  | Decided_projection_condition { at = origin; subject; base; trait; name } ->
      make Decided_condition (Build.at origin)
        (say
           (Printf.sprintf
              "A condition names a type parameter or `Self`, as a bound does, and `%s` is an \
               associated type. Give it a type parameter, as in `[%s, %s: %s[%s = %s]]`, and name \
               `%s` in the condition."
              (Types.show subject) name (Types.show base) (Types.show_trait trait) name name name))
  | Not_a_capability { at = origin; written; is_type_parameter } ->
      make Not_a_capability (Build.at origin)
        (say
           (if is_type_parameter then
              Printf.sprintf
                "`%s` is a type parameter, not a capability. A capability parameter is written \
                 `generic %s` at each use."
                written written
            else Printf.sprintf "`%s` is not a capability." written))
  | Calls_not_a_capability { at = origin; written } ->
      make Not_a_capability (Build.at origin)
        (say
           (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." written))
  | Calls_through_parameter { at = origin; name } ->
      make Not_a_capability (Build.at origin)
        (say
           (Printf.sprintf
              "A function type's `calls` counts the calls of a capability, as in \
               `calls(FileRead)`: a type cannot name `%s`. Calls through a parameter are counted \
               in a function's own clauses."
              name))
  | Unknown_capability_method { at = origin; written; method_ } ->
      make Unknown_member (Build.at origin)
        (say (Printf.sprintf "`%s` has no method `%s`." written method_))
  | Time_of_run_forever { at = origin } ->
      make Unbounded_time (Build.at origin)
        (say
           "A function that uses `RunForever` may run forever, so no `time` clause bounds it. \
            Remove the `time` clause, or remove `RunForever` and give each loop a measure.")
  | Time_of_unbounded_parameter { at = origin; name } ->
      make Unbounded_time (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` may run forever, since its type uses `RunForever`, so `time(%s)` has no value."
              name name))
  | Misplaced_value_condition { at = origin; condition } ->
      make Misplaced_value_condition (Build.at origin)
        (say
           (match condition with
           | In_capability_method ->
               "A capability's method takes no condition on its arguments: an implementation uses \
                the capabilities of the code that provides it, so it could panic where the \
                condition holds."
           | Joined_with_bound ->
               "A condition on the arguments cannot be joined with a bound with `&&`."
           | Not_panic capabilities ->
               Printf.sprintf
                 "A condition on the arguments applies only to `Panic`, and `%s` is not `Panic`."
                 (String.concat ", " (List.map Types.show_capability capabilities))))
  | Wrong_value_parameter_type { at = origin; parameter; type_ } ->
      make Wrong_value_parameter_type (Build.at origin)
        ~fixes:
          [ { title = say "Write `UInt64`."; edits = [ Build.replace origin [ Text "UInt64" ] ] } ]
        (say
           (Printf.sprintf "`%s` is a value parameter, so its type is `UInt64`, not `%s`." parameter
              (Types.show type_)))
  | Missing_associated_type { at = origin; name; trait } ->
      make Missing_member (Build.at origin)
        (say (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares." name trait))
  | Missing_method { at = origin; name; signature; trait } ->
      make Missing_member (Build.at origin)
        (say
           (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares." name signature trait))
  | Implements_built_in_capability { at = origin; capability } ->
      make Implements_built_in_capability (Build.at origin)
        (say
           (match capability with
           | Panic ->
               "Nothing can implement `Panic`: no Truss code runs after a panic, and two \
                `parallel` branches that called one implementation with state would race."
           | Run_forever ->
               "Nothing can implement `RunForever`, since a `provide` of it would let a function \
                that does not declare `RunForever` run forever."
           | System ->
               "Nothing can implement `System`: the runtime grants it to the real implementations, \
                and a `provide` of it would let code that does not declare it reach the operating \
                system."))
  | Implements_built_in { at = origin; trait } ->
      make Implements_built_in (Build.at origin)
        (say
           (Printf.sprintf
              "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
              trait))
  | Associated_bound_unmet { at = origin; trait; name; bound; chosen } ->
      make Unsatisfied_bound (Build.at origin)
        (say
           (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one." trait name
              (Types.show_trait bound) (Types.show chosen)))
  | Extra_associated { at = origin; trait; name; associated } ->
      make Extra_member (Build.at origin)
        (say (Printf.sprintf "`%s` declares no %s `%s`." trait (show_associated associated) name))
  | Capability_set_defined_twice { at = origin; name } ->
      make Extra_member (Build.at origin)
        (say
           (Printf.sprintf
              "This `impl` already defines `%s`. List every capability in one definition, \
               separated by commas."
              name))
  | Missing_required_impl { at = origin; trait; required; for_type } ->
      make Missing_required_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement." trait
              (Types.show_trait required) (Types.show for_type)))
  | Uses_on_trait_impl { at = origin } ->
      make Impl_uses (Build.at origin)
        (say
           "Only an `impl` of a capability can have `uses`. A trait's methods can use only the \
            capabilities the trait declares.")
  | Callback_contract_mismatch { at = origin; name; trait; parameter; declaration; clauses } ->
      make Signature_mismatch (Build.at origin)
        (Description.Text
           (Printf.sprintf "`%s` must state the callback contract that `%s` declares for `%s`: "
              name trait parameter)
         ::
         (match clauses with
         | [] -> say "no `requires` and no `ensures`"
         | clauses ->
             List.concat
               (List.mapi
                  (fun index clause ->
                    (if index = 0 then [] else say ", ")
                    @ [
                        Description.Text "`";
                        Quote (Nodes.In_definition (declaration, clause));
                        Text "`";
                      ])
                  clauses))
        @ say
            (Printf.sprintf
               ". A caller through `%s` relies on that contract, so the method's own callback \
                contract is that one."
               trait))
  | Restated_without_own { at = origin; trait; declared_by; name; for_type } ->
      make Extra_member (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s` and declares no method of its own by that name. Give `%s` in \
               the `impl` of `%s` for `%s`."
              trait (Path.show declared_by) name name (Path.show declared_by) (Types.show for_type)))
  | Undeclared_method { at = origin; trait; name } ->
      make Extra_member (Build.at origin)
        (say (Printf.sprintf "`%s` declares no method `%s` with this receiver." trait name))
  | Capability_method_receiver { at = origin } ->
      make Wrong_receiver (Build.at origin)
        (say
           "A capability's implementation takes `self`, or `mut self` if it mutates its own state.")
  | Overridden_default { at = origin; trait; name } ->
      make Overridden_method_default (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` declares `%s` with a default, so no `impl` overrides it. A call that omits the \
               argument reads the default from the declaration in `%s`, and this method would be a \
               second declaration that shows none."
              trait name trait))
  | Impl_signature_mismatch { at = origin; name; signature; trait } ->
      make Signature_mismatch (Build.at origin)
        (say
           (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name name
              signature trait))
  | Uses_beyond_impl { at = origin; name } ->
      make Impl_uses (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` implements a capability, so it can use only the capabilities its `impl` \
               declares with `uses`."
              name))
  | Uses_beyond_trait { at = origin; name; trait } ->
      make Impl_uses (Build.at origin)
        (say (Printf.sprintf "`%s` can use only the capabilities `%s` declares for it." name trait))
  | Panic_beyond_condition { at = origin; name; trait } ->
      make Impl_uses (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` declares `%s` with `uses Panic unless` a condition, and this `%s` uses `Panic` \
               without one, so it could panic where that condition holds. Declare `uses Panic \
               unless` a condition that `%s`'s implies."
              trait name name trait))
  | Bound_unmet { at = origin; type_; argument; bound } ->
      make Unsatisfied_bound (Build.at origin)
        (say
           (Printf.sprintf "`%s` needs `%s: %s`, which does not hold here." (Types.show type_)
              (Types.show argument) (Types.show_trait bound)))
  | Private_in_public { at = origin; path } ->
      make Private_in_public (Build.at origin)
        (say
           (Printf.sprintf
              "This public definition mentions `%s`, which other packages cannot name. Make `%s` \
               public, or this definition not."
              (Path.show path) (Path.show path)))
  | Method_outside_package { at = origin; owner; package } ->
      make Method_outside_package (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is defined in the package `%s`, so its methods and constants must be too. A \
               function of this package can take it as a parameter instead."
              (Path.show owner) (Path.show_package package)))
  | Method_outside_module { at = origin; owner } ->
      make Method_outside_package (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is private to its module, so its methods and constants must be in that module."
              (Path.show owner)))
  | System_not_provided { at = origin; recipient } ->
      make No_real_implementation (Build.at origin)
        (say
           (Printf.sprintf
              "The runtime grants `System` only to the real implementations of the standard \
               capabilities, so it cannot provide it to %s."
              (show_recipient recipient)))
  | No_real_implementation { at = origin; written; recipient } ->
      make No_real_implementation (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` has no real implementation, so the runtime cannot provide it to %s. Provide an \
               implementation in the body with `provide`."
              written (show_recipient recipient)))
  | Main_signature { at = origin } ->
      make Main_signature (Build.at origin)
        (say
           "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`.")
  | Duplicate_member { at = origin; member_kind; name } ->
      make Duplicate_field (Build.at origin)
        (say (Printf.sprintf "Another %s of this type is already named `%s`." member_kind name))
  | Not_derivable { at = origin; written } ->
      make Not_derivable (Build.at origin)
        (say
           (Printf.sprintf
              "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, `Plain`, \
               `serialization.Serialize`, and `serialization.Deserialize` can be derived, not \
               `%s`."
              written))
  | Derives_inferred { at = origin; written; entry; siblings } ->
      make Derives_inferred (Build.at origin)
        ~fixes:
          [
            { title = say "Remove the declaration."; edits = [ Build.remove_entry entry siblings ] };
          ]
        (say
           (Printf.sprintf
              "Whether `%s` holds for this type is derived from its fields, which are visible. \
               Only an opaque type declares it."
              written))
  | Field_not_derivable { at = origin; written } ->
      make Cannot_derive (Build.at origin)
        (say (Printf.sprintf "A field of this type is not `%s`, so the type cannot be." written))
  | Default_of_sum { at = origin } ->
      make Cannot_derive (Build.at origin)
        (say
           "`Default` is derived as each field's default, so only a record can derive it: no \
            variant of this type is its default. Write the `impl`, which says which variant is.")
  | Derived_without_equal { at = origin; written } ->
      make Cannot_derive (Build.at origin)
        (say
           (Printf.sprintf "Deriving `%s` needs `Equal` to be derived too, so that the two agree."
              written))
  | Field_lacks_impl { at = origin; type_; written } ->
      make Cannot_derive (Build.at origin)
        (say
           (Printf.sprintf
              "A field of type `%s` does not implement `%s`, so `%s` cannot be derived."
              (Types.show type_) written written))
  | Trait_cycle { at = origin } ->
      make Trait_cycle (Build.at origin)
        (say "This trait requires itself through the traits it requires.")
  | Restated_requires { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. A caller \
               through `%s` would never prove this `requires`."
              name declared_by name declared_by))
  | Restated_decreases { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. It has no \
               body, so it has no recursion to measure."
              name declared_by name))
  | Restated_modifies { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. The parts that \
               its implementations change are those that `%s.%s` names."
              name declared_by name declared_by name))
  | Not_viewable_type { at = origin; type_ } ->
      make Not_viewable (Build.at origin)
        (say
           (Printf.sprintf
              "`view` applies to a `String` and to a `List`, and this type is `%s`. A value of \
               another type is viewed by a read-only parameter, a `let`, or a lending method."
              (Types.show type_)))
  | Indexed_modified_part { at = origin } ->
      make Not_a_field_path (Build.at origin)
        (say
           "One element or a narrower range is not a fixed part. A `modifies` clause names every \
            element of a list with `[..]`, as in `items[..]`, or the field that holds the \
            collection.")
  | Not_a_modified_part { at = origin } ->
      make Not_a_field_path (Build.at origin)
        (say "A `modifies` clause names fields of `mut` parameters, such as `scanner.position`.")
  | Modified_non_parameter { at = origin; name } ->
      make Not_a_field_path (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is not a parameter, and a `modifies` clause names fields of `mut` parameters."
              name))
  | Modified_whole_parameter { at = origin; parameter } ->
      make Not_a_field_path (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is a whole parameter. A `mut` parameter that the clause does not name may \
               change in every part already, so name the fields of `%s` that change, or remove \
               `%s`."
              parameter parameter parameter))
  | Read_only_part { at = origin; parameter; part } ->
      make Read_only_part (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is not `mut`, so the function changes no part of it. Remove `%s` from the \
               clause, or take `%s` as `mut`."
              parameter
              (Types.show_modified_part ~root:parameter part)
              parameter))
  | Repeated_part { at = origin; parameter; part; container; siblings } ->
      make Repeated_part (Build.at origin)
        ~fixes:
          [
            {
              title = say "Remove it.";
              edits = [ Build.remove_entry { covering = [ origin ] } siblings ];
            };
          ]
        (say
           (if container = part then
              Printf.sprintf "The clause names `%s` twice."
                (Types.show_modified_part ~root:parameter part)
            else
              Printf.sprintf "`%s` is a part of `%s`, which the clause names already."
                (Types.show_modified_part ~root:parameter part)
                (Types.show_modified_part ~root:parameter container)))
  | Fieldless_part { at = origin; parameter; prefix; fields; type_; has_variants } ->
      let reason =
        if has_variants then "whose fields belong to its variants and so are not fixed parts"
        else "which has no fields to name"
      in
      make Not_a_field_path (Build.at origin)
        (say
           (match prefix with
           | [] ->
               Printf.sprintf
                 "`%s` is of type `%s`, %s, so a `modifies` clause names no part of it. Remove \
                  `%s`."
                 parameter (Types.show type_) reason
                 (Build.show_field_path parameter fields)
           | _ :: _ ->
               Printf.sprintf "`%s` is of type `%s`, %s. Name `%s` whole in `modifies`."
                 (Build.show_field_path parameter prefix)
                 (Types.show type_) reason
                 (Build.show_field_path parameter prefix)))
  | Opaque_part { at = origin; type_ } ->
      make Private_field (Build.at origin)
        (say
           (Printf.sprintf "`%s` is opaque, so its fields can be named only in its own package."
              (Types.show type_)))
  | Unknown_part_field { at = origin; type_; field; candidates } ->
      make Unknown_member (Build.at origin)
        ~fixes:(Build.list_spelling_fixes origin ~written:field candidates)
        (say (Printf.sprintf "`%s` has no field `%s`." (Types.show type_) field))
  | Part_without_elements { at = origin; parameter; fields; type_ } ->
      make Not_a_field_path (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is of type `%s`, which is no `List` and no `Array`, so it has no elements for \
               `[..]` to name."
              (Build.show_field_path parameter fields)
              (Types.show type_)))
  | Impl_modifies { at = origin; name; parameter; part; trait } ->
      make Impl_modifies (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` names `%s` in `modifies`, and the `modifies` clause of `%s.%s` names no part \
               that holds it. An implementation changes only the parts that its trait's method \
               names."
              name
              (Types.show_modified_part ~root:parameter part)
              trait name))
  | Restated_default { at = origin; name; declared_by } ->
      make Restated_method_default (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, which has a default, and a method with a default has one \
               declaration. A call that omits the argument reads the default from `%s`, and this \
               restatement would be a second declaration that shows none."
              name declared_by name declared_by))
  | Restated_body { at = origin; name; declared_by } ->
      make Restated_method_body (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it has no body: each type's `impl` of `%s` gives the body."
              name declared_by name declared_by))
  | Redeclared_method { at = origin; declared_by; name; receiver } ->
      make Redeclared_method (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` already declares a `%s` that takes %s, and this restatement adds no `ensures` \
               or `cost` clause. Add the clauses that the trait promises, or delete the method."
              declared_by name (Path.show_receiver receiver)))
  | Restated_signature { at = origin; name; declared_by; signature; uses } ->
      make Signature_mismatch (Build.at origin)
        (say
           (Printf.sprintf "`%s` restates `%s.%s`, so it has the signature `%s%s%s`." name
              declared_by name name signature
              (match uses with
              | [] -> ""
              | capabilities ->
                  " uses " ^ String.concat ", " (List.map Types.show_capability capabilities))))
  | Default_without_body { at = origin; type_; default; name } ->
      make Default_without_body (Build.at origin)
        ~fixes:
          [
            {
              title = say "Remove the default";
              edits = [ Build.delete (Stop type_) (Stop default) ];
            };
          ]
        (say
           (Printf.sprintf
              "`%s` has no body, so each `impl` writes it, and a method that an `impl` writes has \
               no default: a call on a known type names the `impl`'s method, which would not show \
               the default. Remove the default, or give `%s` a body."
              name name))
  | Proof_bound_unmet { at = origin; generic; bound } ->
      make Unsatisfied_bound (Build.at origin)
        (say
           (Printf.sprintf
              "The `impl` does not require `%s: %s`, so this proof cannot assume it: the law is \
               proven for every type that the `impl` is for."
              generic (Types.show_trait bound)))
  | Unknown_law { at = origin; trait; law } ->
      make Unknown_member (Build.at origin)
        (say (Printf.sprintf "`%s` has no law `%s`." (Types.show_trait trait) law))
  | Law_without_impl { at = origin; for_type; trait } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not implement `%s`, so it has no law of it to keep."
              (Types.show for_type) (Types.show_trait trait)))
  | Specification_only_field { at = origin; type_ } ->
      make Specification_only (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` exists only in specifications and has no representation in code that runs, so \
               it is not the type of a field."
              (Types.show type_)))
