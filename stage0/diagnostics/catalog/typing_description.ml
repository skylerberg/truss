let make ?(fixes = []) code location message : Nodes.description =
  { code = Types code; severity = Error; location; message; notes = []; fixes }

let tick written = [ Description.Text "`"; Build.quote_over written; Text "`" ]
let tick_node origin = [ Description.Text "`"; Build.quote origin; Text "`" ]

let show_generic (generic : Types.generic) =
  match generic.kind with
  | Type_generic [] -> generic.generic.name
  | Type_generic bounds ->
      generic.generic.name ^ ": " ^ String.concat " + " (List.map Types.show_trait bounds)
  | Value_generic -> generic.generic.name ^ ": UInt64"

let show_signature (signature : Types.signature) =
  Printf.sprintf "%s(%s)%s"
    (match signature.generics with
    | [] -> ""
    | generics -> "[" ^ String.concat ", " (List.map show_generic generics) ^ "]")
    (String.concat ", "
       ((match signature.receiver with
          | Some (mode, _) -> [ Language.Mode.show_prefix mode ^ "self" ]
          | None -> [])
       @ List.map
           (fun (parameter : Types.parameter_info) ->
             Printf.sprintf "%s: %s%s%s" parameter.name
               (Language.Mode.show_prefix parameter.mode)
               (Types.show parameter.type_)
               (if parameter.has_default then " = ..." else ""))
           signature.parameters))
    (Types.show_output signature.output)

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
  | Ambiguous_associated { at = origin; base; name; associated; traits } ->
      let listed =
        String.concat ", " (List.map (fun trait -> "`" ^ Types.show_trait trait ^ "`") traits)
      in
      let advice =
        match (associated, base, traits) with
        | Associated_type, Parameter parameter, first :: _
          when not (Types.is_self_parameter parameter) ->
            Printf.sprintf
              " Name it through a type parameter that one of them fixes, as in `%s: %s[%s]`."
              parameter.name (Path.show_name first.trait)
              (String.concat ", "
                 (List.map Types.show_argument first.trait_arguments @ [ name ^ " = " ^ name ]))
        | _ -> ""
      in
      make Ambiguous_associated (Build.at origin)
        (say
           (Printf.sprintf "More than one trait gives `%s` an %s `%s`: %s.%s" (Types.show base)
              (show_associated associated) name listed advice))
  | Self_defined_associated { at = origin; name; associated } ->
      make
        (match associated with
        | Associated_type -> Unknown_associated_type
        | Associated_capability_set -> Unknown_associated_capability)
        (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is defined from itself, or from an %s that this `impl` defines after it." name
              (show_associated associated)))
  | Arity { at = origin; written; expected; given } ->
      make Arity (Build.at origin)
        (tick written
        @ say
            (Printf.sprintf " takes %s, and %s given."
               (Diagnostic.show_count expected "argument" "arguments")
               (Diagnostic.show_count given "is" "are")))
  | Head_arity { at = origin; written; expected; given } ->
      make Arity (Build.at origin)
        (tick written
        @ say
            (Printf.sprintf " takes %s, and this head names %d."
               (Diagnostic.show_count expected "generic parameter" "generic parameters")
               given))
  | Argument_kind { at = origin; written; parameter; mismatch } ->
      make Argument_kind (Build.at origin)
        (tick written
        @ say
            (match mismatch with
            | Value_for_type ->
                Printf.sprintf "'s parameter `%s` is a `UInt64` value, not a type." parameter
            | Type_for_value -> Printf.sprintf "'s parameter `%s` is a type, not a value." parameter)
        )
  | Constraint_in_type_arguments { at = origin } ->
      make Arity (Build.at origin)
        (say
           "An associated type is fixed in a bound, as in `Source: Cursor[Element = Int64]`, not \
            among type arguments.")
  | Arguments_to_parameter { at = origin; written } ->
      make Arity (Build.at origin)
        (tick written @ say " is a generic parameter, which takes no arguments.")
  | Count_error { at = origin; error } ->
      make Arity (Build.at origin)
        (match error with
        | Not_uint64 ->
            tick_node origin @ say " in a type argument must be a constant of type `UInt64`."
        | Uncomputable ->
            say "The value of " @ tick_node origin
            @ say
                " cannot be computed: a constant used in a type cannot refer to itself, and is \
                 made of literals, arithmetic, and other such constants.")
  | Trait_as_type { at = origin; written } ->
      make Not_a_type (Build.at origin)
        (tick written
        @ say " is a trait, not a type. A type parameter can have it as a bound, as in `[Item: "
        @ [ Build.quote_over written ]
        @ say "]`.")
  | Capability_as_type { at = origin; written } ->
      make Not_a_type (Build.at origin) (tick written @ say " is a capability, not a type.")
  | Head_not_a_type { at = origin; written; kind } ->
      make Not_a_type (Build.at origin)
        (tick written
        @ say
            (Printf.sprintf " is %s, not a type, so it has no methods, constants, or `impl`s."
               (show_kind kind)))
  | Not_a_trait { at = origin; written; is_parameter } ->
      make Not_a_trait (Build.at origin)
        (tick written
        @ say (if is_parameter then " is a generic parameter, not a trait." else " is not a trait.")
        )
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
        (if is_type_parameter then
           tick written
           @ say
               " is a type parameter, not a capability. A capability parameter is written `generic "
           @ [ Build.quote_over written ]
           @ say "` at each use."
         else tick written @ say " is not a capability.")
  | Calls_not_a_capability { at = origin; written } ->
      make Not_a_capability (Build.at origin)
        (say "`calls` counts the calls of a capability, and " @ tick written @ say " is not one.")
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
        (tick written @ say (Printf.sprintf " has no method `%s`." method_))
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
        (say
           (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares." name
              (Path.show_name trait)))
  | Missing_method { at = origin; name; signature; trait } ->
      make Missing_member (Build.at origin)
        (say
           (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares." name
              (show_signature signature) (Path.show_name trait)))
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
              (Path.show_name trait)))
  | Associated_bound_unmet { at = origin; trait; name; bound; chosen } ->
      make Unsatisfied_bound (Build.at origin)
        (say
           (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one."
              (Path.show_name trait) name (Types.show_trait bound) (Types.show chosen)))
  | Extra_associated { at = origin; trait; name; associated } ->
      make Extra_member (Build.at origin)
        (say
           (Printf.sprintf "`%s` declares no %s `%s`." (Path.show_name trait)
              (show_associated associated) name))
  | Defined_twice { at = origin; name; associated } ->
      make Duplicate_member (Build.at origin)
        (say
           (match associated with
           | Associated_type -> Printf.sprintf "This `impl` already defines `%s`." name
           | Associated_capability_set ->
               Printf.sprintf
                 "This `impl` already defines `%s`. List every capability in one definition, \
                  separated by commas."
                 name))
  | Missing_required_impl { at = origin; trait; required; for_type } ->
      make Missing_required_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement."
              (Path.show_name trait) (Types.show_trait required) (Types.show for_type)))
  | Uses_on_trait_impl { at = origin } ->
      make Impl_uses (Build.at origin)
        (say
           "Only an `impl` of a capability can have `uses`. A trait's methods can use only the \
            capabilities the trait declares.")
  | Callback_contract_mismatch { at = origin; name; trait; parameter; declaration; clauses } ->
      make Signature_mismatch (Build.at origin)
        (Description.Text
           (Printf.sprintf "`%s` must state the callback contract that `%s` declares for `%s`: "
              name (Path.show_name trait) parameter)
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
               (Path.show_name trait)))
  | Restated_without_own { at = origin; trait; declared_by; name; for_type } ->
      make Extra_member (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s` and declares no method of its own by that name. Give `%s` in \
               the `impl` of `%s` for `%s`."
              (Path.show_name trait) (Path.show declared_by) name name (Path.show declared_by)
              (Types.show for_type)))
  | Undeclared_method { at = origin; trait; name } ->
      make Extra_member (Build.at origin)
        (say
           (Printf.sprintf "`%s` declares no method `%s` with this receiver." (Path.show_name trait)
              name))
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
              (Path.show_name trait) name (Path.show_name trait)))
  | Impl_signature_mismatch { at = origin; name; signature; trait } ->
      make Signature_mismatch (Build.at origin)
        (say
           (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name name
              (show_signature signature) (Path.show_name trait)))
  | Uses_beyond_impl { at = origin; name } ->
      make Impl_uses (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` implements a capability, so it can use only the capabilities its `impl` \
               declares with `uses`."
              name))
  | Uses_beyond_trait { at = origin; name; trait } ->
      make Impl_uses (Build.at origin)
        (say
           (Printf.sprintf "`%s` can use only the capabilities `%s` declares for it." name
              (Path.show_name trait)))
  | Panic_beyond_condition { at = origin; name; trait } ->
      make Impl_uses (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` declares `%s` with `uses Panic unless` a condition, and this `%s` uses `Panic` \
               without one, so it could panic where that condition holds. Declare `uses Panic \
               unless` a condition that `%s`'s implies."
              (Path.show_name trait) name name (Path.show_name trait)))
  | Bound_unmet { at = origin; definition; arguments; argument; bound } ->
      make Unsatisfied_bound (Build.at origin)
        (say
           (Printf.sprintf "`%s[%s]` needs `%s: %s`, which does not hold here."
              (Path.show_name definition)
              (String.concat ", " (List.map Types.show_argument arguments))
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
        (tick written
        @ say
            (Printf.sprintf
               " has no real implementation, so the runtime cannot provide it to %s. Provide an \
                implementation in the body with `provide`."
               (show_recipient recipient)))
  | Main_signature { at = origin } ->
      make Main_signature (Build.at origin)
        (say
           "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`.")
  | Duplicate_member { at = origin; member_kind; name } ->
      let member, container =
        match member_kind with
        | Field_member -> ("field", "type")
        | Variant_member -> ("variant", "type")
        | Associated_type_member -> ("associated type", "trait")
        | Capability_set_member -> ("associated capability set", "trait")
        | Law_member -> ("law", "trait")
      in
      make Duplicate_member (Build.at origin)
        (say (Printf.sprintf "Another %s of this %s is already named `%s`." member container name))
  | Not_derivable { at = origin; written } ->
      make Not_derivable (Build.at origin)
        (say
           "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, `Plain`, \
            `serialization.Serialize`, and `serialization.Deserialize` can be derived, not "
        @ tick written @ say ".")
  | Derives_inferred { at = origin; written; entry; siblings } ->
      make Derives_inferred (Build.at origin)
        ~fixes:
          [
            { title = say "Remove the declaration."; edits = [ Build.remove_entry entry siblings ] };
          ]
        (say "Whether " @ tick written
        @ say
            " holds for this type is derived from its fields, which are visible. Only an opaque \
             type declares it.")
  | Repeated_derive { at = origin; written; entry; siblings } ->
      make Repeated_derive (Build.at origin)
        ~fixes:[ { title = say "Remove it."; edits = [ Build.remove_entry entry siblings ] } ]
        (say "The type already derives " @ tick written @ say ".")
  | Field_not_derivable { at = origin; written } ->
      make Cannot_derive (Build.at origin)
        (say "A field of this type is not " @ tick written @ say ", so the type cannot be.")
  | Potential_not_plain { at = origin } ->
      make Cannot_derive (Build.at origin)
        (say
           "A type that declares a `cost potential` is not `Plain`: an implicit copy would \
            duplicate the potential, and a caller could spend it twice. Derive `Copyable`, whose \
            `copy()` pays for the potential of the copy.")
  | Default_of_sum { at = origin } ->
      make Cannot_derive (Build.at origin)
        (say
           "`Default` is derived as each field's default, so only a record can derive it: no \
            variant of this type is its default. Write the `impl`, which says which variant is.")
  | Derived_without_equal { at = origin; written } ->
      make Cannot_derive (Build.at origin)
        (say "Deriving " @ tick written
        @ say " needs `Equal` to be derived too, so that the two agree.")
  | Field_lacks_impl { at = origin; type_; written } ->
      make Cannot_derive (Build.at origin)
        (say (Printf.sprintf "A field of type `%s` does not implement " (Types.show type_))
        @ tick written @ say ", so " @ tick written @ say " cannot be derived.")
  | Trait_cycle { at = origin } ->
      make Trait_cycle (Build.at origin)
        (say "This trait requires itself through the traits it requires.")
  | Restated_requires { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. A caller \
               through `%s` would never prove this `requires`."
              name (Path.show declared_by) name (Path.show declared_by)))
  | Restated_decreases { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. It has no \
               body, so it has no recursion to measure."
              name (Path.show declared_by) name))
  | Restated_modifies { at = origin; name; declared_by } ->
      make Restated_method_clause (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. The parts that \
               its implementations change are those that `%s.%s` names."
              name (Path.show declared_by) name (Path.show declared_by) name))
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
              (Path.show_name trait) name))
  | Restated_default { at = origin; name; declared_by } ->
      make Restated_method_default (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, which has a default, and a method with a default has one \
               declaration. A call that omits the argument reads the default from `%s`, and this \
               restatement would be a second declaration that shows none."
              name (Path.show declared_by) name (Path.show declared_by)))
  | Restated_body { at = origin; name; declared_by } ->
      make Restated_method_body (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` restates `%s.%s`, so it has no body: each type's `impl` of `%s` gives the body."
              name (Path.show declared_by) name (Path.show declared_by)))
  | Redeclared_method { at = origin; declared_by; name; receiver } ->
      make Redeclared_method (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` already declares a `%s` that takes %s, and this restatement adds no `ensures` \
               or `cost` clause. Add the clauses that the trait promises, or delete the method."
              (Path.show declared_by) name (Path.show_receiver receiver)))
  | Restated_signature { at = origin; name; declared_by; signature } ->
      make Signature_mismatch (Build.at origin)
        (say
           (Printf.sprintf "`%s` restates `%s.%s`, so it has the signature `%s%s%s`." name
              (Path.show declared_by) name name (show_signature signature)
              (match Types.list_capabilities signature.uses with
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
