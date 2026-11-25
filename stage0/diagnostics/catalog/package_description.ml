let make ?(fixes = []) code location message : Nodes.description =
  { code = Package code; severity = Error; location; message; notes = []; fixes }

let not_strictly_positive =
  "A function stored in such a value could be called on the value and call itself through it, so a \
   function without `RunForever` might run forever. Add `RunForever` to the function type's \
   `uses`, or pass the function the fields that it needs instead of the whole value."

let describe_holder method_name = function
  | Package.Own -> Printf.sprintf "a `%s` of its own" method_name
  | Of_list list ->
      Printf.sprintf "the `%s` of `%s`, whose methods an `Array` has" method_name (Types.show list)

let describe : Package.t -> Nodes.description = function
  | Impl_location { header; trait; for_type } ->
      make Impl_location (Build.at header)
        [
          Text
            (Printf.sprintf
               "This `impl` must be in the package of `%s`, of `%s`, or of a type its trait's \
                arguments name, so that only one place can hold it."
               (Types.show_trait trait) (Types.show for_type));
        ]
  | Sealed_trait_impl { header; trait; type_; is_floating_point } ->
      let implementors, reason =
        if is_floating_point then
          ( "the built-in float types",
            "the trait describes the IEEE 754 formats of `Float32` and `Float64`, which its `Bits` \
             and methods such as `is_nan` expose" )
        else ("the built-in integer types", "generic code over the trait is proven for each of them")
      in
      make Sealed_trait_impl (Build.at header)
        [
          Text
            (Printf.sprintf "Only %s implement `%s`, so `%s` cannot: %s." implementors
               (Path.show trait) (Path.show type_) reason);
        ]
  | Method_name_clash { header; for_type; method_name; holder; clash } ->
      let held = describe_holder method_name holder in
      make Method_name_clash (Build.at header)
        [
          Text
            (match clash with
            | Same_receiver { receiver; trait } ->
                Printf.sprintf "`%s` has %s, which takes %s, so it cannot also get one from `%s`."
                  (Types.show for_type) held (Path.show_receiver receiver) (Types.show_trait trait)
            | Other_package ->
                Printf.sprintf
                  "`%s` has %s, so only an `impl` in its own package can give it another."
                  (Types.show for_type) held
            | Unwritten { trait } ->
                Printf.sprintf
                  "`%s` has %s, so this `impl` can give it another only by writing it, and `%s` is \
                   left to the body `%s` provides."
                  (Types.show for_type) held method_name (Types.show_trait trait));
        ]
  | Overlapping_impls { header; trait; for_type } ->
      make Overlapping_impls (Build.at header)
        [
          Text
            (Printf.sprintf
               "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at most one \
                `impl` of a trait for each set of its arguments."
               (Types.show_trait trait) (Types.show for_type));
        ]
  | Variant_in_place { variant } ->
      make Needs_indirect (Build.at variant)
        ~fixes:
          [
            {
              title = [ Text "Declare the variant `indirect`." ];
              edits = [ Build.insert_before variant [ Text "indirect " ] ];
            };
          ]
        [
          Text
            "This type contains itself in place, so it would be infinitely large. Declare the \
             variant `indirect` to keep its fields on the heap.";
        ]
  | Record_in_place { header } ->
      make Needs_indirect (Build.at header)
        [
          Text
            "This record contains itself in place, so it would be infinitely large. A record has \
             no variant to declare `indirect`; use a sum type with an `indirect` variant, or a \
             collection.";
        ]
  | Associated_type_in_place { member; name; recursive } ->
      make Needs_indirect (Build.at member)
        [
          Text
            (Printf.sprintf
               "With this definition of `%s`, `%s` contains itself in place, so it would be \
                infinitely large. Define `%s` as a type that holds it in a collection or in an \
                `indirect` variant."
               name (Types.show recursive) name);
        ]
  | Function_input_field { field; type_name } ->
      make Not_strictly_positive (Build.at field)
        [
          Text
            (Printf.sprintf
               "Through this field, `%s` contains a function type that has a `time` clause and \
                whose input contains `%s`. %s"
               type_name type_name not_strictly_positive);
        ]
  | Associated_function_input { member; name; recursive } ->
      make Not_strictly_positive (Build.at member)
        [
          Text
            (Printf.sprintf
               "With this definition of `%s`, `%s` contains a function type that has a `time` \
                clause and whose input contains `%s`. %s"
               name (Types.show recursive) (Types.show recursive) not_strictly_positive);
        ]
  | Growing_type { header } ->
      make Growing_type (Build.at header)
        [
          Text
            "This type contains itself with different type arguments, so it has no fixed set of \
             instances, and generic code is compiled once for each set of arguments.";
        ]
  | Instantiation_cycle { header } ->
      make Instantiation_cycle (Build.at header)
        [
          Text
            "This generic code instantiates itself with type arguments that grow each time around, \
             so it would be compiled without end.";
        ]
  | Duplicate_test { name } ->
      make Duplicate_test (At Definition)
        [ Text (Printf.sprintf "Another test of this package is named %S." name) ]
