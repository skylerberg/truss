let items : Well_known.t list =
  [
    Option;
    Result;
    Fixed_width_integer;
    Signed_integer;
    Unsigned_integer;
    Floating_point;
    Equal;
    Ordered;
    Ordering;
    Hash;
    Hasher;
    Default;
    Display;
    From;
    Try_from;
    Copyable;
    Plain;
    Storable;
    Add;
    Subtract;
    Multiply;
    Divide;
    Remainder;
    Negate;
    Index;
    Index_mut;
    Index_assign;
    Model;
    Iterable;
    Cursor;
    Range;
    Exit_code;
    String;
    String_slice;
    From_template;
    Template;
    List;
    Slice;
    From_elements;
    Sequence;
    Finite_set;
    Finite_map;
    Multiset;
    Map;
    From_entries;
    Set;
    System_error;
    Instant;
    Duration;
    File_path;
  ]

let locate (path : Path.t) =
  match path with
  | Top { module_; name } -> (name, module_)
  | _ ->
      Compiler_bug.raise_bug ~stage:"Resolve" "the prelude's `%s` is not a top-level definition"
        (Path.show path)

let types =
  List.map locate
    (List.filter_map
       (fun (builtin : Language.Builtin_type.t) ->
         match builtin with
         | Storage | View | Handle | Shared -> None
         | _ -> Some (Well_known.make_builtin_type_path builtin))
       Language.Builtin_type.all
    @ List.map Well_known.make_path items)
  @ List.map (fun name -> (name, Grant.prelude_capability_module)) Grant.prelude_capabilities

let variants : Well_known.variant list = [ Option_some; Option_none; Result_ok; Result_err ]
let find_type name = List.assoc_opt name types

let find_variant name =
  List.find_map
    (fun variant ->
      if Well_known.show_variant variant = name then
        Some (Well_known.make_variant_type_path variant, name)
      else None)
    variants

let names = List.map fst types @ List.map Well_known.show_variant variants
