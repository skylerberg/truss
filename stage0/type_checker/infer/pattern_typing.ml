let order_fields (declared : Types.field list) (matched : (string * Syntax.pattern) list) =
  List.filter_map
    (fun (field : Types.field) ->
      Option.map
        (fun written -> (field.field_name, written))
        (List.assoc_opt field.field_name matched))
    declared

let find_bare_name (inner : Syntax.pattern) =
  match inner.kind with Binding name -> Some name.text | _ -> None

let rec check_binding_pattern state env written type_ ~is_var ~accepts_tuple_pattern ~mode =
  check_pattern_with state env written type_
    ~binding:(if is_var then State.Var else Let)
    ~accepts_tuple_pattern ~mode

and check_pattern state env written type_ ~mode =
  check_pattern_with state env written type_ ~binding:Let ~mode

and check_parameter_pattern state env written type_ ~mode =
  check_pattern_with state env written type_ ~binding:Parameter ~mode

and check_pattern_with ?(accepts_tuple_pattern = false) state env (written : Syntax.pattern) type_
    ~(binding : State.binding) ~mode =
  let is_var = binding = Var in
  let part_binding : State.binding = match binding with Parameter -> Let | Var | Let -> binding in
  let type_ = State.normalize state type_ in
  state.tables.scrutinee_types.((written.id :> int)) <- Some type_;
  let recurse = check_pattern_with state env ~binding:part_binding ~mode in
  let check_unknown type_ =
    check_unknown_pattern state env written type_ ~binding:part_binding ~mode
  in
  let binds local =
    state.tables.patterns.((written.id :> int)) <- Some (Binding_pattern { local; is_var; mode })
  in
  match written.kind with
  | Wildcard | Pattern_error -> ()
  | Binding bound -> (
      match State.find_target state bound with
      | Some Binding ->
          binds bound.id;
          State.declare_compiled state env bound type_ ~binding ~mode
      | Some (Local id) -> (
          binds id;
          match Hashtbl.find_opt state.locals id with
          | Some local ->
              if not (State.unify state local.type_ type_) then
                State.report state Mismatch (State.read_span state bound.id)
                  (Printf.sprintf
                     "`%s` is a `%s` in the first alternative, and a `%s` here; every alternative \
                      binds it with one type."
                     bound.text (State.show state local.type_) (State.show state type_))
          | None -> ())
      | _ -> ())
  | Qualified_constant written_constant ->
      check_qualified_constant state written.id
        (State.read_span state written.id)
        written_constant type_
  | Literal literal ->
      check_literal_pattern state written.id (State.read_span state written.id) literal type_
  | Pattern_range { start; stop; _ } -> (
      match
        Solver.require_within state type_
          (Types.integer_types @ [ Language.Builtin_type.Character; Integer ])
          ~reason:(fun excluded ->
            State.add_diagnostic state Mismatch
              (State.read_span state written.id)
              (Printf.sprintf "A range pattern matches an integer or a `Character`, not %s."
                 (State.describe state excluded)))
      with
      | Types.Error _ when not (Types.is_error type_) -> ()
      | _ ->
          List.iter
            (fun (bound : Syntax.range_end) ->
              match bound.kind with
              | End_literal literal ->
                  check_literal_pattern state bound.id (State.read_span state bound.id) literal
                    type_
              | End_constant constant ->
                  check_qualified_constant state bound.id (State.read_span state bound.id) constant
                    type_)
            [ start; stop ])
  | Variant { name = variant_name; fields } -> (
      match type_ with
      | Types.Named { path; arguments } -> (
          match Members.find_variants state.lookups path arguments with
          | Some variants -> (
              check_fields_visible state (State.read_span state written.id) path type_;
              match
                List.find_opt
                  (fun (variant : Types.variant) -> variant.variant_name = variant_name.text)
                  variants
              with
              | Some variant ->
                  (match (variant.fields, fields) with
                  | Some (_ :: _), None ->
                      State.report state Missing_argument
                        (State.read_span state written.id)
                        ~fixes:
                          [
                            State.fix "Match its fields with `..`."
                              [ State.insert (State.read_span state written.id).stop "(..)" ];
                          ]
                        (Printf.sprintf
                           "`%s` has fields, so its pattern names them, or writes `(..)`."
                           variant.variant_name)
                  | _ -> ());
                  let declared = Option.value ~default:[] variant.fields in
                  let matched =
                    check_pattern_fields state env written declared
                      (Option.value ~default:[] fields) ~binding:part_binding ~mode
                      ~is_tuple_type:false
                      ~declared_order:
                        (lazy
                          (list_in_declared_order state path ~variant:(Some variant.variant_name)
                             declared))
                  in
                  state.tables.patterns.((written.id :> int)) <-
                    Some
                      (Variant_pattern
                         {
                           type_;
                           variant = variant.variant_name;
                           fields = order_fields declared matched;
                         })
              | None ->
                  check_unknown
                  @@ State.make_error_type state Unknown_variant
                       (State.read_span state variant_name.id)
                       ~fixes:
                         (Diagnostic.list_spelling_fixes
                            (State.read_span state variant_name.id)
                            ~written:variant_name.text
                            (List.map
                               (fun (variant : Types.variant) -> variant.variant_name)
                               variants))
                       (Printf.sprintf "`%s` has no variant `%s`." (Types.show type_)
                          variant_name.text))
          | None ->
              check_unknown
                (State.make_error_type state Unknown_variant
                   (State.read_span state written.id)
                   (Printf.sprintf "`%s` has no variants." (Types.show type_))))
      | Types.Error _ | Types.Hole -> check_unknown type_
      | _ ->
          check_unknown
            (State.make_error_type state Unknown_variant
               (State.read_span state written.id)
               (Printf.sprintf "`%s` has no variants." (State.show state type_))))
  | Record fields -> (
      match type_ with
      | Types.Named { path; arguments } -> (
          match Members.find_fields state.lookups path arguments with
          | Some record_fields -> (
              check_fields_visible state (State.read_span state written.id) path type_;
              let is_tuple_type = Members.is_tuple_type state.lookups path in
              match
                if accepts_tuple_pattern && is_tuple_type then
                  find_parenthesized_tuple record_fields fields
                else None
              with
              | Some patterns ->
                  let span = State.read_span state written.id in
                  State.report state Unknown_member span
                    ~fixes:
                      [
                        State.fix "Remove the parentheses."
                          [
                            State.replace
                              (Source.Definition_span.make span.start (span.start + 1))
                              "";
                            State.replace (Source.Definition_span.make (span.stop - 1) span.stop) "";
                          ];
                      ]
                    (Printf.sprintf
                       "`%s` is a tuple type, so a list of patterns without parentheses matches \
                        its fields by position, as in `%s`. In parentheses, fields match by name."
                       (Types.show type_)
                       (State.quote_span state
                          (Source.Definition_span.make (span.start + 1) (span.stop - 1))));
                  check_tuple_fields state env written type_ record_fields patterns
                    ~binding:part_binding ~mode
              | None ->
                  let matched =
                    check_pattern_fields state env written record_fields fields
                      ~binding:part_binding ~mode ~is_tuple_type
                      ~declared_order:
                        (lazy (list_in_declared_order state path ~variant:None record_fields))
                  in
                  state.tables.patterns.((written.id :> int)) <-
                    Some (Record_pattern { type_; fields = order_fields record_fields matched }))
          | None ->
              check_unknown
                (State.make_error_type state Not_a_record
                   (State.read_span state written.id)
                   (Printf.sprintf "%s is not a record."
                      (String.capitalize_ascii (State.describe state type_)))))
      | Types.Error _ | Types.Hole -> check_unknown type_
      | _ ->
          check_unknown
            (State.make_error_type state Not_a_record
               (State.read_span state written.id)
               (Printf.sprintf "%s is not a record."
                  (String.capitalize_ascii (State.describe state type_)))))
  | Tuple patterns -> (
      let check_each type_ = List.iter (fun inner -> recurse inner type_) patterns in
      let span = State.read_span state written.id in
      match type_ with
      | Types.Error _ | Types.Hole -> check_each type_
      | Types.Named { path; arguments } when Members.is_tuple_type state.lookups path -> (
          match Members.find_fields state.lookups path arguments with
          | Some declared when List.length declared = List.length patterns ->
              check_fields_visible state span path type_;
              check_tuple_fields state env written type_ declared patterns ~binding:part_binding
                ~mode
          | Some declared ->
              check_each
                (State.make_error_type state Arity span
                   (Printf.sprintf
                      "`%s` has %d fields, %s, so its tuple pattern has %d patterns, not %d. `_` \
                       skips a field."
                      (Types.show type_) (List.length declared) (show_field_names declared)
                      (List.length declared) (List.length patterns)))
          | None -> State.raise_bug "the tuple type `%s` has no fields" (Types.show type_))
      | Types.Named { path; arguments }
        when Option.is_some (Members.find_fields state.lookups path arguments) ->
          check_each
            (State.make_error_type state Not_a_tuple_type span
               ~fixes:
                 [
                   State.fix "Match its fields by name, in parentheses."
                     [ State.insert span.start "("; State.insert span.stop ")" ];
                 ]
               (Printf.sprintf
                  "`%s` is not a tuple type, so its fields match by name, in parentheses, as in \
                   `(%s)`."
                  (Types.show type_) (State.quote_span state span)))
      | _ ->
          check_each
            (State.make_error_type state Not_a_tuple_type span
               (Printf.sprintf "%s is not a tuple type, so a list of patterns cannot match it."
                  (String.capitalize_ascii (State.describe state type_)))))
  | Alternatives alternatives ->
      List.iter (fun alternative -> recurse alternative type_) alternatives

and check_fields_visible (state : State.state) span path type_ =
  if not (Members.are_fields_visible state.lookups ~package:state.package path) then
    State.report state Private_field span
      (Printf.sprintf "`%s` is opaque, so only its own package can match on it." (Types.show type_))

and find_parenthesized_tuple (declared : Types.field list)
    (written_fields : Syntax.pattern_field list) =
  let patterns =
    List.filter_map
      (fun (field : Syntax.pattern_field) ->
        match field.kind with Field inner -> Some inner | Named_field _ | Rest -> None)
      written_fields
  in
  let positions =
    List.map
      (fun (inner : Syntax.pattern) ->
        match inner.kind with
        | Binding name ->
            List.find_index (fun (field : Types.field) -> field.field_name = name.text) declared
        | _ -> None)
      patterns
  in
  if
    List.length patterns = List.length written_fields
    && List.length patterns = List.length declared
    && List.exists Option.is_none positions
    && List.for_all Fun.id
         (List.mapi
            (fun index position -> match position with Some field -> field = index | None -> true)
            positions)
  then Some patterns
  else None

and list_in_declared_order (state : State.state) path ~variant fields =
  Interface.Definition.sort_in_declared_order state.lookups.interface path ~variant
    ~name_of:(fun (field : Types.field) -> field.field_name)
    fields

and show_field_names (fields : Types.field list) =
  String.concat ", "
    (List.map (fun (declared : Types.field) -> "`" ^ declared.field_name ^ "`") fields)

and check_tuple_fields state env (written : Syntax.pattern) type_ (declared : Types.field list)
    (patterns : Syntax.pattern list) ~binding ~mode =
  let is_field_name name =
    List.exists (fun (field : Types.field) -> field.field_name = name) declared
  in
  let misplaced =
    List.find_map
      (fun ((inner : Syntax.pattern), (field : Types.field)) ->
        match find_bare_name inner with
        | Some name when name <> field.field_name && is_field_name name ->
            Some (name, field.field_name)
        | _ -> None)
      (List.combine patterns declared)
  in
  Option.iter
    (fun (name, bound_field) ->
      let field_names = List.map (fun (field : Types.field) -> field.field_name) declared in
      let bare_names = List.filter_map find_bare_name patterns in
      State.report state Out_of_order
        (State.read_span state written.id)
        ~fixes:
          (if List.sort compare bare_names = List.sort compare field_names then
             [
               State.fix "Put the patterns in the order of the fields."
                 [
                   State.replace (State.read_span state written.id) (String.concat ", " field_names);
                 ];
             ]
           else [])
        (Printf.sprintf
           "The patterns name the fields of `%s` out of order. A tuple pattern matches each field \
            by its position, so `%s` here would bind the field `%s`."
           (Types.show type_) name bound_field))
    misplaced;
  List.iter2
    (fun (inner : Syntax.pattern) (field : Types.field) ->
      check_pattern_with state env inner
        (Solver.flatten state
           (Bound { at = State.read_span state inner.id; of_type = None })
           field.field_type)
        ~binding ~mode)
    patterns declared;
  state.tables.patterns.((written.id :> int)) <-
    Some
      (Record_pattern
         {
           type_;
           fields =
             List.map2
               (fun (field : Types.field) inner -> (field.field_name, inner))
               declared patterns;
         })

and check_pattern_fields state env (written : Syntax.pattern) (fields : Types.field list)
    (written_fields : Syntax.pattern_field list) ~binding ~mode ~is_tuple_type ~declared_order =
  let named =
    List.filter_map
      (fun (field : Syntax.pattern_field) ->
        match field.kind with
        | Named_field (name, _) -> Some name.text
        | Field inner -> (
            match find_bare_name inner with
            | Some name
              when List.exists (fun (declared : Types.field) -> declared.field_name = name) fields
              ->
                Some name
            | _ -> ( match fields with [ only ] -> Some only.field_name | _ -> None))
        | Rest -> None)
      written_fields
  in
  let rest = List.exists (fun (field : Syntax.pattern_field) -> field.kind = Rest) written_fields in
  let flatten (inner : Syntax.pattern) (declared : Types.field) =
    Solver.flatten state
      (Bound { at = State.read_span state inner.id; of_type = None })
      declared.field_type
  in
  let all_matched =
    List.length named
    = List.length
        (List.filter (fun (field : Syntax.pattern_field) -> field.kind <> Rest) written_fields)
  in
  (if (not rest) && all_matched then
     match
       List.filter (fun (declared : Types.field) -> not (List.mem declared.field_name named)) fields
     with
     | [] -> ()
     | missing ->
         State.report state Missing_argument
           (State.read_span state written.id)
           (Printf.sprintf "This pattern does not match %s. Name %s, or write `..` for the rest."
              (String.concat ", "
                 (List.map
                    (fun (declared : Types.field) -> "`" ^ declared.field_name ^ "`")
                    missing))
              (match missing with [ _ ] -> "it" | _ -> "them")));
  List.filter_map
    (fun (position, (field : Syntax.pattern_field)) ->
      match field.kind with
      | Rest -> None
      | Named_field (name, inner) -> (
          match
            List.find_opt (fun (declared : Types.field) -> declared.field_name = name.text) fields
          with
          | Some declared ->
              check_pattern_with state env inner (flatten inner declared) ~binding ~mode;
              Some (declared.field_name, inner)
          | None ->
              check_pattern_with state env inner ~binding ~mode
              @@ State.make_error_type state Unknown_member (State.read_span state name.id)
                   ~fixes:
                     (Diagnostic.list_spelling_fixes (State.read_span state name.id)
                        ~written:name.text
                        (List.map (fun (declared : Types.field) -> declared.field_name) fields))
                   (Printf.sprintf "There is no field `%s` here." name.text);
              None)
      | Field inner -> (
          let field_of_name =
            Option.bind (find_bare_name inner) (fun name ->
                List.find_opt (fun (declared : Types.field) -> declared.field_name = name) fields)
          in
          match (field_of_name, fields) with
          | Some declared, _ | None, [ declared ] ->
              check_pattern_with state env inner (flatten inner declared) ~binding ~mode;
              Some (declared.field_name, inner)
          | None, _ ->
              let span = State.read_span state inner.id in
              let fixes =
                match List.nth_opt (Lazy.force declared_order) position with
                | Some (declared : Types.field) when not (List.mem declared.field_name named) ->
                    [
                      State.fix
                        (Printf.sprintf "Write `%s: %s`." declared.field_name
                           (State.quote_span state span))
                        [ State.insert span.start (declared.field_name ^ ": ") ];
                    ]
                | _ -> []
              in
              check_pattern_with state env inner ~binding ~mode
                (State.make_error_type state Unknown_member span ~fixes
                   (Printf.sprintf
                      "A bare pattern must name a field, since this has %d fields: %s. In \
                       parentheses, fields match by name.%s"
                      (List.length fields) (show_field_names fields)
                      (if is_tuple_type then
                         " A list of patterns without parentheses, after `let`, `var`, or `for`, \
                          matches the fields of this tuple type by position."
                       else "")));
              None))
    (List.mapi (fun position field -> (position, field)) written_fields)

and check_unknown_pattern state env (written : Syntax.pattern) unknown ~binding ~mode =
  state.tables.scrutinee_types.((written.id :> int)) <- Some unknown;
  match written.kind with
  | Variant { fields = Some fields; _ } | Record fields ->
      List.iter
        (fun (field : Syntax.pattern_field) ->
          match field.kind with
          | Named_field (_, inner) | Field inner ->
              check_pattern_with state env inner unknown ~binding ~mode
          | Rest -> ())
        fields
  | _ -> ()

and check_constant_pattern (state : State.state) (id : Syntax.id) span path type_ =
  state.tables.patterns.((id :> int)) <- Some (Constant_pattern path);
  match Interface.Definition.find_constant_type state.lookups.interface path with
  | Some constant_type ->
      if not (State.unify state constant_type type_) then
        Failures.report_mismatch state span ~expected:type_ ~actual:constant_type
      else if not (is_structural state (State.resolve state constant_type)) then
        State.report state Not_structural span
          (Printf.sprintf
             "A constant in a pattern needs a type with structural equality, whose `==` compares \
              contents, because the checks that a `match` covers every case and that every arm is \
              reachable compare constants by their contents. `%s` does not have it: its equality \
              is hand-written, or it holds a float, whose `==` treats `-0.0` and `0.0` as equal. \
              Match with a guard instead, as in `value if value == %s`."
             (State.show state constant_type)
             (match path with
             | Top { name; _ } | Member_constant { name; _ } | Method { name; _ } -> name
             | _ -> "the_constant"))
  | None -> ()

and is_structural ?(seen = []) state (type_ : Types.ty) =
  if
    State.is_within state type_ Types.integer_types
    || Types.is_builtin Bool type_ || Types.is_builtin Character type_
    || Types.is_builtin Unit type_ || Types.is_well_known String type_
  then true
  else if Types.is_float_type type_ then false
  else if List.exists (Types.equal type_) seen then true
  else
    match type_ with
    | Types.Named { path; arguments } -> (
        match Interface.Definition.find_interface state.lookups.interface path with
        | Some (Interface.Environment.Type_interface interface)
          when (not interface.opaque) || Path.locate_package path = state.package ->
            let derives_equal =
              List.exists (fun derived -> Well_known.is Equal derived) interface.derives
            in
            let substitution = Types.make_substitution interface.type_generics arguments in
            let are_fields_structural (fields : Types.field list) =
              List.for_all
                (fun (field : Types.field) ->
                  is_structural ~seen:(type_ :: seen) state
                    (Types.substitute substitution field.field_type))
                fields
            in
            derives_equal
            && begin match interface.shape with
            | Record fields -> are_fields_structural fields
            | Sum variants ->
                List.for_all
                  (fun (variant : Types.variant) ->
                    match variant.fields with
                    | Some fields -> are_fields_structural fields
                    | None -> true)
                  variants
            | Todo_type | Builtin_type _ -> false
            end
        | _ -> false)
    | _ -> false

and check_qualified_constant state id span constant type_ =
  let constant_lookup : Path.t Resolve.Names.lookup =
    match constant with
    | Module_constant written_path -> (
        match State.find_target state written_path.last with
        | Some (Definition (Constant, path)) -> Visible path
        | _ -> Absent)
    | Type_constant (written_path, member) -> (
        match State.find_target state written_path.last with
        | Some (Definition (Type, owner)) ->
            Members.lookup_member state (Member_constant { owner; name = member.text })
        | _ -> Absent)
  in
  match constant_lookup with
  | Visible path -> check_constant_pattern state id span path type_
  | Hidden hidden -> ignore (Members.make_hidden_error state span hidden)
  | Absent -> State.report state Unknown_member span "This names no constant."

and report_out_of_range state span number excluded =
  let low, high = State.read_integer_range state excluded in
  State.add_diagnostic state Literal_out_of_range span
    (Printf.sprintf "`%s` does not fit in %s, which holds %s to %s." (Z.to_string number)
       (State.describe state excluded) (Z.to_string low) (Z.to_string high))

and report_negated_unsigned state (value : Syntax.expression) excluded =
  State.add_diagnostic state Negated_unsigned (State.read_span state value.id)
    (Printf.sprintf "%s %s unsigned, so it cannot be negated."
       (String.capitalize_ascii (State.describe state excluded))
       (if State.is_within state excluded Types.unsigned_integer_types then "is" else "may be"))

and check_integer_literal state (env : State.env) ?expected (value : Syntax.expression) number =
  let span = State.read_span state value.id in
  match
    ( Option.map (State.resolve state) expected,
      Types.list_fitting_integer_types number
      @ if env.specification then [ Language.Builtin_type.Integer ] else [] )
  with
  | Some Types.Integer, _ -> Types.Integer
  | _, [] ->
      State.make_error_type state Literal_out_of_range span
        (Printf.sprintf "`%s` does not fit in any integer type." (Z.to_string number))
  | _, allowed ->
      State.make_literal_type state value allowed ~report_excluded:(fun excluded ->
          if Z.sign number < 0 && not (State.is_within state excluded Types.signed_integer_types)
          then report_negated_unsigned state value excluded
          else report_out_of_range state span number excluded)

and find_character_tag state (literal : Syntax.string_literal) =
  match literal.tag with
  | Some tag -> (
      match State.find_target state tag.last with
      | Some (Definition (Type, path)) -> (
          match Well_known.find_builtin_type path with
          | Some ((Character | UInt8) as builtin) -> Some builtin
          | _ -> None)
      | _ -> None)
  | None -> None

and check_character_value (state : State.state) (literal : Syntax.string_literal)
    (builtin : Language.Builtin_type.t) =
  let text = literal.first.value in
  let scalars =
    let rec count index scalars =
      if index >= String.length text then List.rev scalars
      else
        let decoded = String.get_utf_8_uchar text index in
        count (index + Uchar.utf_decode_length decoded) (Uchar.utf_decode_uchar decoded :: scalars)
    in
    count 0 []
  in
  let value =
    match (literal.rest, scalars, builtin) with
    | [], [ scalar ], Character -> Some (Uchar.to_int scalar)
    | [], [ scalar ], UInt8 when Uchar.to_int scalar < 128 -> Some (Uchar.to_int scalar)
    | _ -> None
  in
  match value with
  | Some value -> Some (Z.of_int value)
  | None ->
      State.report state Character_scalar_count
        (State.read_span state literal.id)
        (match builtin with
        | Character ->
            "`Character\"...\"` holds exactly one Unicode scalar value, with no `${...}`."
        | _ -> "`UInt8\"...\"` holds exactly one ASCII character, with no `${...}`.");
      None

and check_character_literal state id literal builtin =
  Option.iter
    (fun value -> State.elaborate state id (Literal (Integer_value value)))
    (check_character_value state literal builtin);
  Types.make_builtin builtin

and check_literal_pattern state id (span : Source.Definition_span.t) literal type_ =
  let record_integer integer =
    state.tables.patterns.((id :> int)) <- Some (Literal_pattern integer)
  in
  match literal with
  | Literal_integer number ->
      record_integer number;
      ignore
        (Solver.require_within state type_
           (Types.list_fitting_integer_types number @ [ Language.Builtin_type.Integer ])
           ~reason:(fun excluded ->
             if State.is_within state excluded Types.integer_types then
               report_out_of_range state span number excluded
             else
               State.add_diagnostic state Mismatch span
                 (Printf.sprintf "An integer pattern matches an integer, not %s."
                    (State.describe state excluded))))
  | Literal_true | Literal_false ->
      if not (State.unify state type_ Types.bool) then
        Failures.report_mismatch state span ~expected:type_ ~actual:Types.bool
  | Literal_string tagged -> (
      match find_character_tag state tagged with
      | Some builtin ->
          Option.iter record_integer (check_character_value state tagged builtin);
          if not (State.unify state type_ (Types.make_builtin builtin)) then
            Failures.report_mismatch state span ~expected:type_ ~actual:(Types.make_builtin builtin)
      | None -> check_string_pattern state span type_)

and check_string_pattern state span type_ =
  if
    not
      (Types.is_well_known String type_
      || Types.is_well_known String_slice type_
      || Types.is_error type_)
  then
    State.report state Mismatch span
      (Printf.sprintf "A string pattern matches a string, not `%s`." (Types.show type_))
