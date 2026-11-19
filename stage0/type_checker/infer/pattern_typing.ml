let rec check_binding_pattern state env written type_ ~is_var ~mode =
  check_pattern_with state env written type_ ~binding:(if is_var then State.Var else Let) ~mode

and check_pattern state env written type_ ~mode =
  check_pattern_with state env written type_ ~binding:Let ~mode

and check_parameter_pattern state env written type_ ~mode =
  check_pattern_with state env written type_ ~binding:Parameter ~mode

and check_pattern_with state env (written : Syntax.pattern) type_ ~(binding : State.binding) ~mode =
  let is_var = binding = Var in
  let part_binding : State.binding = match binding with Parameter -> Let | Var | Let -> binding in
  let type_ = State.normalize state type_ in
  state.tables.scrutinee_types.(written.id) <- Some type_;
  let recurse = check_pattern_with state env ~binding:part_binding ~mode in
  let check_unknown type_ =
    check_unknown_pattern state env written type_ ~binding:part_binding ~mode
  in
  let binds id (bound : Syntax.name) =
    State.register_pattern state written (fun () ->
        Bind { local = Declared { origin = id; name = bound.text }; is_var; mode })
  in
  match written.kind with
  | Wildcard | Pattern_error -> State.register_pattern state written (fun () -> Wildcard)
  | Binding bound -> (
      match State.find_target state bound with
      | Some Binding ->
          binds bound.id bound;
          State.declare_compiled state env bound type_ ~binding ~mode
      | Some (Local id) -> (
          binds id bound;
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
      State.register_pattern state written (fun () ->
          Form.build_constant_pattern state written.id (Form.build_named_constant state written.id));
      check_qualified_constant state written.id
        (State.read_span state written.id)
        written_constant type_
  | Literal literal ->
      State.register_pattern state written (fun () ->
          Form.build_constant_pattern state written.id
            (Form.build_literal_constant state written.id literal));
      check_literal_pattern state written.id (State.read_span state written.id) literal type_
  | Pattern_range { start; stop; inclusive } -> (
      State.register_pattern state written (fun () ->
          Range
            {
              start = Form.build_range_bound state start;
              stop = Form.build_range_bound state stop;
              inclusive;
            });
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
              if not (Members.are_fields_visible state.lookups ~package:state.package path) then
                State.report state Private_field
                  (State.read_span state written.id)
                  (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
                     (Types.show type_));
              match
                List.find_opt
                  (fun (variant : Types.variant) -> variant.variant_name = variant_name.text)
                  variants
              with
              | Some variant ->
                  state.tables.patterns.(written.id) <-
                    Some (Variant_pattern { type_; variant = variant.variant_name });
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
                  in
                  State.register_pattern state written (fun () ->
                      Variant
                        {
                          variant = variant.variant_name;
                          fields = Form.build_pattern_fields state declared matched;
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
          | Some record_fields ->
              if not (Members.are_fields_visible state.lookups ~package:state.package path) then
                State.report state Private_field
                  (State.read_span state written.id)
                  (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
                     (Types.show type_));
              state.tables.patterns.(written.id) <- Some (Record_pattern { type_ });
              let matched =
                check_pattern_fields state env written record_fields fields ~binding:part_binding
                  ~mode
              in
              State.register_pattern state written (fun () ->
                  Record (Form.build_pattern_fields state record_fields matched))
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
  | Alternatives alternatives ->
      List.iter (fun alternative -> recurse alternative type_) alternatives;
      State.register_pattern state written (fun () ->
          Alternatives (List.map (State.build_pattern state) alternatives))

and check_pattern_fields state env (written : Syntax.pattern) (fields : Types.field list)
    (written_fields : Syntax.pattern_field list) ~binding ~mode =
  let find_bare_name (inner : Syntax.pattern) =
    match inner.kind with Binding name -> Some name.text | _ -> None
  in
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
    (fun (field : Syntax.pattern_field) ->
      match field.kind with
      | Rest -> None
      | Named_field (name, inner) -> (
          match
            List.find_opt (fun (declared : Types.field) -> declared.field_name = name.text) fields
          with
          | Some declared ->
              check_pattern_with state env inner declared.field_type ~binding ~mode;
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
          let named =
            Option.bind (find_bare_name inner) (fun name ->
                List.find_opt (fun (declared : Types.field) -> declared.field_name = name) fields)
          in
          match (named, fields) with
          | Some declared, _ | None, [ declared ] ->
              check_pattern_with state env inner declared.field_type ~binding ~mode;
              Some (declared.field_name, inner)
          | None, _ ->
              let names =
                String.concat ", "
                  (List.map
                     (fun (declared : Types.field) -> "`" ^ declared.field_name ^ "`")
                     fields)
              in
              check_pattern_with state env inner ~binding ~mode
                (State.make_error_type state Unknown_member (State.read_span state inner.id)
                   (Printf.sprintf
                      "A bare pattern must name a field, since this has %d fields: %s. Truss has \
                       no tuples, so fields match by name."
                      (List.length fields) names));
              None))
    written_fields

and check_unknown_pattern state env (written : Syntax.pattern) unknown ~binding ~mode =
  state.tables.scrutinee_types.(written.id) <- Some unknown;
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

and check_constant_pattern (state : State.state) id span path type_ =
  state.tables.patterns.(id) <- Some (Constant_pattern path);
  match Interface.Definition.find_constant_type state.lookups.interface path with
  | Some constant_type ->
      if not (State.unify state constant_type type_) then
        State.report_mismatch state span ~expected:type_ ~actual:constant_type
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
      State.make_literal_type state ~at:span allowed ~report_excluded:(fun excluded ->
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

and check_character_value (state : State.state) id (literal : Syntax.string_literal)
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
  | Some value -> state.tables.literals.(id) <- Some (Integer_value (Z.of_int value))
  | None ->
      State.report state Character_scalar_count
        (State.read_span state literal.id)
        (match builtin with
        | Character ->
            "`Character\"...\"` holds exactly one Unicode scalar value, with no `${...}`."
        | _ -> "`UInt8\"...\"` holds exactly one ASCII character, with no `${...}`.")

and check_character_literal state id literal builtin =
  check_character_value state id literal builtin;
  Types.make_builtin builtin

and check_literal_pattern state id (span : Source.Definition_span.t) literal type_ =
  match literal with
  | Literal_integer number ->
      state.tables.literals.(id) <- Some (Integer_value number);
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
        State.report_mismatch state span ~expected:type_ ~actual:Types.bool
  | Literal_string tagged -> (
      match find_character_tag state tagged with
      | Some builtin ->
          check_character_value state id tagged builtin;
          if not (State.unify state type_ (Types.make_builtin builtin)) then
            State.report_mismatch state span ~expected:type_ ~actual:(Types.make_builtin builtin)
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
