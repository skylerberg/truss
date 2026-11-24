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
  state.tables.scrutinee_types.(written.id) <- Some type_;
  let recurse = check_pattern_with state env ~binding:part_binding ~mode in
  let check_unknown type_ =
    check_unknown_pattern state env written type_ ~binding:part_binding ~mode
  in
  let binds local =
    state.tables.patterns.(written.id) <- Some (Binding_pattern { local; is_var; mode })
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
                State.report state
                  (Alternative_type_mismatch
                     {
                       at = Written bound.id;
                       name = bound.text;
                       first = State.zonk state local.type_;
                       here = State.zonk state type_;
                     })
          | None -> ())
      | _ -> ())
  | Qualified_constant written_constant ->
      check_qualified_constant state written.id (Core.Written written.id) written_constant type_
  | Literal literal ->
      check_literal_pattern state written.id (Core.Written written.id) literal type_
  | Pattern_range { start; stop; _ } -> (
      match
        Solver.require_within state type_
          (Types.integer_types @ [ Language.Builtin_type.Character; Integer ])
          ~reason:(fun excluded ->
            State.add_diagnostic state
              (Range_pattern_type
                 { at = Written written.id; excluded = State.make_shown state excluded }))
      with
      | Types.Error _ when not (Types.is_error type_) -> ()
      | _ ->
          List.iter
            (fun (bound : Syntax.range_end) ->
              match bound.kind with
              | End_literal literal ->
                  check_literal_pattern state bound.id (Written bound.id) literal type_
              | End_constant constant ->
                  check_qualified_constant state bound.id (Written bound.id) constant type_)
            [ start; stop ])
  | Variant { name = variant_name; fields } -> (
      match type_ with
      | Types.Named { path; arguments } -> (
          match Members.find_variants state.lookups path arguments with
          | Some variants -> (
              check_fields_visible state (Core.Written written.id) path type_;
              match
                List.find_opt
                  (fun (variant : Types.variant) -> variant.variant_name = variant_name.text)
                  variants
              with
              | Some variant ->
                  (match (variant.fields, fields) with
                  | Some (_ :: _), None ->
                      State.report state
                        (Variant_pattern_without_fields
                           { at = Written written.id; variant = variant.variant_name })
                  | _ -> ());
                  let declared = Option.value ~default:[] variant.fields in
                  let matched =
                    check_pattern_fields state env written declared
                      (Option.value ~default:[] fields) ~binding:part_binding ~mode
                      ~owner:(Catalog.Inference.Variant_name variant.variant_name)
                      ~is_tuple_type:false
                  in
                  state.tables.patterns.(written.id) <-
                    Some
                      (Variant_pattern
                         {
                           type_;
                           variant = variant.variant_name;
                           fields = order_fields declared matched;
                         })
              | None ->
                  check_unknown
                  @@ State.make_error_type state
                       (Unknown_variant
                          {
                            at = Written variant_name.id;
                            type_;
                            variant = variant_name.text;
                            candidates =
                              List.map
                                (fun (variant : Types.variant) -> variant.variant_name)
                                variants;
                          }))
          | None ->
              check_unknown
                (State.make_error_type state (No_variants { at = Written written.id; type_ })))
      | Types.Error _ | Types.Hole -> check_unknown type_
      | _ ->
          check_unknown
            (State.make_error_type state
               (No_variants { at = Written written.id; type_ = State.zonk state type_ })))
  | Record fields -> (
      match type_ with
      | Types.Named { path; arguments } -> (
          match Members.find_fields state.lookups path arguments with
          | Some record_fields -> (
              check_fields_visible state (Written written.id) path type_;
              let is_tuple_type = Members.is_tuple_type state.lookups path in
              match
                if accepts_tuple_pattern && is_tuple_type then
                  find_parenthesized_tuple record_fields fields
                else None
              with
              | Some patterns ->
                  State.report state
                    (Parenthesized_tuple_pattern
                       {
                         at = Written written.id;
                         patterns =
                           {
                             covering =
                               List.map
                                 (fun (inner : Syntax.pattern) -> Core.Written inner.id)
                                 patterns;
                           };
                         type_;
                       });
                  check_tuple_fields state env written type_ record_fields patterns
                    ~binding:part_binding ~mode
              | None ->
                  let matched =
                    check_pattern_fields state env written record_fields fields
                      ~binding:part_binding ~mode ~owner:(Type_named type_) ~is_tuple_type
                  in
                  state.tables.patterns.(written.id) <-
                    Some (Record_pattern { type_; fields = order_fields record_fields matched }))
          | None ->
              check_unknown
                (State.make_error_type state
                   (Not_a_record_pattern
                      { at = Written written.id; type_ = State.make_shown state type_ })))
      | Types.Error _ | Types.Hole -> check_unknown type_
      | _ ->
          check_unknown
            (State.make_error_type state
               (Not_a_record_pattern
                  { at = Written written.id; type_ = State.make_shown state type_ })))
  | Tuple patterns -> (
      let check_each type_ = List.iter (fun inner -> recurse inner type_) patterns in
      let at : Core.origin = Written written.id in
      let report_no_tuple_type () =
        State.make_error_type state
          (Not_a_tuple_type_pattern { at; type_ = State.make_shown state type_ })
      in
      match type_ with
      | Types.Error _ | Types.Hole -> check_each type_
      | Types.Named { path; arguments } when Members.is_tuple_type state.lookups path -> (
          match Members.find_fields state.lookups path arguments with
          | Some declared when List.length declared = List.length patterns ->
              check_fields_visible state at path type_;
              check_tuple_fields state env written type_ declared patterns ~binding:part_binding
                ~mode
          | Some declared ->
              check_each
                (State.make_error_type state
                   (Tuple_pattern_arity
                      {
                        at;
                        type_;
                        fields = List.map (fun (field : Types.field) -> field.field_name) declared;
                        given = List.length patterns;
                      }))
          | None -> State.raise_bug "the tuple type `%s` has no fields" (Types.show type_))
      | Types.Named { path; arguments } -> (
          match Members.find_fields state.lookups path arguments with
          | Some fields ->
              let field_names = List.map (fun (field : Types.field) -> field.field_name) fields in
              let form =
                Argument_matching.find_labeled_form ~parameter_names:field_names
                  (List.map
                     (fun (inner : Syntax.pattern) ->
                       {
                         Argument_matching.label = None;
                         punned = find_bare_name inner;
                         origin = Written inner.id;
                       })
                     patterns)
              in
              check_each
                (State.make_error_type state
                   (Tuple_pattern_for_record { at; type_; fields = field_names; form }))
          | None -> check_each (report_no_tuple_type ()))
      | _ -> check_each (report_no_tuple_type ()))
  | Alternatives alternatives ->
      List.iter (fun alternative -> recurse alternative type_) alternatives

and check_fields_visible (state : State.state) at path type_ =
  if not (Members.are_fields_visible state.lookups ~package:state.package path) then
    State.report state (Opaque_pattern { at; type_ })

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
      State.report state
        (Tuple_pattern_out_of_order
           {
             at = Written written.id;
             type_;
             name;
             bound_field;
             reorder =
               (if List.sort compare bare_names = List.sort compare field_names then
                  Some field_names
                else None);
           }))
    misplaced;
  List.iter2
    (fun (inner : Syntax.pattern) (field : Types.field) ->
      check_pattern_with state env inner
        (Solver.flatten state (Bound { at = Written inner.id; of_type = None }) field.field_type)
        ~binding ~mode)
    patterns declared;
  state.tables.patterns.(written.id) <-
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
    (written_fields : Syntax.pattern_field list) ~binding ~mode ~owner ~is_tuple_type =
  let entries =
    List.filter_map
      (fun (field : Syntax.pattern_field) ->
        match field.kind with
        | Named_field (name, inner) ->
            Some
              ( { Argument_matching.label = Some name; punned = None; origin = Written inner.id },
                inner )
        | Field inner ->
            Some
              ( {
                  Argument_matching.label = None;
                  punned = find_bare_name inner;
                  origin = Written inner.id;
                },
                inner )
        | Rest -> None)
      written_fields
  in
  let indexes =
    Argument_matching.list_indexes state
      (Pattern { owner; is_tuple_type })
      ~parameter_names:(List.map (fun (field : Types.field) -> field.field_name) fields)
      (List.map fst entries)
  in
  let has_rest =
    List.exists (fun (field : Syntax.pattern_field) -> field.kind = Rest) written_fields
  in
  (if (not has_rest) && List.for_all Result.is_ok indexes then
     let matched_names =
       List.filter_map
         (function Ok index -> Some (List.nth fields index).field_name | Error _ -> None)
         indexes
     in
     match
       List.filter
         (fun name -> not (List.mem name matched_names))
         (List.map (fun (field : Types.field) -> field.field_name) fields)
     with
     | [] -> ()
     | missing -> State.report state (Unmatched_fields { at = Written written.id; missing }));
  List.filter_map Fun.id
    (List.map2
       (fun (_, (inner : Syntax.pattern)) index ->
         match index with
         | Ok index ->
             let declared = List.nth fields index in
             check_pattern_with state env inner
               (Solver.flatten state
                  (Bound { at = Written inner.id; of_type = None })
                  declared.field_type)
               ~binding ~mode;
             Some (declared.field_name, inner)
         | Error error ->
             check_pattern_with state env inner error ~binding ~mode;
             None)
       entries indexes)

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

and check_constant_pattern (state : State.state) id at path type_ =
  state.tables.patterns.(id) <- Some (Constant_pattern path);
  match Interface.Definition.find_constant_type state.lookups.interface path with
  | Some constant_type ->
      if not (State.unify state constant_type type_) then
        Failures.report_mismatch state at ~expected:type_ ~actual:constant_type
      else if not (is_structural state (State.resolve state constant_type)) then
        State.report state
          (Not_structural
             {
               at;
               type_ = State.zonk state constant_type;
               constant =
                 (match path with
                 | Top { name; _ } | Member_constant { name; _ } | Method { name; _ } -> name
                 | _ -> "the_constant");
             })
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

and check_qualified_constant state id at constant type_ =
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
  | Visible path -> check_constant_pattern state id at path type_
  | Hidden hidden -> ignore (Members.make_hidden_error state at hidden)
  | Absent -> State.report state (Not_a_constant { at })

and report_out_of_range state at number excluded =
  let low, high = State.read_integer_range state excluded in
  State.add_diagnostic state
    (Literal_does_not_fit { at; number; excluded = State.make_shown state excluded; low; high })

and report_negated_unsigned state (value : Syntax.expression) excluded =
  State.add_diagnostic state
    (Negated_unsigned
       {
         at = Written value.id;
         excluded = State.make_shown state excluded;
         is_unsigned = State.is_within state excluded Types.unsigned_integer_types;
       })

and check_integer_literal state (env : State.env) ?expected (value : Syntax.expression) number =
  let at : Core.origin = Written value.id in
  match
    ( Option.map (State.resolve state) expected,
      Types.list_fitting_integer_types number
      @ if env.specification then [ Language.Builtin_type.Integer ] else [] )
  with
  | Some Types.Integer, _ -> Types.Integer
  | _, [] -> State.make_error_type state (Literal_fits_no_integer { at; number })
  | _, allowed ->
      State.make_literal_type state value allowed ~report_excluded:(fun excluded ->
          if Z.sign number < 0 && not (State.is_within state excluded Types.signed_integer_types)
          then report_negated_unsigned state value excluded
          else report_out_of_range state at number excluded)

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
      State.report state (Character_literal { at = Written literal.id; tag = builtin });
      None

and check_character_literal state id literal builtin =
  Option.iter
    (fun value -> State.elaborate state id (Literal (Integer_value value)))
    (check_character_value state literal builtin);
  Types.make_builtin builtin

and check_literal_pattern state id at literal type_ =
  let record_integer integer = state.tables.patterns.(id) <- Some (Literal_pattern integer) in
  match literal with
  | Literal_integer number ->
      record_integer number;
      ignore
        (Solver.require_within state type_
           (Types.list_fitting_integer_types number @ [ Language.Builtin_type.Integer ])
           ~reason:(fun excluded ->
             if State.is_within state excluded Types.integer_types then
               report_out_of_range state at number excluded
             else
               State.add_diagnostic state
                 (Integer_pattern_type { at; excluded = State.make_shown state excluded })))
  | Literal_true | Literal_false ->
      if not (State.unify state type_ Types.bool) then
        Failures.report_mismatch state at ~expected:type_ ~actual:Types.bool
  | Literal_string tagged -> (
      match find_character_tag state tagged with
      | Some builtin ->
          Option.iter record_integer (check_character_value state tagged builtin);
          if not (State.unify state type_ (Types.make_builtin builtin)) then
            Failures.report_mismatch state at ~expected:type_ ~actual:(Types.make_builtin builtin)
      | None -> check_string_pattern state at type_)

and check_string_pattern state at type_ =
  if
    not
      (Types.is_well_known String type_
      || Types.is_well_known String_slice type_
      || Types.is_error type_)
  then State.report state (String_pattern_type { at; type_ })
