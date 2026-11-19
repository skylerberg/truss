type overload =
  | Type_overload of Path.t
  | View_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

let classify_receiver_mode (arguments : Syntax.argument list) : Language.Mode.t =
  match arguments with
  | { value = { kind = Mode (Mut, _); _ }; _ } :: _ -> Mut
  | { value = { kind = Mode (Own, _); _ }; _ } :: _ -> Own
  | _ -> Read

let describe_missing_method state type_ name =
  match Types.find_view (State.normalize state type_) with
  | Some view ->
      Printf.sprintf "`%s` has no method `%s`, and neither has its view `%s`."
        (State.show state type_) name (State.show state view)
  | None -> Printf.sprintf "`%s` has no method `%s`." (State.show state type_) name

let rec coerce state env ?argument ?takes_view_as_owner (value : Syntax.expression) ~actual
    ~expected =
  State.convert state env ?argument ?takes_view_as_owner ~expression:value.id
    (State.read_span state value.id) ~actual ~expected

and check_name (state : State.state) (env : State.env) (value : Syntax.expression)
    ({ name; target; type_arguments } : Resolve.head) =
  let text = name.text in
  match target with
  | Local id -> (
      state.locals_read <- id :: state.locals_read;
      state.tables.resolutions.(value.id) <- Some (Local_value id);
      State.register_expression state value (fun () ->
          Form.build_local_use state ~origin:value.id id);
      match Hashtbl.find_opt state.locals id with
      | Some local -> local.type_
      | None -> State.raise_bug "the local `%s` has no type" text)
  | Law_parameter index -> (
      match List.nth_opt state.law_parameters index with
      | Some (name, type_) ->
          State.register_expression state value (fun () ->
              Use
                (Local
                   {
                     local = Trait_parameter { index; name };
                     type_ = State.finalize_type state type_;
                     origin = value.id;
                   }));
          type_
      | None -> State.raise_bug "the law has no parameter `%s`" text)
  | Value_parameter parameter ->
      state.tables.resolutions.(value.id) <- Some (Value_parameter parameter);
      State.register_expression state value (fun () -> Value_parameter parameter);
      Types.make_builtin UInt64
  | Type_parameter _ | Capability_parameter _ ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf "`%s` is a type, not a value." text)
  | Definition (Theorem, _) ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf
           "`%s` is a theorem, so it is not a value. Call it in a proof to use its `ensures`." text)
  | Definition (Function, path) -> (
      match Instantiation.find_function_signature state path with
      | Some signature -> (
          let instance =
            Instantiation.instantiate state (State.read_span state value.id) signature
          in
          match
            match type_arguments with
            | Some items -> check_explicit_type_arguments state value instance items
            | None -> Ok ()
          with
          | Error error -> error
          | Ok () ->
              state.tables.resolutions.(value.id) <-
                Some (Global { path; instantiation = instance.instantiation });
              check_function_value state value instance.signature)
      | None -> State.raise_bug "`%s` has no signature" (Path.show path))
  | Definition (Constant, path) ->
      state.tables.resolutions.(value.id) <-
        Some (Global { path; instantiation = Types.no_instantiation });
      State.register_expression state value (fun () ->
          Use (Form.build_constant_place state ~origin:value.id path));
      Interface.Definition.read_constant_type state.lookups.interface path
  | Definition (Type, path) ->
      if Intrinsic.find_builtin path = Some Unit then begin
        state.tables.resolutions.(value.id) <-
          Some (Variant_value { type_ = Types.unit; variant = Intrinsic.show_builtin Unit });
        State.register_expression state value (fun () -> Construct { variant = None; fields = [] });
        Types.unit
      end
      else
        State.make_error_type state Not_a_value (State.read_span state value.id)
          (Printf.sprintf "`%s` is a type. Build a value with `%s(...)`." text text)
  | Definition ((Trait | Capability), _) ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf "`%s` is not a value." text)
  | Variant (type_path, variant) ->
      check_variant_value state value type_path variant
        ~arguments:(Instantiation.instantiate_type state (State.read_span state value.id) type_path)
  | Field field -> (
      match env.self with
      | Some (Types.Named { path = self_path; arguments }) -> (
          match Members.find_fields state.lookups self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : Types.field) -> written.field_name = field) fields
              with
              | Some written ->
                  State.register_expression state value (fun () ->
                      Use
                        (Field
                           {
                             base = Form.build_self_local state env ~origin:value.id;
                             field;
                             type_ = Form.read_type state value;
                             origin = value.id;
                           }));
                  written.field_type
              | None -> State.raise_bug "the field `%s` is not in its record" field)
          | None -> State.raise_bug "the field `%s` is not in a record" field)
      | _ -> State.raise_bug "the field `%s` is named outside its type" field)
  | Result_value -> (
      state.tables.resolutions.(value.id) <- Some Specification_value;
      State.register_expression state value (fun () -> Result);
      match env.output with
      | Some output -> Types.extract_result_type output
      | None -> State.raise_bug "`result` is named where nothing is returned")
  | Old | Identical | Final | Specification_function _ ->
      state.tables.resolutions.(value.id) <- Some Specification_value;
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf "`%s` is applied to its subject, as in `%s(...)`." text text)
  | Visited -> (
      state.tables.resolutions.(value.id) <- Some Specification_value;
      State.register_expression state value (fun () -> Yielded);
      match env.loop_element with
      | Some element ->
          Types.Named { path = Well_known.make_path Sequence; arguments = [ Types.Type element ] }
      | None -> State.raise_bug "`visited` is named outside a loop's clauses")
  | Unknown report -> Types.Error report
  | Binding | Module _ -> State.raise_bug "the name `%s` is not resolved" text

and check_variant_value state (value : Syntax.expression) type_path variant ~arguments =
  let type_ = Types.Named { path = type_path; arguments } in
  state.tables.resolutions.(value.id) <- Some (Variant_value { type_; variant });
  State.register_expression state value (fun () ->
      Form.build_variant_value state value type_path variant);
  match Members.find_variants state.lookups type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : Types.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some [ field ]; _ } ->
          Types.Function
            {
              inputs = [ (Language.Mode.Own, field.field_type) ];
              output = type_;
              uses = Types.no_capabilities;
              costs = [ { amortized = false; resource = Metric Time; bound = Order_of } ];
            }
      | Some { fields = Some fields; _ } ->
          State.make_error_type state Not_a_value (State.read_span state value.id)
            (Printf.sprintf
               "`%s` has %d fields, so it is not a function: a function takes its arguments by \
                position, and fields have no order. Build it with named fields, as in `%s(%s)`."
               variant (List.length fields) variant
               (String.concat ", "
                  (List.map (fun (field : Types.field) -> field.field_name ^ ": ...") fields)))
      | None ->
          State.make_error_type state Unknown_variant (State.read_span state value.id)
            (Printf.sprintf "`%s` has no variant `%s`." (Types.show type_) variant))
  | None ->
      State.make_error_type state Unknown_variant (State.read_span state value.id)
        (Printf.sprintf "`%s` has no variants." (Types.show type_))

and check_field state (value : Syntax.expression) base_type (member : Syntax.name) =
  let report_unknown candidates =
    State.make_error_type state Unknown_member (State.read_span state member.id)
      ~fixes:
        (Diagnostic.list_spelling_fixes (State.read_span state member.id) ~written:member.text
           candidates)
      (Printf.sprintf "%s has no field `%s`."
         (String.capitalize_ascii (State.describe state base_type))
         member.text)
  in
  match base_type with
  | Types.Named { path; arguments } -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields -> (
          match
            List.find_opt (fun (written : Types.field) -> written.field_name = member.text) fields
          with
          | Some written ->
              if not (Members.are_fields_visible state.lookups ~package:state.package path) then begin
                State.make_error_type state Private_field (State.read_span state member.id)
                  (Printf.sprintf
                     "`%s` is opaque, so its fields can be read only in its own package."
                     (State.show state base_type))
              end
              else begin
                state.tables.resolutions.(value.id) <-
                  Some (Field_access { type_ = base_type; field = member.text });
                written.field_type
              end
          | None ->
              if Members.has_visible_method state path member.text then begin
                State.make_error_type state Not_a_value (State.read_span state member.id)
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text)
              end
              else
                report_unknown (List.map (fun (written : Types.field) -> written.field_name) fields)
          )
      | None ->
          if Members.has_visible_method state path member.text then
            State.make_error_type state Not_a_value (State.read_span state member.id)
              (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text member.text)
          else report_unknown [])
  | _ -> report_unknown []

and check_function_value state (value : Syntax.expression) (signature : Types.signature) =
  match Types.make_function_type signature with
  | Some function_type ->
      State.register_expression state value (fun () -> Form.build_function_value state value);
      Types.Function function_type
  | None ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf
           "`%s` lends a part, and a function value cannot lend. Call it where the part is used, \
            or write a lambda that returns a copy of the part."
           (State.quote_span state (State.read_span state value.id)))

and check_static_member state (value : Syntax.expression) type_ (member : Syntax.name) =
  match type_ with
  | Types.Named { path; arguments } -> (
      if member.case = Upper then check_variant_value state value path member.text ~arguments
      else
        match
          Resolve.Names.choose_visible
            (Members.lookup_member state (Member_constant { owner = path; name = member.text })
            :: Members.list_method_lookups state path member.text)
        with
        | Visible (Member_constant _ as constant) ->
            state.tables.resolutions.(value.id) <-
              Some (Global { path = constant; instantiation = Types.no_instantiation });
            State.register_expression state value (fun () ->
                Use (Form.build_constant_place state ~origin:value.id constant));
            Interface.Definition.read_constant_type state.lookups.interface constant
        | Visible method_path -> (
            match Instantiation.find_function_signature state method_path with
            | Some signature ->
                let instance =
                  Instantiation.instantiate state (State.read_span state value.id) signature
                in
                (match instance.signature.receiver with
                | Some (_, receiver) -> ignore (State.unify state receiver type_)
                | None -> ());
                state.tables.resolutions.(value.id) <-
                  Some (Global { path = method_path; instantiation = instance.instantiation });
                check_function_value state value instance.signature
            | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path))
        | Hidden hidden -> Members.make_hidden_error state (State.read_span state member.id) hidden
        | Absent ->
            State.make_error_type state Unknown_member (State.read_span state member.id)
              (match Types.find_view type_ with
              | Some (Types.Named { path = Top { name; _ } as view; _ })
                when Members.has_visible_method state view member.text ->
                  Printf.sprintf
                    "`%s` has no member `%s` of its own. The method is its view's: `%s.%s`."
                    (State.show state type_) member.text name member.text
              | _ -> Printf.sprintf "`%s` has no member `%s`." (State.show state type_) member.text)
      )
  | Types.Error _ | Types.Hole -> type_
  | _ ->
      State.make_error_type state Unknown_member (State.read_span state member.id)
        (Printf.sprintf "`%s` has no member `%s`." (State.show state type_) member.text)

and check_explicit_type_arguments ?(head = 0) state (value : Syntax.expression) instance items :
    (unit, Types.ty) result =
  if items = [] then Ok ()
  else
    match Instantiation.check_written_arguments state items with
    | Error error -> Error error
    | Ok written -> (
        let own = List.drop head instance.instantiation.type_arguments in
        if List.length written <> List.length own then
          Error
            (State.make_error_type state Arity (State.read_span state value.id)
               (Printf.sprintf "This takes %s, and %s given."
                  (Diagnostic.show_count (List.length own) "type argument" "type arguments")
                  (Diagnostic.show_count (List.length written) "is" "are")))
        else
          let errors =
            List.concat
              (List.map2
                 (fun written own ->
                   match (written, own) with
                   | Types.Type written, Types.Type own ->
                       ignore (State.unify state written own);
                       []
                   | Types.Value written, Types.Value own ->
                       ignore (Unify.unify_value state.unifier written own);
                       []
                   | Types.Type _, Types.Value _ ->
                       [
                         State.make_error_type state Argument_kind (State.read_span state value.id)
                           "A type argument is given where a `UInt64` value is expected.";
                       ]
                   | Types.Value _, Types.Type _ ->
                       [
                         State.make_error_type state Argument_kind (State.read_span state value.id)
                           "A `UInt64` value is given where a type argument is expected.";
                       ])
                 written own)
          in
          match errors with [] -> Ok () | error :: _ -> Error error)

and finish_call (state : State.state) env (value : Syntax.expression) path callee
    (instance : Instantiation.instance) arguments left_out =
  let result = Types.extract_result_type instance.signature.output in
  state.tables.calls.(value.id) <-
    Some { callee; arguments; omitted_defaults = left_out; callee_result = result };
  Modes.note_lending state value instance.signature.output;
  Form.register_call state value;
  Option.value (reject_specification_call state env value path instance.signature) ~default:result

and reject_specification_call state (env : State.env) (value : Syntax.expression) (path : Path.t)
    (signature : Types.signature) =
  if (not signature.specification_only) || env.specification then None
  else
    let name =
      match path with Top { name; _ } | Method { name; _ } -> name | path -> Path.show path
    in
    let specification_type =
      List.find_map Types.find_specification_only_type
        (Types.extract_result_type signature.output
        :: List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
        )
    in
    Some
      (Types.Error
         (State.report_specification_only state (State.read_span state value.id)
            (match
               (Interface.Definition.find_interface state.lookups.interface path, specification_type)
             with
            | Some (Theorem_interface _), _ ->
                Printf.sprintf
                  "`%s` is a theorem, so it is called only in specifications and proofs, which are \
                   not compiled."
                  name
            | _, Some specification_type ->
                Printf.sprintf
                  "`%s` mentions `%s`, which exists only in specifications, so it is called only \
                   in specifications."
                  name (Types.show specification_type)
            | _, None ->
                Printf.sprintf
                  "`%s` is for specifications only, so it is called only in specifications." name)))

and list_trait_static_methods (state : State.state) path name receiver =
  List.filter_map
    (fun trait ->
      match
        Interface.Definition.find_trait_method state.lookups.interface trait ~name ~receiver
      with
      | Some method_ ->
          let reference = Instantiation.make_fresh_trait_reference state trait in
          if
            Option.is_some
              (State.find_evidence state
                 (Types.Named { path; arguments = Instantiation.make_fresh_arguments state path })
                 reference)
          then Some (reference, method_)
          else None
      | None -> None)
    (Resolve.Names.list_visible_traits_declaring state.lookups.interface.names
       ~from:state.key.module_ name)

and check_implements ?(code : Diagnostic.Code.types = No_impl) state
    (span : Source.Definition_span.t) self_type (reference : Types.trait_reference) =
  State.defer state (fun () ->
      let self_type = State.zonk state self_type in
      let reference = State.solve_trait_arguments state self_type reference in
      if
        Types.contains_unsolved self_type
        || List.exists Types.is_unsolved_argument reference.trait_arguments
      then false
      else begin
        if
          Option.is_none (State.find_evidence state self_type reference)
          && not (Types.is_error self_type)
        then
          State.report state code span
            (Printf.sprintf "`%s` does not implement `%s`." (Types.show self_type)
               (Types.show_trait reference));
        true
      end)

and list_trait_candidates (state : State.state) receiver_type name =
  let with_method (trait : Types.trait_reference) =
    match
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_receiver <> Path.Static)
        (Members.list_trait_methods state.lookups trait.trait name)
    with
    | [] -> None
    | methods -> Some (trait, methods)
  in
  match receiver_type with
  | Types.Parameter parameter ->
      List.filter_map with_method
        (merge_bounds_by_trait state
           (Interface.Properties.list_known_bounds state.lookups.interface
              ~list_bounds:(State.lookup_bounds state) (Types.Parameter parameter)))
  | Types.Any trait ->
      List.filter_map with_method
        (merge_bounds_by_trait state
           (Interface.Properties.list_bound_closure state.lookups.interface ~self:receiver_type
              trait))
  | _ ->
      List.filter_map
        (fun trait ->
          let reference = Instantiation.make_fresh_trait_reference state trait in
          if Option.is_some (State.find_evidence state receiver_type reference) then
            with_method reference
          else None)
        (Resolve.Names.list_visible_traits_declaring state.lookups.interface.names
           ~from:state.key.module_ name)

and merge_bounds_by_trait state = function
  | [] -> []
  | (bound : Types.trait_reference) :: rest ->
      let same_trait, other_traits =
        List.partition
          (fun (other : Types.trait_reference) -> Path.equal other.trait bound.trait)
          rest
      in
      (if
         List.for_all
           (fun (other : Types.trait_reference) -> other.trait_arguments = bound.trait_arguments)
           same_trait
       then bound
       else Instantiation.make_fresh_trait_reference state bound.trait)
      :: merge_bounds_by_trait state other_traits

and is_one_family (state : State.state) (traits : Types.trait_reference list) =
  let requires (first : Types.trait_reference) (second : Types.trait_reference) =
    List.exists
      (fun (bound : Types.trait_reference) -> Path.equal bound.trait second.trait)
      (Interface.Properties.list_bound_closure state.lookups.interface
         ~self:(Types.Parameter (Types.make_self_parameter first.trait))
         first)
  in
  let are_related first second = requires first second || requires second first in
  let rec grow reached left =
    match List.partition (fun trait -> List.exists (are_related trait) reached) left with
    | [], [] -> true
    | [], _ -> false
    | more, left -> grow (more @ reached) left
  in
  match traits with [] -> true | first :: rest -> grow [ first ] rest

and resolve_overloads state receiver_type name :
    ((Path.receiver * overload) list Resolve.Names.lookup, Types.trait_reference list) Result.t =
  let candidates = list_trait_candidates state receiver_type name in
  if not (is_one_family state (List.map fst candidates)) then Error (List.map fst candidates)
  else
    let lookup_method make owner receiver : overload Resolve.Names.lookup =
      match owner with
      | Some (Types.Named { path; _ }) -> (
          match Members.lookup_method state path name receiver with
          | Visible method_path -> Visible (make method_path)
          | Hidden hidden -> Hidden hidden
          | Absent -> Absent)
      | _ -> Absent
    in
    let lookup_trait_method receiver : overload Resolve.Names.lookup =
      match
        List.find_map
          (fun ((trait : Types.trait_reference), methods) ->
            Option.map
              (fun method_ -> Trait_overload (trait, method_))
              (List.find_opt
                 (fun (method_ : Types.trait_method) -> method_.method_receiver = receiver)
                 methods))
          candidates
      with
      | Some overload -> Visible overload
      | None -> Absent
    in
    Ok
      (Resolve.Names.collect_visible
         (List.map
            (fun receiver ->
              ( receiver,
                Resolve.Names.choose_visible
                  [
                    lookup_method
                      (fun method_path -> Type_overload method_path)
                      (Some receiver_type) receiver;
                    lookup_trait_method receiver;
                    lookup_method
                      (fun method_path -> View_overload method_path)
                      (Types.find_view receiver_type) receiver;
                  ] ))
            [ Path.Instance Read; Instance Mut; Instance Own ]))

and find_method_version state (span : Source.Definition_span.t) type_ name
    (receiver : Path.receiver) : (Tables.callee * Types.signature) Resolve.Names.lookup =
  match resolve_overloads state type_ name with
  | Error _ | Ok Absent -> Absent
  | Ok (Hidden hidden) -> Hidden hidden
  | Ok (Visible overloads) -> (
      match List.assoc_opt receiver overloads with
      | Some (Type_overload method_path) -> (
          match Instantiation.find_function_signature state method_path with
          | Some signature ->
              let instance = Instantiation.instantiate state span signature in
              (match instance.signature.receiver with
              | Some (_, self_type) -> ignore (State.unify state self_type type_)
              | None -> ());
              Visible
                ( Function { path = method_path; instantiation = instance.instantiation },
                  instance.signature )
          | None -> Absent)
      | Some (Trait_overload (trait, method_)) ->
          let instance, callee =
            instantiate_trait_method state span ~self_type:type_ trait method_
          in
          check_implements ~code:Not_indexable state span type_ trait;
          Visible (callee, (instance : Instantiation.instance).signature)
      | Some (View_overload _) | None -> Absent)

and instantiate_trait_method state span ~self_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) =
  let instance =
    Instantiation.instantiate state span
      ~extra:
        (Types.make_trait_substitution
           (Members.list_trait_generics state.lookups trait.trait)
           ~self:self_type trait)
      (Members.read_method_signature state.lookups trait.trait method_)
  in
  ( instance,
    Tables.Trait_method
      {
        trait;
        name = method_.method_name;
        receiver = method_.method_receiver;
        self_type;
        instantiation = instance.instantiation;
      } )

and make_argumentless_call callee result : Tables.call =
  { callee; arguments = []; omitted_defaults = []; callee_result = result }

and find_elements_calls state (span : Source.Definition_span.t) type_ (mode : Language.Mode.t) :
    (Tables.loop * Types.ty * Language.Mode.t) Resolve.Names.lookup =
  let receiver = Path.Instance mode in
  let is_uint64 type_ = Types.is_builtin UInt64 (State.normalize state type_) in
  match
    ( find_method_version state span type_ "count" (Instance Read),
      find_method_version state span type_ "element" receiver )
  with
  | Visible (count, counted), Visible (element, lent) -> (
      match (counted.parameters, counted.output, lent.parameters, lent.output) with
      | [], Returns count_type, [ position ], Lends (lends, part)
        when is_uint64 count_type && is_uint64 position.type_ ->
          let part = State.normalize state part in
          Visible
            ( Tables.Elements
                {
                  count = make_argumentless_call count (Types.make_builtin UInt64);
                  element = make_argumentless_call element part;
                  lends;
                },
              part,
              lends )
      | _ -> Absent)
  | Hidden hidden, (Visible _ | Hidden _) | Visible _, Hidden hidden -> Hidden hidden
  | Absent, _ | _, Absent -> Absent

and find_consuming_cursor state (span : Source.Definition_span.t) type_ :
    (Tables.loop * Types.ty) Resolve.Names.lookup =
  match find_method_version state span type_ "cursor" (Instance Own) with
  | Visible (callee, { parameters = []; output = Returns cursor; _ }) -> (
      let cursor = State.normalize state cursor in
      let trait = State.make_trait_reference ~arguments:[] (Well_known.make_path Cursor) in
      match State.find_evidence state cursor trait with
      | Some _ ->
          Visible
            ( Tables.Pulled
                {
                  cursor;
                  cursor_call = Some (make_argumentless_call callee cursor);
                  remaining = find_remaining_call state span cursor;
                },
              State.resolve_associated_type state cursor trait Cursor_element ~at:span )
      | None -> Absent)
  | Hidden hidden -> Hidden hidden
  | Visible _ | Absent -> Absent

and find_remaining_call state (span : Source.Definition_span.t) cursor =
  match find_method_version state span cursor "remaining" (Instance Read) with
  | Visible (callee, { parameters = []; output = Returns bound; _ })
    when Types.is_builtin UInt64 (State.normalize state bound) ->
      Some (make_argumentless_call callee (Types.make_builtin UInt64))
  | Visible _ | Hidden _ | Absent -> None
