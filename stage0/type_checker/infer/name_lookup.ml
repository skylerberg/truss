type overload =
  | Type_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

let classify_receiver (receiver : Syntax.expression) : Path.receiver =
  match receiver.kind with Mode (Mut, _) -> Mut | Mode (Own, _) -> Own | _ -> Read

let rec coerce state env ?argument (value : Syntax.expression) ~actual ~expected =
  State.convert state env ?argument ~expression:value.id (State.read_span state value.id) ~actual
    ~expected

and infer_literal_type state ~expected kind =
  match Option.map (State.resolve state) expected with
  | Some expected when Unify.literal_fits state.unifier kind expected -> expected
  | _ -> Unify.make_fresh_literal state.unifier kind

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
      | Some (_, type_) ->
          State.register_expression state value (fun () ->
              Use
                (Local
                   {
                     local = Synthetic index;
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
                Some (Global { path; type_arguments = instance.type_arguments });
              check_function_value state value instance.signature)
      | None -> State.raise_bug "`%s` has no signature" (Path.show path))
  | Definition (Constant, path) -> (
      state.tables.resolutions.(value.id) <- Some (Global { path; type_arguments = [] });
      State.register_expression state value (fun () ->
          Use (Form.build_constant_place state ~origin:value.id path));
      match Interface.Definition.read_constant_type state.lookups.interface path with
      | Some type_ -> type_
      | None -> State.raise_bug "the constant `%s` has no type" (Path.show path))
  | Definition (Type, path) ->
      if Intrinsic.builtin_of_path path = Some Unit then begin
        state.tables.resolutions.(value.id) <-
          Some (Variant_value { type_ = Types.unit; variant = "Unit" });
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
              inputs = [ (Types.Own, field.field_type) ];
              output = type_;
              uses = Types.no_capabilities;
              costs = [ { amortized = false; resource = Time; bound = Order_of } ];
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
  let unknown candidates =
    State.make_error_type state Unknown_member (State.read_span state member.id)
      ~fixes:
        (match Diagnostic.find_closest member.text candidates with
        | Some candidate ->
            [
              State.fix
                (Printf.sprintf "Write `%s`." candidate)
                [ State.replace (State.read_span state member.id) candidate ];
            ]
        | None -> [])
      (Printf.sprintf "`%s` has no field `%s`." (State.show state base_type) member.text)
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
              if Members.list_own_methods state.lookups path member.text <> [] then begin
                State.make_error_type state Not_a_value (State.read_span state member.id)
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text)
              end
              else unknown (List.map (fun (written : Types.field) -> written.field_name) fields))
      | None ->
          if Members.list_own_methods state.lookups path member.text <> [] then
            State.make_error_type state Not_a_value (State.read_span state member.id)
              (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text member.text)
          else unknown [])
  | _ -> unknown []

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
  | Types.Named { path; arguments } ->
      if State.is_variant_name member then
        check_variant_value state value path member.text ~arguments
      else
        begin match Members.find_own_constant state.lookups path member.text with
        | Some constant -> (
            state.tables.resolutions.(value.id) <-
              Some (Global { path = constant; type_arguments = [] });
            State.register_expression state value (fun () ->
                Use (Form.build_constant_place state ~origin:value.id constant));
            match Interface.Definition.read_constant_type state.lookups.interface constant with
            | Some type_ -> type_
            | None -> State.raise_bug "the constant `%s` has no type" (Path.show constant))
        | None -> (
            match Members.list_own_methods state.lookups path member.text with
            | (_, method_path) :: _ -> (
                match Instantiation.find_function_signature state method_path with
                | Some signature ->
                    let instance =
                      Instantiation.instantiate state (State.read_span state value.id) signature
                    in
                    (match instance.signature.receiver with
                    | Some (_, receiver) -> ignore (State.unify state receiver type_)
                    | None -> ());
                    state.tables.resolutions.(value.id) <-
                      Some (Global { path = method_path; type_arguments = instance.type_arguments });
                    check_function_value state value instance.signature
                | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path)
                )
            | [] ->
                State.make_error_type state Unknown_member (State.read_span state member.id)
                  (Printf.sprintf "`%s` has no member `%s`." (State.show state type_) member.text))
        end
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
        let own = List.drop head instance.type_arguments in
        if List.length written <> List.length own then
          Error
            (State.make_error_type state Arity (State.read_span state value.id)
               (Printf.sprintf "This takes %d type %s, and %d %s given." (List.length own)
                  (if List.length own = 1 then "argument" else "arguments")
                  (List.length written)
                  (if List.length written = 1 then "is" else "are")))
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
                       ]
                   | _ -> [])
                 written own)
          in
          match errors with [] -> Ok () | error :: _ -> Error error)

and finish_call (state : State.state) env (value : Syntax.expression) path callee
    (instance : Instantiation.instance) arguments left_out =
  let result = Types.extract_result_type instance.signature.output in
  state.tables.calls.(value.id) <-
    Some
      {
        callee;
        arguments;
        omitted_defaults = left_out;
        uses = instance.signature.uses;
        callee_result = result;
      };
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
               (Interface.Definition.read_interface state.lookups.interface path, specification_type)
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
  List.concat_map
    (fun package ->
      List.filter_map
        (fun trait ->
          match Members.find_trait_method state.lookups trait name receiver with
          | Some method_ ->
              let reference = Instantiation.make_fresh_trait_reference state trait in
              if
                Option.is_some
                  (State.implements state
                     (Types.Named
                        { path; arguments = Instantiation.make_fresh_arguments state path })
                     reference)
              then Some (reference, method_)
              else None
          | None -> None)
        (state.lookups.interface.names.list_traits_declaring package name))
    (Resolve.Names.list_visible_packages state.lookups.interface.names state.package)

and resolve_evidence state (value : Syntax.expression) self_type (reference : Types.trait_reference)
    =
  State.defer state (fun () ->
      let self_type = State.zonk state self_type
      and reference = Unify.zonk_trait state.unifier reference in
      if
        Types.contains_unsolved self_type
        || List.exists
             (function
               | Types.Type type_ -> Types.contains_unsolved type_
               | Types.Value (Value_variable _) -> true
               | Types.Value (Known _ | Value_parameter _) | Types.Capabilities _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match State.implements state self_type reference with
        | Some evidence -> (
            match state.tables.calls.(value.id) with
            | Some ({ callee = Trait_method method_; _ } as call) ->
                state.tables.calls.(value.id) <-
                  Some
                    {
                      call with
                      callee =
                        Trait_method
                          {
                            method_ with
                            trait = reference;
                            evidence = State.convert_evidence evidence;
                          };
                    }
            | _ -> ())
        | None ->
            if not (Types.is_error self_type) then
              State.report state No_impl (State.read_span state value.id)
                (Printf.sprintf "`%s` does not implement `%s`." (Types.show self_type)
                   (Types.show_trait reference)));
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
  let unique candidates =
    List.fold_left
      (fun acc ((trait : Types.trait_reference), methods) ->
        if
          List.exists
            (fun ((other : Types.trait_reference), _) -> Path.equal other.trait trait.trait)
            acc
        then acc
        else acc @ [ (trait, methods) ])
      [] candidates
  in
  match receiver_type with
  | Types.Parameter parameter ->
      unique
        (List.filter_map with_method
           (Interface.Properties.list_known_bounds state.lookups.interface
              ~bounds:(State.lookup_bounds state) (Types.Parameter parameter)))
  | Types.Any trait ->
      unique
        (List.filter_map with_method
           (Interface.Properties.list_bound_closure state.lookups.interface ~self:receiver_type
              trait))
  | _ ->
      unique
        (List.concat_map
           (fun package ->
             List.filter_map
               (fun trait ->
                 let reference = Instantiation.make_fresh_trait_reference state trait in
                 if Option.is_some (State.implements state receiver_type reference) then
                   with_method reference
                 else None)
               (state.lookups.interface.names.list_traits_declaring package name))
           (Resolve.Names.list_visible_packages state.lookups.interface.names state.package))

and is_one_family (state : State.state) (traits : Types.trait_reference list) =
  let requires (first : Types.trait_reference) (second : Types.trait_reference) =
    List.exists
      (fun (bound : Types.trait_reference) -> Path.equal bound.trait second.trait)
      (Interface.Properties.list_bound_closure state.lookups.interface
         ~self:(Types.Parameter (Types.make_self_parameter first.trait))
         first)
  in
  let related first second = requires first second || requires second first in
  let rec grow reached left =
    match List.partition (fun trait -> List.exists (related trait) reached) left with
    | [], [] -> true
    | [], _ -> false
    | more, left -> grow (more @ reached) left
  in
  match traits with [] -> true | first :: rest -> grow [ first ] rest

and resolve_overloads state receiver_type name :
    ((Path.receiver * overload) list, Types.trait_reference list) Result.t =
  let candidates = list_trait_candidates state receiver_type name in
  if not (is_one_family state (List.map fst candidates)) then Error (List.map fst candidates)
  else
    let own =
      match receiver_type with
      | Types.Named { path; _ } ->
          List.filter_map
            (fun (receiver, method_path) ->
              if receiver = Path.Static then None else Some (receiver, Type_overload method_path))
            (Members.list_own_methods state.lookups path name)
      | _ -> []
    in
    let from_traits =
      List.concat_map
        (fun ((trait : Types.trait_reference), methods) ->
          List.map
            (fun (method_ : Types.trait_method) ->
              (method_.method_receiver, Trait_overload (trait, method_)))
            methods)
        candidates
    in
    Ok
      (List.filter_map
         (fun (receiver : Path.receiver) ->
           Option.map
             (fun overload -> (receiver, overload))
             (List.assoc_opt receiver (own @ from_traits)))
         [ Read; Mut; Own ])

and find_method_version state (span : Source.Definition_span.t) type_ name
    (receiver : Path.receiver) : (Tables.callee * Types.signature) option =
  let found = match resolve_overloads state type_ name with Ok found -> found | Error _ -> [] in
  match List.assoc_opt receiver found with
  | Some (Type_overload method_path) -> (
      match Instantiation.find_function_signature state method_path with
      | Some signature ->
          let instance = Instantiation.instantiate state span signature in
          (match instance.signature.receiver with
          | Some (_, self_type) -> ignore (State.unify state self_type type_)
          | None -> ());
          Some
            ( Function { path = method_path; type_arguments = instance.type_arguments },
              instance.signature )
      | None -> None)
  | Some (Trait_overload (trait, method_)) ->
      let instance =
        Instantiation.instantiate state span
          ~extra:[ (Types.make_self_parameter trait.trait, Types.Type type_) ]
          (Members.read_method_signature state.lookups trait.trait method_)
      in
      Some
        ( Trait_method
            {
              trait;
              name;
              receiver;
              self_type = type_;
              type_arguments = [];
              evidence =
                (match type_ with
                | Types.Any _ -> Dynamic
                | Types.Parameter _ -> Bound
                | _ -> (
                    match State.implements state type_ trait with
                    | Some evidence -> State.convert_evidence evidence
                    | None -> Built_in));
            },
          instance.signature )
  | None -> None

and make_argumentless_call callee (signature : Types.signature) result : Tables.call =
  { callee; arguments = []; omitted_defaults = []; uses = signature.uses; callee_result = result }

and find_elements_calls state (span : Source.Definition_span.t) type_ (mode : Types.mode) =
  let receiver : Path.receiver = match mode with Read -> Read | Mut -> Mut | Own -> Own in
  let is_uint64 type_ = Types.is_builtin UInt64 (State.normalize state type_) in
  match
    ( find_method_version state span type_ "count" Read,
      find_method_version state span type_ "element" receiver )
  with
  | Some (count, counted), Some (element, lent) -> (
      match (counted.parameters, counted.output, lent.parameters, lent.output) with
      | [], Returns count_type, [ position ], Lends (lends, part)
        when is_uint64 count_type && is_uint64 position.type_ ->
          let part = State.normalize state part in
          Some
            ( Tables.Elements
                {
                  count = make_argumentless_call count counted (Types.make_builtin UInt64);
                  element = make_argumentless_call element lent part;
                  lends;
                },
              part,
              lends )
      | _ -> None)
  | _ -> None

and find_consuming_cursor state (span : Source.Definition_span.t) type_ =
  match find_method_version state span type_ "cursor" Own with
  | Some (callee, ({ parameters = []; output = Returns cursor; _ } as signature)) -> (
      let cursor = State.normalize state cursor in
      let trait = State.make_trait_reference ~arguments:[] (Well_known.make_path Cursor) in
      match State.implements state cursor trait with
      | Some _ ->
          Some
            ( Tables.Pulled
                {
                  cursor;
                  cursor_call = Some (make_argumentless_call callee signature cursor);
                  remaining = find_remaining_call state span cursor;
                },
              State.resolve_associated_type state cursor trait "Element" ~at:span )
      | None -> None)
  | _ -> None

and find_remaining_call state (span : Source.Definition_span.t) cursor =
  match find_method_version state span cursor "remaining" Read with
  | Some (callee, ({ parameters = []; output = Returns bound; _ } as signature))
    when Types.is_builtin UInt64 (State.normalize state bound) ->
      Some (make_argumentless_call callee signature (Types.make_builtin UInt64))
  | _ -> None
