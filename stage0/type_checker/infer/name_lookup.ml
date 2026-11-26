type overload =
  | Type_overload of Path.t
  | List_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

let classify_receiver_mode (arguments : Syntax.argument list) : Language.Mode.t =
  match arguments with
  | { value = { kind = Mode (Mut, _); _ }; _ } :: _ -> Mut
  | { value = { kind = Mode (Own, _); _ }; _ } :: _ -> Own
  | _ -> Read

let make_method_owner state type_ : Catalog.Inference.method_owner =
  Type_owner
    {
      type_ = State.normalize_known state type_;
      list =
        Option.map (State.normalize_known state)
          (Types.find_list_of_array (State.normalize state type_));
    }

let rec check_name (state : State.state) (env : State.env) (value : Syntax.expression)
    ({ name; target; type_arguments } : Resolve.head) =
  let text = name.text in
  match target with
  | Local id -> (
      state.locals_read <- id :: state.locals_read;
      state.tables.resolutions.(value.id) <- Some (Local_value id);
      match Hashtbl.find_opt state.locals id with
      | Some local -> local.type_
      | None -> State.raise_bug "the local `%s` has no type" text)
  | Law_parameter index -> (
      match List.nth_opt state.law_parameters index with
      | Some (_, type_) -> type_
      | None -> State.raise_bug "the law has no parameter `%s`" text)
  | Value_parameter parameter ->
      state.tables.resolutions.(value.id) <- Some (Value_parameter parameter);
      Types.make_builtin UInt64
  | Type_parameter _ | Capability_parameter _ ->
      State.make_error_type state (Type_parameter_as_value { at = Written value.id; name = text })
  | Definition (Theorem, _) ->
      State.make_error_type state (Theorem_as_value { at = Written value.id; name = text })
  | Definition (Function, path) -> (
      match Instantiation.find_function_signature state.signatures state.lookups path with
      | Some signature -> (
          let instance =
            Instantiation.instantiate state ~written:value.id ~declared_on:path signature
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
              check_function_value state value instance)
      | None -> State.raise_bug "`%s` has no signature" (Path.show path))
  | Definition (Constant, path) ->
      state.tables.resolutions.(value.id) <-
        Some (Global { path; instantiation = Types.no_instantiation });
      Interface.Definition.read_constant_type state.lookups.interface path
  | Definition (Type, path) ->
      if Well_known.find_builtin_type path = Some Unit then begin
        state.tables.resolutions.(value.id) <-
          Some (Variant_value { type_ = Types.unit; variant = Language.Builtin_type.show Unit });
        Types.unit
      end
      else State.make_error_type state (Type_as_value { at = Written value.id; name = text })
  | Definition ((Trait | Capability), _) ->
      State.make_error_type state (Trait_as_value { at = Written value.id; name = text })
  | Variant (type_path, variant) ->
      check_variant_value state value type_path variant
        ~arguments:(Instantiation.instantiate_type state ~written:value.id type_path)
  | Field field -> (
      match env.self with
      | Some (Types.Named { path = self_path; arguments }) -> (
          match Members.find_fields state.lookups self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : Types.field) -> written.field_name = field) fields
              with
              | Some written -> written.field_type
              | None -> State.raise_bug "the field `%s` is not in its record" field)
          | None -> State.raise_bug "the field `%s` is not in a record" field)
      | _ -> State.raise_bug "the field `%s` is named outside its type" field)
  | Result_value -> (
      state.tables.resolutions.(value.id) <- Some Specification_value;
      match env.output with
      | Some output -> Types.extract_result_type output
      | None -> State.raise_bug "`result` is named where nothing is returned")
  | Old | Identical | Final | Specification_function _ ->
      state.tables.resolutions.(value.id) <- Some Specification_value;
      State.make_error_type state
        (Specification_function_as_value { at = Written value.id; name = text })
  | Visited -> (
      state.tables.resolutions.(value.id) <- Some Specification_value;
      match env.loop_element with
      | Some element ->
          Types.Named { path = Well_known.make_path Sequence; arguments = [ Types.Type element ] }
      | None -> State.raise_bug "`visited` is named outside a loop's clauses")
  | Unknown report -> Types.Error report
  | Binding | Module _ -> State.raise_bug "the name `%s` is not resolved" text

and check_variant_value state (value : Syntax.expression) type_path variant ~arguments =
  let type_ = Types.Named { path = type_path; arguments } in
  state.tables.resolutions.(value.id) <- Some (Variant_value { type_; variant });
  match Members.find_variants state.lookups type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : Types.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some [ field ]; _ } ->
          Solver.flatten state
            (Bound { at = Written value.id; of_type = None })
            (Types.Function
               {
                 inputs = [ (Language.Mode.Own, field.field_type) ];
                 output = type_;
                 uses = Types.no_capabilities;
                 costs = [ { amortized = false; resource = Metric Time; bound = Order_of } ];
               })
      | Some { fields = Some fields; _ } ->
          State.make_error_type state
            (Variant_with_fields_as_function
               {
                 at = Written value.id;
                 variant;
                 fields = List.map (fun (field : Types.field) -> field.field_name) fields;
               })
      | None ->
          State.make_error_type state
            (Unknown_variant { at = Written value.id; type_; variant; candidates = [] }))
  | None -> State.make_error_type state (No_variants { at = Written value.id; type_ })

and check_field state (value : Syntax.expression) base_type (member : Syntax.name) =
  let report_unknown candidates =
    State.make_error_type state
      (Unknown_field
         {
           at = Written member.id;
           base = State.make_shown state base_type;
           name = member.text;
           candidates;
         })
  in
  let base_type = Types.strip_view base_type in
  match base_type with
  | Types.Named { path; arguments } -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields -> (
          match
            List.find_opt (fun (written : Types.field) -> written.field_name = member.text) fields
          with
          | Some written ->
              if not (Members.are_fields_visible state.lookups ~package:state.package path) then begin
                State.make_error_type state
                  (Opaque_field_read
                     { at = Written member.id; type_ = State.normalize_known state base_type })
              end
              else begin
                state.tables.resolutions.(value.id) <-
                  Some (Field_access { type_ = base_type; field = member.text });
                Solver.flatten state
                  (Bound { at = Written member.id; of_type = None })
                  written.field_type
              end
          | None ->
              if Members.has_visible_method state path member.text then begin
                State.make_error_type state
                  (Method_as_field { at = Written member.id; name = member.text })
              end
              else
                report_unknown (List.map (fun (written : Types.field) -> written.field_name) fields)
          )
      | None ->
          if Members.has_visible_method state path member.text then
            State.make_error_type state
              (Method_as_field { at = Written member.id; name = member.text })
          else report_unknown [])
  | _ -> report_unknown []

and check_function_value state (value : Syntax.expression) (instance : Instantiation.instance) =
  match Types.make_function_type instance.signature with
  | Some function_type -> instance.flatten (Types.Function function_type)
  | None -> State.make_error_type state (Lending_function_value { at = Written value.id })

and check_static_member state ?expected (value : Syntax.expression) type_ (member : Syntax.name) =
  let report_no_member list =
    State.make_error_type state
      (No_member
         {
           at = Written member.id;
           type_ = State.normalize_known state type_;
           name = member.text;
           list;
         })
  in
  match type_ with
  | Types.Named { path; arguments } when member.case = Upper ->
      check_variant_value state value path member.text ~arguments
  | Types.Named _ | Types.Parameter _ | Types.Projection _ -> (
      let constant =
        match type_ with
        | Types.Named { path; _ } ->
            Resolve.Names.choose_member
              (Members.list_member_lookups state path member.text)
              (Member_constant { owner = path; name = member.text })
        | _ -> Absent
      in
      match (constant, resolve_member_overloads state type_ member.text) with
      | Visible constant, _ ->
          state.tables.resolutions.(value.id) <-
            Some (Global { path = constant; instantiation = Types.no_instantiation });
          Interface.Definition.read_constant_type state.lookups.interface constant
      | _, Error traits ->
          State.make_error_type state
            (Ambiguous_static_method
               {
                 at = Written member.id;
                 type_ = State.normalize_known state type_;
                 name = member.text;
                 traits;
               })
      | _, Ok (Resolve.Names.Visible overloads) -> (
          match choose_value_overload state ?expected overloads with
          | Type_overload method_path -> (
              match
                Instantiation.find_function_signature state.signatures state.lookups method_path
              with
              | Some signature ->
                  let instance =
                    Instantiation.instantiate state ~written:value.id ~declared_on:method_path
                      signature
                  in
                  (match instance.signature.receiver with
                  | Some (_, receiver) -> ignore (State.unify state receiver type_)
                  | None -> ());
                  state.tables.resolutions.(value.id) <-
                    Some (Global { path = method_path; instantiation = instance.instantiation });
                  check_function_value state value instance
              | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path))
          | Trait_overload (trait, method_) ->
              check_trait_method_value state value ~self_type:type_ trait method_
          | List_overload (Top { name; _ }) -> report_no_member (Some name)
          | List_overload _ -> report_no_member None)
      | Hidden hidden, _ | _, Ok (Hidden hidden) ->
          Members.make_hidden_error state (Written member.id) hidden
      | Absent, Ok Absent -> report_no_member None)
  | Types.Error _ | Types.Hole -> type_
  | _ -> report_no_member None

and check_trait_value_in_full state ?expected (value : Syntax.expression) trait ~trait_arguments
    (member : Syntax.name) =
  let fresh = Instantiation.make_fresh_trait_reference state trait in
  let reference =
    match trait_arguments with
    | Some trait_arguments -> { fresh with trait_arguments }
    | None -> fresh
  in
  match
    List.filter_map
      (function
        | Path.Method { receiver; _ } ->
            Option.map
              (fun method_ -> (receiver, Trait_overload (reference, method_)))
              (Interface.Definition.find_trait_method state.lookups.interface trait
                 ~name:member.text ~receiver)
        | _ -> None)
      (Members.list_methods trait member.text)
  with
  | [] ->
      State.make_error_type state
        (No_method
           { at = Written member.id; owner = Path_owner trait; name = member.text; candidates = [] })
  | overloads -> (
      match choose_value_overload state ?expected overloads with
      | Trait_overload (trait, method_) ->
          check_trait_method_value state value
            ~self_type:(Unify.make_fresh_type state.unifier)
            trait method_
      | Type_overload _ | List_overload _ -> State.raise_bug "a trait has a method of a type")

and choose_value_overload state ?expected overloads =
  let wanted =
    match Option.map (State.zonk state) expected with
    | Some (Types.Function { inputs = (mode, _) :: _; _ }) ->
        List.assoc_opt (Path.Instance mode) overloads
    | _ -> None
  in
  match (wanted, overloads) with
  | Some overload, _ | None, (_, overload) :: _ -> overload
  | None, [] -> State.raise_bug "a method has no overload"

and check_trait_method_value state (value : Syntax.expression) ~self_type trait method_ =
  let instance, trait_method =
    instantiate_trait_method state ~written:value.id ~self_type trait method_
  in
  Solver.require state (Method_call (Written value.id)) self_type trait;
  state.tables.resolutions.(value.id) <- Some (Trait_method_value trait_method);
  check_function_value state value instance

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
            (State.make_error_type state
               (Type_argument_count
                  { at = Written value.id; expected = List.length own; given = List.length written }))
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
                   | Types.Type (Types.Error _ as reported), Types.Value _ -> [ reported ]
                   | Types.Type _, Types.Value _ ->
                       [
                         State.make_error_type state
                           (Type_for_value_argument { at = Written value.id });
                       ]
                   | Types.Value _, Types.Type _ ->
                       [
                         State.make_error_type state
                           (Value_for_type_argument { at = Written value.id });
                       ])
                 written own)
          in
          match errors with [] -> Ok () | error :: _ -> Error error)

and finish_call (state : State.state) env (value : Syntax.expression) path callee
    (instance : Instantiation.instance) arguments left_out =
  let result = Types.extract_result_type instance.signature.output in
  State.elaborate state value.id
    (Call
       {
         callee;
         arguments;
         omitted_defaults = left_out;
         callee_result = result;
         lends = Types.find_lent_mode instance.signature.output;
       });
  Option.value (reject_specification_call state env value path instance.signature) ~default:result

and reject_specification_call state (env : State.env) (value : Syntax.expression) (path : Path.t)
    (signature : Types.signature) =
  if (not signature.specification_only) || env.specification then None
  else
    let specification_type =
      List.find_map Types.find_specification_only_type
        (Types.extract_result_type signature.output
        :: List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
        )
    in
    Some
      (Types.Error
         (State.report_specification_only state
            (Specification_call_in_code
               {
                 at = Written value.id;
                 callee = path;
                 call =
                   (match
                      ( Interface.Definition.find_interface state.lookups.interface path,
                        specification_type )
                    with
                   | Some (Theorem_interface _), _ -> Theorem_call
                   | _, Some specification_type -> Mentions specification_type
                   | _, None -> Specification_function_call);
               })))

and lookup_trait_static_methods (state : State.state) path name =
  Resolve.Names.collect_visible
    (List.map
       (fun candidate ->
         choose_trait_method name Path.Static candidate
           (list_candidate_methods state name candidate))
       (list_implemented_trait_lookups state
          (Types.Named
             {
               path;
               arguments =
                 List.map
                   (Unify.make_fresh_argument state.unifier)
                   (Instantiation.read_type_generics state path);
             })
          name))

and list_implemented_trait_lookups ?checks_conditions (state : State.state) self_type name =
  List.filter_map
    (fun (lookup : Path.t Resolve.Names.lookup) ->
      match lookup with
      | Visible trait | Hidden (trait, _) ->
          let reference = Instantiation.make_fresh_trait_reference state trait in
          if Option.is_some (State.find_evidence ?checks_conditions state self_type reference) then
            Some (Resolve.Names.map_visible (fun _ -> reference) lookup)
          else None
      | Absent -> None)
    (Resolve.Names.list_declaring_trait_lookups state.lookups.interface.names
       ~visible_packages:(Lazy.force state.visible_packages)
       ~from:state.key.module_ name)

and list_candidate_methods (state : State.state) name
    (candidate : Types.trait_reference Resolve.Names.lookup) =
  match candidate with
  | Visible { trait; _ } | Hidden (trait, _) -> Members.list_trait_methods state.lookups trait name
  | Absent -> []

and choose_trait_method name receiver (candidate : Types.trait_reference Resolve.Names.lookup)
    (methods : Types.trait_method list) :
    (Types.trait_reference * Types.trait_method) Resolve.Names.lookup =
  match
    ( candidate,
      List.find_opt
        (fun (method_ : Types.trait_method) -> method_.method_receiver = receiver)
        methods )
  with
  | Visible trait, Some method_ -> Visible (trait, method_)
  | Hidden (trait, visibility), Some _ ->
      Hidden (Method { owner = trait; name; receiver }, visibility)
  | (Visible _ | Hidden _), None | Absent, _ -> Absent

and find_method_of_an_unmet_impl state receiver_type name receiver =
  match
    Resolve.Names.collect_visible
      (List.map
         (fun candidate ->
           choose_trait_method name receiver candidate (list_candidate_methods state name candidate))
         (list_implemented_trait_lookups ~checks_conditions:false state receiver_type name))
  with
  | Visible [ found ] -> Some found
  | Visible _ | Hidden _ | Absent -> None

and has_method_without_self state receiver_type name =
  match list_static_overloads state receiver_type name with
  | Ok (Resolve.Names.Visible _) | Error _ -> true
  | Ok (Hidden _ | Absent) -> false

and list_static_overloads state self_type name =
  let of_trait_methods = function
    | [] -> Ok Resolve.Names.Absent
    | [ (trait, method_) ] ->
        Ok (Resolve.Names.Visible [ (Path.Static, Trait_overload (trait, method_)) ])
    | several -> Error (List.map fst several)
  in
  match self_type with
  | Types.Named { path; _ } -> (
      match
        (Members.lookup_method state path name Static, lookup_trait_static_methods state path name)
      with
      | Visible method_path, _ -> Ok (Visible [ (Path.Static, Type_overload method_path) ])
      | _, Visible found -> of_trait_methods found
      | Hidden hidden, _ | _, Hidden hidden -> Ok (Hidden hidden)
      | Absent, Absent -> Ok Absent)
  | Types.Parameter _ | Types.Projection _ ->
      of_trait_methods
        (List.fold_left
           (fun methods (bound : Types.trait_reference) ->
             match
               Interface.Definition.find_trait_method state.lookups.interface bound.trait ~name
                 ~receiver:Static
             with
             | Some method_
               when not
                      (List.exists
                         (fun ((other : Types.trait_reference), _) ->
                           Path.equal other.trait bound.trait)
                         methods) ->
                 methods @ [ (bound, method_) ]
             | _ -> methods)
           []
           (Interface.Properties.list_known_bounds state.lookups.interface
              ~list_bounds:(State.lookup_bounds state) self_type))
  | _ -> Ok Absent

and resolve_member_overloads state self_type name =
  match (list_static_overloads state self_type name, resolve_overloads state self_type name) with
  | Error traits, _ -> Error traits
  | Ok (Resolve.Names.Visible static), Ok (Resolve.Names.Visible instance) ->
      Ok (Resolve.Names.Visible (static @ instance))
  | Ok (Visible static), (Ok (Hidden _ | Absent) | Error _) -> Ok (Visible static)
  | Ok (Hidden _ | Absent), Error traits -> Error traits
  | Ok (Hidden _ | Absent), Ok (Visible instance) -> Ok (Visible instance)
  | Ok (Hidden hidden), Ok (Hidden _ | Absent) | Ok Absent, Ok (Hidden hidden) -> Ok (Hidden hidden)
  | Ok Absent, Ok Absent -> Ok Absent

and list_trait_candidates (state : State.state) receiver_type name =
  let list_bound_candidates bounds =
    List.map (fun bound -> Resolve.Names.Visible bound) (merge_bounds_by_trait state bounds)
  in
  match (receiver_type, list_meeting_closures state receiver_type) with
  | Types.Parameter parameter, _ ->
      list_bound_candidates
        (Interface.Properties.list_known_bounds state.lookups.interface
           ~list_bounds:(State.lookup_bounds state) (Types.Parameter parameter))
  | _, (_ :: _ as closures) -> list_bound_candidates (List.concat_map snd closures)
  | _, [] -> list_implemented_trait_lookups state receiver_type name

and list_meeting_closures (state : State.state) receiver_type =
  match State.find_domain state receiver_type with
  | Some domain ->
      Solver.list_sealed_closures state receiver_type
        ~includes:(List.exists (fun member -> List.mem member domain))
  | None -> []

and find_sealed_provider state receiver_type (trait : Types.trait_reference) =
  List.find_map
    (fun (sealed, closure) ->
      if
        List.exists
          (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait.trait)
          closure
      then Some sealed
      else None)
    (list_meeting_closures state receiver_type)

and has_sealed_method state receiver_type name =
  Option.is_some (State.find_domain state receiver_type)
  &&
  match resolve_overloads state receiver_type name with
  | Ok (Visible _) -> true
  | Ok (Hidden _ | Absent) | Error _ -> false

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
  let candidates =
    List.map
      (fun candidate -> (candidate, list_candidate_methods state name candidate))
      (list_trait_candidates state receiver_type name)
  in
  let visible_traits =
    List.filter_map
      (function
        | Resolve.Names.Visible trait, methods
          when List.exists
                 (fun (method_ : Types.trait_method) -> method_.method_receiver <> Path.Static)
                 methods ->
            Some trait
        | (Visible _ | Hidden _ | Absent), _ -> None)
      candidates
  in
  if not (is_one_family state visible_traits) then Error visible_traits
  else
    let list_methods_of make owner : Path.receiver -> overload Resolve.Names.lookup =
      match owner with
      | Some (Types.Named { path; _ }) ->
          let members = Members.list_member_lookups state path name in
          fun receiver ->
            Resolve.Names.map_visible make
              (Resolve.Names.choose_member members (Method { owner = path; name; receiver }))
      | _ -> fun _ -> Absent
    in
    let lookup_type_method =
      list_methods_of (fun method_path -> Type_overload method_path) (Some receiver_type)
    and lookup_list_method =
      list_methods_of
        (fun method_path -> List_overload method_path)
        (Types.find_list_of_array receiver_type)
    in
    Ok
      (Resolve.Names.collect_visible
         (List.map
            (fun receiver ->
              Resolve.Names.map_visible
                (fun overload -> (receiver, overload))
                (Resolve.Names.choose_visible
                   (lookup_type_method receiver
                    :: List.map
                         (fun (candidate, methods) ->
                           Resolve.Names.map_visible
                             (fun (trait, method_) -> Trait_overload (trait, method_))
                             (choose_trait_method name receiver candidate methods))
                         candidates
                   @ [
                       (match receiver with
                       | Path.Instance Own | Static -> Resolve.Names.Absent
                       | Instance (Read | Mut) -> lookup_list_method receiver);
                     ])))
            [ Path.Instance Read; Instance Mut; Instance Own ]))

and instantiate_trait_method state ~written ~self_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) =
  let instance =
    Instantiation.instantiate state ~written
      ~declared_on:
        (Method
           { owner = trait.trait; name = method_.method_name; receiver = method_.method_receiver })
      ~extra:
        (Types.make_trait_substitution
           (Members.list_trait_generics state.lookups trait.trait)
           ~self:self_type trait)
      (Members.read_method_signature state.signatures state.lookups trait.trait method_)
  in
  ( instance,
    {
      Tables.trait;
      name = method_.method_name;
      receiver = method_.method_receiver;
      self_type;
      instantiation = instance.instantiation;
    } )
