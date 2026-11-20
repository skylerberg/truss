let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let find_derived_method : Path.t -> Well_known.method_ option = function
  | Method { owner = Derived { trait; _ }; name; receiver } -> (
      match Well_known.find_method (Method { owner = trait; name; receiver }) with
      | Some method_ when List.mem method_ Resolve.Names.derived_methods -> Some method_
      | _ -> None)
  | _ -> None

let is_derived_method path = Option.is_some (find_derived_method path)

let collapse_spaces text =
  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false in
  let buffer = Buffer.create (String.length text) in
  String.iteri
    (fun index character ->
      if not (is_space character) then Buffer.add_char buffer character
      else if index = 0 || not (is_space text.[index - 1]) then Buffer.add_char buffer ' ')
    text;
  Buffer.contents buffer

let read_derives_entry (lookups : Lookups.t) ~(type_ : Path.t) ~(trait : Path.t) : Syntax.id =
  let key =
    match lookups.interface.names.find_key type_ with
    | Some key -> key
    | None ->
        raise_bug "`%s` derives `%s` and has no declaration" (Path.show type_) (Path.show trait)
  in
  let clauses =
    match (lookups.interface.names.read_definition key).kind with
    | Type_definition { clauses; _ } -> clauses
    | _ -> raise_bug "`%s` derives `%s` and is not a type" (Path.show type_) (Path.show trait)
  in
  match
    List.find_opt
      (fun (_, _, derived) -> Path.equal derived trait)
      (Interface.Definition.list_derives_entries
         (lookups.interface.read_resolved Interface key)
         clauses)
  with
  | Some (_, (written : Syntax.path_type), _) -> written.id
  | None ->
      raise_bug "`%s` derives `%s` and no `derives` entry names it" (Path.show type_)
        (Path.show trait)

let derive_form (lookups : Lookups.t) (path : Path.t) : Core.t option =
  match (path, find_derived_method path) with
  | Method { owner = Derived { type_; trait } as impl; _ }, Some derived_method -> (
      match
        ( Interface.Definition.find_impl_interface lookups.interface impl,
          Interface.Definition.find_type_interface lookups.interface type_,
          Interface.Impls.read_signature lookups.interface path )
      with
      | _, Some { shape = Todo_type; _ }, _ -> None
      | Some interface, Some { shape; _ }, Some signature ->
          let nodes = ref 0 and locals = ref 0 in
          let take_id () =
            let id = !nodes in
            incr nodes;
            id
          in
          let make_local () : Core.local =
            let local = !locals in
            incr locals;
            Synthetic local
          in
          let origin : Core.origin =
            Desugared { construct = read_derives_entry lookups ~type_ ~trait; desugaring = Derived }
          in
          let node type_ kind : Core.expression = { id = take_id (); origin; type_; kind } in
          let pattern type_ kind : Core.pattern = { id = take_id (); origin; type_; kind } in
          let statement kind : Core.statement = { id = take_id (); origin; kind } in
          let make_giving_block value : Core.block = { statements = []; value = Some value } in
          let arm pattern body : Core.arm =
            { patterns = [ pattern ]; guard = None; body; origin }
          in
          let self_type = interface.for_type in
          let list_bounds = Types.list_bounds interface.impl_generics in
          let result =
            match signature.output with
            | Returns type_ -> type_
            | Lends _ -> raise_bug "a derived method that lends"
          in
          let parameters : Core.parameter list =
            (match signature.receiver with
              | Some (mode, type_) ->
                  [ { Core.local = Self; mode; type_; default = None; callback_contract = None } ]
              | None -> [])
            @ List.mapi
                (fun index (info : Types.parameter_info) : Core.parameter ->
                  {
                    local = Trait_parameter { index; name = info.name };
                    mode = info.mode;
                    type_ = info.type_;
                    default = None;
                    callback_contract = None;
                  })
                signature.parameters
          in
          let make_other_place () : Core.place =
            match
              List.filter (fun (parameter : Core.parameter) -> parameter.local <> Self) parameters
            with
            | [ parameter ] -> Local { local = parameter.local; type_ = parameter.type_; origin }
            | _ -> raise_bug "`%s` takes one value beside its own" (Path.show path)
          in
          let make_method_call ?(type_arguments = []) (method_ : Well_known.method_) of_type
              arguments type_ =
            let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
            let reference : Types.trait_reference =
              { trait = Well_known.make_path owner; trait_arguments = []; associated = [] }
            in
            let evidence : Core.evidence =
              match
                Interface.Impls.find_evidence lookups.interface ~list_bounds of_type reference
              with
              | Some (From_impl { impl; substitution }) -> Impl { impl; substitution }
              | Some From_bound -> Bound
              | Some From_any -> Dynamic
              | Some Built_in | Some (Accepted _) | None ->
                  raise_bug "`%s` is derived for a type with a field that has none"
                    (Path.show reference.trait)
            in
            node type_
              (Call
                 (Callee_uses.make_call lookups.interface ~list_bounds
                    ~callee:
                      (Trait_method
                         {
                           trait = reference;
                           name;
                           receiver;
                           self_type = of_type;
                           instantiation = { Types.no_instantiation with type_arguments };
                           evidence;
                         })
                    ~arguments ~lends:None))
          in
          let trait_call method_ ~self_type ~evidence arguments type_ =
            let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
            node type_
              (Call
                 (Callee_uses.make_call lookups.interface ~list_bounds
                    ~callee:
                      (Trait_method
                         {
                           trait =
                             {
                               trait = Well_known.make_path owner;
                               trait_arguments = [];
                               associated = [];
                             };
                           name;
                           receiver;
                           self_type;
                           instantiation = Types.no_instantiation;
                           evidence;
                         })
                    ~arguments ~lends:None))
          in
          let text_argument text =
            Operands.build_argument Read
              (node (Types.make_named (Well_known.make_path String_slice) []) (String text))
          in
          let count_argument count =
            Operands.build_argument Read
              (node (Types.make_builtin UInt64) (Integer (Z.of_int count)))
          in
          let read place : Core.argument = Passed { mode = Read; value = Place place } in
          let variants =
            match shape with
            | Sum variants ->
                Some
                  (List.map
                     (fun (variant : Types.variant) ->
                       (variant.variant_name, Option.value variant.fields ~default:[]))
                     variants)
            | Record _ -> None
            | Todo_type | Builtin_type _ ->
                raise_bug "`%s` is derived for a type with no fields" (Path.show trait)
          in
          let alone = match variants with Some [ _ ] -> true | _ -> false in
          let record_fields () =
            match shape with
            | Record fields -> fields
            | _ -> raise_bug "a record's fields of a sum type"
          in
          let record_parts base =
            List.map
              (fun (field : Types.field) ->
                ( field,
                  Core.Field { base; field = field.field_name; type_ = field.field_type; origin } ))
              (record_fields ())
          in
          let list_bound (fields : Types.field list) =
            List.map (fun (field : Types.field) -> (field, make_local ())) fields
          in
          let binding variant bound : Core.pattern =
            pattern self_type
              (Variant
                 {
                   variant;
                   fields =
                     List.map
                       (fun ((field : Types.field), local) ->
                         ( field.field_name,
                           pattern field.field_type (Bind { local; is_var = false; mode = Read }) ))
                       bound;
                 })
          in
          let list_parts bound =
            List.map
              (fun ((field : Types.field), local) ->
                (field, Core.Local { local; type_ = field.field_type; origin }))
              bound
          in
          let self_place : Core.place = Local { local = Self; type_ = self_type; origin } in
          let make_variant_pattern variant : Core.pattern =
            pattern self_type (Variant { variant; fields = [] })
          in
          let of_self type_
              (each : string option -> int -> (Types.field * Core.place) list -> Core.block) =
            match variants with
            | None -> each None 0 (record_parts self_place)
            | Some variants ->
                make_giving_block
                  (node type_
                     (Match
                        {
                          scrutinees = [ Place self_place ];
                          arms =
                            List.mapi
                              (fun index (variant, fields) ->
                                let mine = list_bound fields in
                                arm (binding variant mine)
                                  (each (Some variant) index (list_parts mine)))
                              variants;
                        }))
          in
          let of_other other type_ variant (mine : (Types.field * Core.place) list) ~build_same
              ~build_different =
            match variant with
            | None -> build_same (record_parts other)
            | Some variant ->
                let theirs = list_bound (List.map fst mine) in
                node type_
                  (Match
                     {
                       scrutinees = [ Place other ];
                       arms =
                         arm (binding variant theirs)
                           (make_giving_block (build_same (list_parts theirs)))
                         ::
                         (if alone then []
                          else
                            [
                              arm (pattern self_type Wildcard)
                                (make_giving_block (build_different ()));
                            ]);
                     })
          in
          let bool = Types.bool and unit = Types.unit in
          let generate_body () : Core.block =
            match derived_method with
            | Equal_equal ->
                let other = make_other_place () in
                let make_each_equal mine theirs =
                  List.fold_left2
                    (fun so_far ((field : Types.field), mine) (_, theirs) ->
                      let this =
                        make_method_call Equal_equal field.field_type
                          [ read mine; read theirs ]
                          bool
                      in
                      match so_far with
                      | None -> Some this
                      | Some so_far ->
                          Some
                            (node bool
                               (Connective { connective = And; left = so_far; right = this })))
                    None mine theirs
                  |> function
                  | Some all -> all
                  | None -> node bool (Boolean true)
                in
                of_self bool (fun variant _ mine ->
                    make_giving_block
                      (match (variant, mine) with
                      | Some variant, [] ->
                          node bool
                            (Matches { value = Place other; pattern = make_variant_pattern variant })
                      | _ ->
                          of_other other bool variant mine ~build_same:(make_each_equal mine)
                            ~build_different:(fun () -> node bool (Boolean false))))
            | Hash_hash ->
                let hasher =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      Core.Local { local; type_; origin }
                  | [] -> raise_bug "`hash` takes a hasher"
                in
                let changed : Core.argument = Passed { mode = Mut; value = Place hasher } in
                let write number =
                  statement
                    (Evaluate
                       (node unit
                          (Call
                             (Callee_uses.make_call lookups.interface ~list_bounds
                                ~callee:
                                  (Function
                                     {
                                       path = Well_known.make_method_path Hasher_write;
                                       instantiation = Types.no_instantiation;
                                     })
                                ~arguments:
                                  [
                                    changed;
                                    Passed
                                      {
                                        mode = Read;
                                        value =
                                          Value
                                            (node (Types.make_builtin UInt64)
                                               (Integer (Z.of_int number)));
                                      };
                                  ]
                                ~lends:None))))
                in
                of_self unit (fun variant index mine ->
                    {
                      statements =
                        (if variant = None then [] else [ write index ])
                        @ List.map
                            (fun ((field : Types.field), mine) ->
                              statement
                                (Evaluate
                                   (make_method_call Hash_hash field.field_type
                                      [ read mine; changed ]
                                      unit)))
                            mine;
                      value = None;
                    })
            | Ordered_compare -> (
                let other = make_other_place () in
                let make_ordering variant =
                  node result
                    (Construct { variant = Some (Well_known.show_variant variant); fields = [] })
                in
                let list_declared variant fields =
                  Interface.Definition.sort_in_declared_order lookups.interface type_ ~variant
                    ~name_of:(fun ((field : Types.field), _) -> field.field_name)
                    fields
                in
                let rec compare_in_turn mine theirs =
                  match (mine, theirs) with
                  | [], _ | _, [] -> make_ordering Ordering_equal
                  | ((field : Types.field), mine) :: rest, (_, theirs) :: rest_of_theirs -> (
                      let compared =
                        make_method_call Ordered_compare field.field_type
                          [ read mine; read theirs ]
                          result
                      in
                      match rest with
                      | [] -> compared
                      | rest ->
                          let decided = make_local () in
                          node result
                            (Match
                               {
                                 scrutinees = [ Operands.build Own compared ];
                                 arms =
                                   [
                                     arm
                                       (pattern result
                                          (Variant
                                             {
                                               variant = Well_known.show_variant Ordering_equal;
                                               fields = [];
                                             }))
                                       (make_giving_block (compare_in_turn rest rest_of_theirs));
                                     arm
                                       (pattern result
                                          (Bind { local = decided; is_var = false; mode = Own }))
                                       (make_giving_block
                                          (node result
                                             (Use
                                                (Local { local = decided; type_ = result; origin }))));
                                   ];
                               }))
                in
                let number = Types.make_builtin UInt32 in
                match variants with
                | None | Some [ _ ] ->
                    of_self result (fun variant _ mine ->
                        make_giving_block
                          (of_other other result variant mine
                             ~build_same:(fun theirs ->
                               compare_in_turn (list_declared variant mine)
                                 (list_declared variant theirs))
                             ~build_different:(fun () -> make_ordering Ordering_equal)))
                | Some variants ->
                    let theirs = make_local () in
                    let numbered =
                      node number
                        (Match
                           {
                             scrutinees = [ Place other ];
                             arms =
                               List.mapi
                                 (fun index (variant, _) ->
                                   arm (make_variant_pattern variant)
                                     (make_giving_block (node number (Integer (Z.of_int index)))))
                                 variants;
                           })
                    in
                    let compare_by_number index =
                      node result
                        (If
                           {
                             condition =
                               node bool
                                 (Compare
                                    {
                                      comparison = Less;
                                      left = node number (Integer (Z.of_int index));
                                      right =
                                        node number
                                          (Use (Local { local = theirs; type_ = number; origin }));
                                    });
                             then_ = make_giving_block (make_ordering Ordering_less);
                             else_ = Some (make_giving_block (make_ordering Ordering_greater));
                             binds_lent_part = false;
                           })
                    in
                    let compared =
                      of_self result (fun variant index mine ->
                          make_giving_block
                            (of_other other result variant mine
                               ~build_same:(fun theirs ->
                                 compare_in_turn (list_declared variant mine)
                                   (list_declared variant theirs))
                               ~build_different:(fun () -> compare_by_number index)))
                    in
                    {
                      compared with
                      statements =
                        [
                          statement
                            (Let
                               {
                                 pattern =
                                   pattern number
                                     (Bind { local = theirs; is_var = false; mode = Own });
                                 value = Operands.build Own numbered;
                                 else_ = None;
                               });
                        ];
                    })
            | Default_default ->
                make_giving_block
                  (node self_type
                     (Construct
                        {
                          variant = None;
                          fields =
                            List.map
                              (fun (field : Types.field) ->
                                ( field.field_name,
                                  if field.field_has_default then None
                                  else
                                    Some
                                      (Core.Value
                                         (make_method_call Default_default field.field_type []
                                            field.field_type)) ))
                              (record_fields ());
                        }))
            | Serialize_serialize ->
                let sink, sink_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      (Core.Local { local; type_; origin }, type_)
                  | [] -> raise_bug "`serialize` takes a serializer"
                in
                let sink_argument : Core.argument = Passed { mode = Mut; value = Place sink } in
                let call method_ arguments =
                  statement
                    (Evaluate
                       (trait_call method_ ~self_type:sink_type ~evidence:Bound
                          (sink_argument :: arguments) unit))
                in
                let serialize_field ((field : Types.field), place) =
                  [
                    call Serializer_field [ text_argument field.field_name ];
                    statement
                      (Evaluate
                         (make_method_call Serialize_serialize field.field_type
                            ~type_arguments:[ Types.Type sink_type ]
                            [ read place; sink_argument ]
                            unit));
                  ]
                in
                of_self unit (fun variant _ mine ->
                    let begin_, end_ =
                      match variant with
                      | None ->
                          ( [ call Serializer_begin_record [ count_argument (List.length mine) ] ],
                            Well_known.Serializer_end_record )
                      | Some variant ->
                          ( [
                              call Serializer_begin_variant
                                [ text_argument variant; count_argument (List.length mine) ];
                            ],
                            Serializer_end_variant )
                    in
                    let mine =
                      Interface.Definition.sort_in_declared_order lookups.interface type_ ~variant
                        ~name_of:(fun ((field : Types.field), _) -> field.field_name)
                        mine
                    in
                    {
                      statements = begin_ @ List.concat_map serialize_field mine @ [ call end_ [] ];
                      value = None;
                    })
            | Deserialize_deserialize -> (
                let source, source_type =
                  match parameters with
                  | [ ({ local; type_; _ } : Core.parameter) ] ->
                      (Core.Local { local; type_; origin }, type_)
                  | _ -> raise_bug "`deserialize` takes a deserializer"
                in
                let make_source_argument mode : Core.argument =
                  Passed { mode; value = Place source }
                in
                let error_type =
                  match result with
                  | Named { arguments = [ _; Type error ]; _ } -> error
                  | _ -> raise_bug "`deserialize` returns a `Result`"
                in
                let make_result_type ok =
                  Types.make_named (Well_known.make_path Result) [ ok; error_type ]
                in
                let make_source_call method_ arguments type_ =
                  trait_call method_ ~self_type:source_type ~evidence:Bound
                    (make_source_argument Mut :: arguments)
                    type_
                in
                let finish method_ = statement (Evaluate (make_source_call method_ [] unit)) in
                let make_attempt ok call =
                  let value = make_local () and error = make_local () in
                  node ok
                    (Match
                       {
                         scrutinees = [ Operands.build Own call ];
                         arms =
                           [
                             arm
                               (pattern (make_result_type ok)
                                  (Variant
                                     {
                                       variant = Well_known.show_variant Result_ok;
                                       fields =
                                         [
                                           ( Well_known.show_field Result_ok_value,
                                             pattern ok
                                               (Bind { local = value; is_var = false; mode = Own })
                                           );
                                         ];
                                     }))
                               (make_giving_block
                                  (node ok (Use (Local { local = value; type_ = ok; origin }))));
                             arm
                               (pattern (make_result_type ok)
                                  (Variant
                                     {
                                       variant = Well_known.show_variant Result_err;
                                       fields =
                                         [
                                           ( Well_known.show_field Result_err_error,
                                             pattern error_type
                                               (Bind { local = error; is_var = false; mode = Own })
                                           );
                                         ];
                                     }))
                               (make_giving_block
                                  (node Types.Never
                                     (Return
                                        (Some
                                           (node result
                                              (Construct
                                                 {
                                                   variant =
                                                     Some (Well_known.show_variant Result_err);
                                                   fields =
                                                     [
                                                       ( Well_known.show_field Result_err_error,
                                                         Some
                                                           (Core.Value
                                                              (node error_type
                                                                 (Use
                                                                    (Local
                                                                       {
                                                                         local = error;
                                                                         type_ = error_type;
                                                                         origin;
                                                                       })))) );
                                                     ];
                                                 }))))));
                           ];
                       })
                in
                let read_field function_ (field : Types.field) ok =
                  make_attempt ok
                    (node (make_result_type ok)
                       (Call
                          (Callee_uses.make_call lookups.interface ~list_bounds
                             ~callee:
                               (Function
                                  {
                                    path = Well_known.make_path function_;
                                    instantiation =
                                      {
                                        Types.no_instantiation with
                                        type_arguments =
                                          [ Types.Type field.field_type; Types.Type source_type ];
                                      };
                                  })
                             ~arguments:[ make_source_argument Mut; text_argument field.field_name ]
                             ~lends:None)))
                in
                let invariant_clauses =
                  match lookups.interface.names.find_key type_ with
                  | None -> []
                  | Some key -> (
                      match lookups.read_contract key with
                      | { definition = Type { invariants; _ }; _ } ->
                          let spans = lookups.interface.names.read_spans key in
                          let text = lookups.interface.names.read_text key in
                          let quote_origin (origin : Core.origin) =
                            collapse_spaces
                              (Source.Definition_span.quote text
                                 (Source.Definition_span.locate spans
                                    (Core_walk.locate_origin origin)))
                          in
                          List.mapi
                            (fun index (invariant : Core.condition) ->
                              if invariant.executable then
                                Some (index, quote_origin invariant.value.origin)
                              else None)
                            invariants
                          |> List.filter_map Fun.id
                      | _ -> [])
                in
                let make_invariant_check built_place (index, text) =
                  let bool = Types.bool and uint64 = Types.make_builtin UInt64 in
                  let holds =
                    node bool
                      (Call
                         (Callee_uses.make_call lookups.interface ~list_bounds
                            ~callee:
                              (Intrinsic
                                 {
                                   operation = Runtime Holds_invariant;
                                   type_arguments = [ Types.Type self_type ];
                                 })
                            ~arguments:
                              [
                                Passed { mode = Read; value = Place built_place };
                                Operands.build_argument Read
                                  (node uint64 (Integer (Z.of_int index)));
                              ]
                            ~lends:None))
                  in
                  let error =
                    trait_call Deserializer_error ~self_type:source_type ~evidence:Bound
                      [
                        make_source_argument Read;
                        text_argument ("breaks the invariant `" ^ text ^ "`");
                      ]
                      error_type
                  in
                  let refused =
                    node Types.Never
                      (Return
                         (Some
                            (node result
                               (Construct
                                  {
                                    variant = Some (Well_known.show_variant Result_err);
                                    fields =
                                      [
                                        ( Well_known.show_field Result_err_error,
                                          Some (Operands.build Own error) );
                                      ];
                                  }))))
                  in
                  statement
                    (Evaluate
                       (node unit
                          (If
                             {
                               condition = node bool (Not holds);
                               then_ =
                                 { statements = [ statement (Evaluate refused) ]; value = None };
                               else_ = None;
                               binds_lent_part = false;
                             })))
                in
                let bind_local local type_ ~is_var value =
                  statement
                    (Let
                       {
                         pattern = pattern type_ (Bind { local; is_var; mode = Own });
                         value = Operands.build Own value;
                         else_ = None;
                       })
                in
                let make_fields_then_built variant (fields : Types.field list) end_ : Core.block =
                  let required, defaulted =
                    match variant with
                    | None ->
                        List.partition
                          (fun (field : Types.field) -> not field.field_has_default)
                          fields
                    | Some _ -> (fields, [])
                  in
                  let read =
                    List.map (fun (field : Types.field) -> (field, make_local ())) required
                  in
                  let built = make_local () in
                  let built_place : Core.place =
                    Local { local = built; type_ = self_type; origin }
                  in
                  let lets =
                    List.map
                      (fun ((field : Types.field), local) ->
                        bind_local local field.field_type ~is_var:false
                          (read_field Deserialize_required field field.field_type))
                      read
                  in
                  let construct =
                    node self_type
                      (Construct
                         {
                           variant;
                           fields =
                             List.map
                               (fun (field : Types.field) ->
                                 ( field.field_name,
                                   match List.assq_opt field read with
                                   | Some local ->
                                       Some
                                         (Core.Value
                                            (node field.field_type
                                               (Use
                                                  (Local { local; type_ = field.field_type; origin }))))
                                   | None -> None ))
                               fields;
                         })
                  in
                  let updates =
                    List.map
                      (fun (field : Types.field) ->
                        let optional =
                          Types.make_named (Well_known.make_path Option) [ field.field_type ]
                        in
                        let present = make_local () in
                        statement
                          (Evaluate
                             (node unit
                                (Match
                                   {
                                     scrutinees =
                                       [
                                         Operands.build Own
                                           (read_field Deserialize_optional field optional);
                                       ];
                                     arms =
                                       [
                                         arm
                                           (pattern optional
                                              (Variant
                                                 {
                                                   variant = Well_known.show_variant Option_some;
                                                   fields =
                                                     [
                                                       ( Well_known.show_field Option_some_value,
                                                         pattern field.field_type
                                                           (Bind
                                                              {
                                                                local = present;
                                                                is_var = false;
                                                                mode = Own;
                                                              }) );
                                                     ];
                                                 }))
                                           {
                                             statements =
                                               [
                                                 statement
                                                   (Assign
                                                      {
                                                        target =
                                                          (match variant with
                                                          | None ->
                                                              Field
                                                                {
                                                                  base = built_place;
                                                                  field = field.field_name;
                                                                  type_ = field.field_type;
                                                                  origin;
                                                                }
                                                          | Some _ ->
                                                              raise_bug
                                                                "a variant's field with a default");
                                                        value =
                                                          node field.field_type
                                                            (Use
                                                               (Local
                                                                  {
                                                                    local = present;
                                                                    type_ = field.field_type;
                                                                    origin;
                                                                  }));
                                                      });
                                               ];
                                             value = None;
                                           };
                                         arm (pattern optional Wildcard)
                                           { statements = []; value = None };
                                       ];
                                   }))))
                      defaulted
                  in
                  {
                    statements =
                      lets
                      @ [ bind_local built self_type ~is_var:(defaulted <> []) construct ]
                      @ updates
                      @ [ finish end_ ]
                      @ List.map (make_invariant_check built_place) invariant_clauses;
                    value =
                      Some
                        (node result
                           (Construct
                              {
                                variant = Some (Well_known.show_variant Result_ok);
                                fields =
                                  [
                                    ( Well_known.show_field Result_ok_value,
                                      Some (Operands.build Own (node self_type (Use built_place)))
                                    );
                                  ];
                              }));
                  }
                in
                let make_begun method_ =
                  statement
                    (Evaluate
                       (make_attempt unit (make_source_call method_ [] (make_result_type unit))))
                in
                match variants with
                | None ->
                    let body =
                      make_fields_then_built None (record_fields ()) Deserializer_end_record
                    in
                    {
                      body with
                      statements = make_begun Deserializer_begin_record :: body.statements;
                    }
                | Some variants ->
                    let string_type = Types.make_named (Well_known.make_path String) [] in
                    let name = make_local () in
                    let name_place : Core.place =
                      Local { local = name; type_ = string_type; origin }
                    in
                    let equal =
                      let { Well_known.owner; name; receiver } =
                        Well_known.locate_method Equal_equal
                      in
                      let reference : Types.trait_reference =
                        {
                          trait = Well_known.make_path owner;
                          trait_arguments = [];
                          associated = [];
                        }
                      in
                      match
                        Interface.Impls.find_evidence lookups.interface ~list_bounds string_type
                          reference
                      with
                      | Some (From_impl { impl; substitution }) ->
                          Callee_uses.make_callee lookups.interface ~list_bounds
                            (Trait_method
                               {
                                 trait = reference;
                                 name;
                                 receiver;
                                 self_type = string_type;
                                 instantiation = Types.no_instantiation;
                                 evidence = Impl { impl; substitution };
                               })
                      | _ -> raise_bug "`String` has no `Equal`"
                    in
                    let unknown =
                      node Types.Never
                        (Return
                           (Some
                              (node result
                                 (Construct
                                    {
                                      variant = Some (Well_known.show_variant Result_err);
                                      fields =
                                        [
                                          ( Well_known.show_field Result_err_error,
                                            Some
                                              (Core.Value
                                                 (node error_type
                                                    (Call
                                                       (Callee_uses.make_call lookups.interface
                                                          ~list_bounds
                                                          ~callee:
                                                            (Function
                                                               {
                                                                 path =
                                                                   Well_known.make_path
                                                                     Unknown_variant;
                                                                 instantiation =
                                                                   {
                                                                     Types.no_instantiation with
                                                                     type_arguments =
                                                                       [ Types.Type source_type ];
                                                                   };
                                                               })
                                                          ~arguments:
                                                            [
                                                              make_source_argument Read;
                                                              read name_place;
                                                            ]
                                                          ~lends:None)))) );
                                        ];
                                    }))))
                    in
                    {
                      statements =
                        [
                          bind_local name string_type ~is_var:false
                            (make_attempt string_type
                               (make_source_call Deserializer_variant []
                                  (make_result_type string_type)));
                        ];
                      value =
                        Some
                          (node result
                             (Match
                                {
                                  scrutinees = [ Place name_place ];
                                  arms =
                                    List.map
                                      (fun (variant, fields) ->
                                        arm
                                          (pattern string_type
                                             (Equal_to { value = String_constant variant; equal }))
                                          (make_fields_then_built (Some variant) fields
                                             Deserializer_end_variant))
                                      variants
                                    @ [
                                        arm (pattern string_type Wildcard)
                                          (make_giving_block unknown);
                                      ];
                                }));
                    })
            | _ -> raise_bug "`%s` cannot be derived" (Path.show path)
          in
          let body = generate_body () in
          let ensures =
            match derived_method with
            | Ordered_compare ->
                [
                  node bool (Identical (node result Result, node result (Block (generate_body ()))));
                ]
            | _ -> []
          in
          Some
            {
              definition =
                Function
                  {
                    parameters;
                    contract =
                      {
                        panics_unless = [];
                        requires = [];
                        ensures =
                          List.map
                            (fun clause : Core.expression Core.conditional ->
                              { holds_when = []; clause })
                            ensures;
                        decreases = [];
                        costs = [];
                      };
                    body = Some body;
                  };
              origin;
            }
      | _ -> None)
  | _ -> None
