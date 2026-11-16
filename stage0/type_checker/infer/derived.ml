let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let gives (trait : Path.t) name =
  match (Well_known.of_path trait, name) with
  | Some Equal, "equal"
  | Some Hash, "hash"
  | Some Ordered, "compare"
  | Some Default, "default"
  | Some Serialize, "serialize"
  | Some Deserialize, "deserialize" ->
      true
  | _ -> false

let collapse_spaces text =
  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false in
  let buffer = Buffer.create (String.length text) in
  String.iteri
    (fun index character ->
      if not (is_space character) then Buffer.add_char buffer character
      else if index = 0 || not (is_space text.[index - 1]) then Buffer.add_char buffer ' ')
    text;
  Buffer.contents buffer

let derive_form (lookups : Lookups.t) (path : Path.t) : Core.t option =
  match path with
  | Method { owner = Derived { type_; trait } as impl; name; receiver = _ } when gives trait name
    -> (
      match
        ( Interface.Definition.read_impl_interface lookups.interface impl,
          Interface.Definition.read_type_interface lookups.interface type_,
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
          let origin = 0 in
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
              | Some (((Read | Mut | Own) as receiver), type_) ->
                  [
                    {
                      Core.local = Self;
                      name = "self";
                      mode = (match receiver with Mut -> Mut | Own -> Own | _ -> Read);
                      type_;
                      default = None;
                      callback_contract = None;
                    };
                  ]
              | Some (Static, _) | None -> [])
            @ List.map
                (fun (info : Types.parameter_info) : Core.parameter ->
                  {
                    local = make_local ();
                    name = info.name;
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
          let make_method_call ?(type_arguments = []) (wanted : Path.t) name
              (receiver : Path.receiver) of_type arguments type_ =
            let reference : Types.trait_reference =
              { trait = wanted; trait_arguments = []; associated = [] }
            in
            let evidence : Core.evidence =
              match
                Interface.Impls.find_evidence lookups.interface ~list_bounds of_type reference
              with
              | Some (From_impl { impl; substitution }) -> Impl { impl; arguments = substitution }
              | Some From_bound -> Bound
              | Some From_any -> Dynamic
              | Some Built_in | Some (Accepted _) | None ->
                  raise_bug "`%s` is derived for a type with a field that has none"
                    (Path.show wanted)
            in
            node type_
              (Call
                 {
                   callee =
                     Trait_method
                       {
                         trait = reference;
                         name;
                         receiver;
                         self_type = of_type;
                         type_arguments;
                         evidence;
                       };
                   arguments;
                   lends = None;
                   uses = Types.no_capabilities;
                 })
          in
          let trait_call ~trait ~name ~receiver ~self_type ~evidence arguments type_ =
            node type_
              (Call
                 {
                   callee =
                     Trait_method
                       {
                         trait = { trait; trait_arguments = []; associated = [] };
                         name;
                         receiver;
                         self_type;
                         type_arguments = [];
                         evidence;
                       };
                   arguments;
                   lends = None;
                   uses = Types.no_capabilities;
                 })
          in
          let text_argument text =
            Operands.build_argument Read
              (node (Types.make_named (Well_known.make_path String_slice) []) (String text))
          in
          let count_argument count =
            Operands.build_argument Read
              (node (Types.make_builtin UInt64) (Integer (Z.of_int count)))
          in
          let read place : Core.argument =
            Passed { mode = Read; value = Place place; mode_keyword = None }
          in
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
          let list_bound name_field (fields : Types.field list) =
            List.map
              (fun (field : Types.field) -> (field, make_local (), name_field field.field_name))
              fields
          in
          let binding variant bound : Core.pattern =
            pattern self_type
              (Variant
                 {
                   variant;
                   fields =
                     List.map
                       (fun ((field : Types.field), local, name) ->
                         ( field.field_name,
                           pattern field.field_type
                             (Bind { local; name; is_var = false; mode = Read }) ))
                       bound;
                 })
          in
          let list_parts bound =
            List.map
              (fun ((field : Types.field), local, _) ->
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
                                let mine = list_bound Fun.id fields in
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
                let theirs = list_bound (fun name -> "other_" ^ name) (List.map fst mine) in
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
          let trait_name = match trait with Top { name; _ } -> name | _ -> Path.show trait in
          let generate_body () : Core.block =
            match (trait_name, name) with
            | "Equal", "equal" ->
                let other = make_other_place () in
                let make_each_equal mine theirs =
                  List.fold_left2
                    (fun so_far ((field : Types.field), mine) (_, theirs) ->
                      let this =
                        make_method_call trait "equal" Read field.field_type
                          [ read mine; read theirs ]
                          bool
                      in
                      match so_far with
                      | None -> Some this
                      | Some so_far -> Some (node bool (And (so_far, this))))
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
            | "Hash", "hash" ->
                let hasher, hasher_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      (Core.Local { local; type_; origin }, type_)
                  | [] -> raise_bug "`hash` takes a hasher"
                in
                let hasher_path =
                  match hasher_type with
                  | Named { path; _ } -> path
                  | _ -> raise_bug "a hasher that is not a named type"
                in
                let changed : Core.argument =
                  Passed { mode = Mut; value = Place hasher; mode_keyword = None }
                in
                let write number =
                  statement
                    (Evaluate
                       (node unit
                          (Call
                             {
                               callee =
                                 Function
                                   {
                                     path =
                                       Method
                                         { owner = hasher_path; name = "write"; receiver = Mut };
                                     type_arguments = [];
                                   };
                               arguments =
                                 [
                                   changed;
                                   Passed
                                     {
                                       mode = Read;
                                       value =
                                         Value
                                           (node (Types.make_builtin UInt64)
                                              (Integer (Z.of_int number)));
                                       mode_keyword = None;
                                     };
                                 ];
                               lends = None;
                               uses = Types.no_capabilities;
                             })))
                in
                of_self unit (fun variant index mine ->
                    {
                      statements =
                        (if variant = None then [] else [ write index ])
                        @ List.map
                            (fun ((field : Types.field), mine) ->
                              statement
                                (Evaluate
                                   (make_method_call trait "hash" Read field.field_type
                                      [ read mine; changed ]
                                      unit)))
                            mine;
                      value = None;
                    })
            | "Ordered", "compare" -> (
                let other = make_other_place () in
                let make_ordering name =
                  node result (Construct { variant = Some name; fields = [] })
                in
                let list_declared variant fields =
                  Interface.Definition.sort_in_declared_order lookups.interface type_ ~variant
                    ~name_of:(fun ((field : Types.field), _) -> field.field_name)
                    fields
                in
                let rec compare_in_turn mine theirs =
                  match (mine, theirs) with
                  | [], _ | _, [] -> make_ordering "Equal"
                  | ((field : Types.field), mine) :: rest, (_, theirs) :: rest_of_theirs -> (
                      let compared =
                        make_method_call trait "compare" Read field.field_type
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
                                       (pattern result (Variant { variant = "Equal"; fields = [] }))
                                       (make_giving_block (compare_in_turn rest rest_of_theirs));
                                     arm
                                       (pattern result
                                          (Bind
                                             {
                                               local = decided;
                                               name = "decided";
                                               is_var = false;
                                               mode = Own;
                                             }))
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
                             ~build_different:(fun () -> make_ordering "Equal")))
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
                             then_ = make_giving_block (make_ordering "Less");
                             else_ = Some (make_giving_block (make_ordering "Greater"));
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
                                     (Bind
                                        {
                                          local = theirs;
                                          name = "theirs";
                                          is_var = false;
                                          mode = Own;
                                        });
                                 value = Operands.build Own numbered;
                                 else_ = None;
                               });
                        ];
                    })
            | "Default", "default" ->
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
                                         (make_method_call trait "default" Static field.field_type
                                            [] field.field_type)) ))
                              (record_fields ());
                        }))
            | "Serialize", "serialize" ->
                let sink, sink_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      (Core.Local { local; type_; origin }, type_)
                  | [] -> raise_bug "`serialize` takes a serializer"
                in
                let sink_argument : Core.argument =
                  Passed { mode = Mut; value = Place sink; mode_keyword = None }
                in
                let serializer = Well_known.make_path Serializer in
                let call name arguments =
                  statement
                    (Evaluate
                       (trait_call ~trait:serializer ~name ~receiver:Mut ~self_type:sink_type
                          ~evidence:Bound (sink_argument :: arguments) unit))
                in
                let serialize_field ((field : Types.field), place) =
                  [
                    call "field" [ text_argument field.field_name ];
                    statement
                      (Evaluate
                         (make_method_call trait "serialize" Read field.field_type
                            ~type_arguments:[ Types.Type sink_type ]
                            [ read place; sink_argument ]
                            unit));
                  ]
                in
                of_self unit (fun variant _ mine ->
                    let begin_, end_ =
                      match variant with
                      | None ->
                          ( [ call "begin_record" [ count_argument (List.length mine) ] ],
                            "end_record" )
                      | Some variant ->
                          ( [
                              call "begin_variant"
                                [ text_argument variant; count_argument (List.length mine) ];
                            ],
                            "end_variant" )
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
            | "Deserialize", "deserialize" -> (
                let source, source_type =
                  match parameters with
                  | [ ({ local; type_; _ } : Core.parameter) ] ->
                      (Core.Local { local; type_; origin }, type_)
                  | _ -> raise_bug "`deserialize` takes a deserializer"
                in
                let make_source_argument mode : Core.argument =
                  Passed { mode; value = Place source; mode_keyword = None }
                in
                let deserializer = Well_known.make_path Deserializer in
                let error_type =
                  match result with
                  | Named { arguments = [ _; Type error ]; _ } -> error
                  | _ -> raise_bug "`deserialize` returns a `Result`"
                in
                let make_result_type ok =
                  Types.make_named (Well_known.make_path Result) [ ok; error_type ]
                in
                let make_source_call name arguments type_ =
                  trait_call ~trait:deserializer ~name ~receiver:Mut ~self_type:source_type
                    ~evidence:Bound
                    (make_source_argument Mut :: arguments)
                    type_
                in
                let finish name = statement (Evaluate (make_source_call name [] unit)) in
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
                                       variant = "Ok";
                                       fields =
                                         [
                                           ( "value",
                                             pattern ok
                                               (Bind
                                                  {
                                                    local = value;
                                                    name = "value";
                                                    is_var = false;
                                                    mode = Own;
                                                  }) );
                                         ];
                                     }))
                               (make_giving_block
                                  (node ok (Use (Local { local = value; type_ = ok; origin }))));
                             arm
                               (pattern (make_result_type ok)
                                  (Variant
                                     {
                                       variant = "Err";
                                       fields =
                                         [
                                           ( "error",
                                             pattern error_type
                                               (Bind
                                                  {
                                                    local = error;
                                                    name = "error";
                                                    is_var = false;
                                                    mode = Own;
                                                  }) );
                                         ];
                                     }))
                               (make_giving_block
                                  (node Types.Never
                                     (Return
                                        (Some
                                           (node result
                                              (Construct
                                                 {
                                                   variant = Some "Err";
                                                   fields =
                                                     [
                                                       ( "error",
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
                          {
                            callee =
                              Function
                                {
                                  path = Well_known.make_path function_;
                                  type_arguments =
                                    [ Types.Type field.field_type; Types.Type source_type ];
                                };
                            arguments = [ make_source_argument Mut; text_argument field.field_name ];
                            lends = None;
                            uses = Types.no_capabilities;
                          }))
                in
                let invariant_clauses =
                  match lookups.interface.names.find_key type_ with
                  | None -> []
                  | Some key -> (
                      match lookups.read_contract key with
                      | { definition = Type { invariants; _ } } ->
                          let spans = lookups.interface.names.read_spans key in
                          let text = lookups.interface.names.read_text key in
                          let quote_origin (origin : Core.origin) =
                            collapse_spaces
                              (Source.Definition_span.quote text
                                 (Source.Definition_span.locate spans origin))
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
                         {
                           callee =
                             Intrinsic
                               {
                                 operation = Holds_invariant;
                                 type_arguments = [ Types.Type self_type ];
                               };
                           arguments =
                             [
                               Passed
                                 { mode = Read; value = Place built_place; mode_keyword = None };
                               Operands.build_argument Read (node uint64 (Integer (Z.of_int index)));
                             ];
                           lends = None;
                           uses = Types.no_capabilities;
                         })
                  in
                  let error =
                    trait_call ~trait:deserializer ~name:"error" ~receiver:Read
                      ~self_type:source_type ~evidence:Bound
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
                                    variant = Some "Err";
                                    fields = [ ("error", Some (Operands.build Own error)) ];
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
                let bind_local local name type_ ~is_var value =
                  statement
                    (Let
                       {
                         pattern = pattern type_ (Bind { local; name; is_var; mode = Own });
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
                        bind_local local field.field_name field.field_type ~is_var:false
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
                                                   variant = "Some";
                                                   fields =
                                                     [
                                                       ( "value",
                                                         pattern field.field_type
                                                           (Bind
                                                              {
                                                                local = present;
                                                                name = field.field_name;
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
                      @ [ bind_local built "built" self_type ~is_var:(defaulted <> []) construct ]
                      @ updates
                      @ [ finish end_ ]
                      @ List.map (make_invariant_check built_place) invariant_clauses;
                    value =
                      Some
                        (node result
                           (Construct
                              {
                                variant = Some "Ok";
                                fields =
                                  [
                                    ( "value",
                                      Some (Operands.build Own (node self_type (Use built_place)))
                                    );
                                  ];
                              }));
                  }
                in
                let make_begun name =
                  statement
                    (Evaluate (make_attempt unit (make_source_call name [] (make_result_type unit))))
                in
                match variants with
                | None ->
                    let body = make_fields_then_built None (record_fields ()) "end_record" in
                    { body with statements = make_begun "begin_record" :: body.statements }
                | Some variants ->
                    let string_type = Types.make_named (Well_known.make_path String) [] in
                    let name = make_local () in
                    let name_place : Core.place =
                      Local { local = name; type_ = string_type; origin }
                    in
                    let equal =
                      let reference : Types.trait_reference =
                        {
                          trait = Well_known.make_path Equal;
                          trait_arguments = [];
                          associated = [];
                        }
                      in
                      match
                        Interface.Impls.find_evidence lookups.interface ~list_bounds string_type
                          reference
                      with
                      | Some (From_impl { impl; substitution }) ->
                          Core.Trait_method
                            {
                              trait = reference;
                              name = "equal";
                              receiver = Read;
                              self_type = string_type;
                              type_arguments = [];
                              evidence = Impl { impl; arguments = substitution };
                            }
                      | _ -> raise_bug "`String` has no `Equal`"
                    in
                    let unknown =
                      node Types.Never
                        (Return
                           (Some
                              (node result
                                 (Construct
                                    {
                                      variant = Some "Err";
                                      fields =
                                        [
                                          ( "error",
                                            Some
                                              (Core.Value
                                                 (node error_type
                                                    (Call
                                                       {
                                                         callee =
                                                           Function
                                                             {
                                                               path =
                                                                 Well_known.make_path
                                                                   Unknown_variant;
                                                               type_arguments =
                                                                 [ Types.Type source_type ];
                                                             };
                                                         arguments =
                                                           [
                                                             make_source_argument Read;
                                                             read name_place;
                                                           ];
                                                         lends = None;
                                                         uses = Types.no_capabilities;
                                                       }))) );
                                        ];
                                    }))))
                    in
                    {
                      statements =
                        [
                          bind_local name "name" string_type ~is_var:false
                            (make_attempt string_type
                               (make_source_call "variant" [] (make_result_type string_type)));
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
                                             "end_variant"))
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
            match (trait_name, name) with
            | "Ordered", "compare" ->
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
                    contract = { requires = []; ensures; decreases = []; costs = [] };
                    body = Some body;
                  };
            }
      | _ -> None)
  | _ -> None
