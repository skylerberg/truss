(* Generates the core forms of the methods of a derived [impl]: each is the
   body that the method would have if it were written by hand. [compare]
   orders by variant, in declaration order, and then by each field in order.
   A method with a default body in the trait, such as [not_equal], uses the
   trait's core form. *)
module Impls = Interface.Impls
module Environment = Interface.Environment

let bug format = Compiler_bug.bug ~stage:"Infer" format

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

let form database (path : Path.t) : Core.t option =
  match path with
  | Method { owner = Derived { type_; trait } as impl; name; receiver = _ } when gives trait name
    -> (
      match
        ( Impls.impl_interface database impl,
          Query.demand database Environment.type_interface type_,
          Impls.signature database path )
      with
      (* A type whose definition is [todo] has no fields to derive from. *)
      | _, Some { shape = Todo_type; _ }, _ -> None
      | Some interface, Some { shape; _ }, Some signature ->
          let nodes = ref 0 and locals = ref 0 in
          let id () =
            let id = !nodes in
            incr nodes;
            id
          in
          let local () : Core.local =
            let local = !locals in
            incr locals;
            Synthetic local
          in
          (* Generated code has no source text, so every node has the origin
             0. *)
          let origin = 0 in
          let node type_ kind : Core.expression = { id = id (); origin; type_; kind } in
          let pattern type_ kind : Core.pattern = { id = id (); origin; type_; kind } in
          let statement kind : Core.statement = { id = id (); origin; kind } in
          let giving value : Core.block = { statements = []; value = Some value } in
          let arm pattern body : Core.arm =
            { patterns = [ pattern ]; guard = None; body; origin }
          in
          let self_type = interface.for_type in
          let bounds = Types.bounds_of interface.impl_generics in
          let result =
            match signature.output with
            | Returns type_ -> type_
            | Yields _ | Lends _ -> bug "a derived method that yields"
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
                    local = local ();
                    name = info.name;
                    mode = info.mode;
                    type_ = info.type_;
                    default = None;
                    callback_contract = None;
                  })
                signature.parameters
          in
          let other_place () : Core.place =
            match
              List.filter (fun (parameter : Core.parameter) -> parameter.local <> Self) parameters
            with
            | [ parameter ] -> Local { local = parameter.local; type_ = parameter.type_; origin }
            | _ -> bug "`%s` takes one value beside its own" (Path.show path)
          in
          (* A call of a method of the trait [wanted] on a value of
             [of_type]. The evidence is the type's [impl], or a bound if the
             type is a generic parameter. *)
          let method_of ?(type_arguments = []) (wanted : Path.t) name (receiver : Path.receiver)
              of_type arguments type_ =
            let reference : Types.trait_reference =
              { trait = wanted; trait_arguments = []; associated = [] }
            in
            let evidence : Core.evidence =
              match Impls.implements database ~bounds of_type reference with
              | Some (From_impl { impl; substitution }) -> Impl { impl; arguments = substitution }
              | Some From_bound -> Bound
              | Some From_any -> Dynamic
              | Some Built_in | Some (Accepted _) | None ->
                  bug "`%s` is derived for a type with a field that has none" (Path.show wanted)
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
          let text_argument text : Core.argument =
            Passed
              {
                mode = Read;
                value = Value (node (Types.named (Well_known.path String_slice) []) (String text));
                mark = None;
              }
          in
          let count_argument count : Core.argument =
            Passed
              {
                mode = Read;
                value = Value (node (Types.builtin USize) (Integer (Z.of_int count)));
                mark = None;
              }
          in
          let read place : Core.argument =
            Passed { mode = Read; value = Place place; mark = None }
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
            | Todo_type | Builtin_type _ | Error_shape _ ->
                bug "`%s` is derived for a type with no fields" (Path.show trait)
          in
          let alone = match variants with Some [ _ ] -> true | _ -> false in
          let record_fields () =
            match shape with Record fields -> fields | _ -> bug "a record's fields of a sum type"
          in
          (* The fields of a record, each as a place inside the record at
             [base]. *)
          let record_parts base =
            List.map
              (fun (field : Types.field) ->
                ( field,
                  Core.Field { base; field = field.field_name; type_ = field.field_type; origin } ))
              (record_fields ())
          in
          (* The fields of a variant are reachable only through a pattern.
             The pattern binds each field, borrowed from the matched value. *)
          let bound named (fields : Types.field list) =
            List.map (fun (field : Types.field) -> (field, local (), named field.field_name)) fields
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
          let parts bound =
            List.map
              (fun ((field : Types.field), local, _) ->
                (field, Core.Local { local; type_ = field.field_type; origin }))
              bound
          in
          let self_place : Core.place = Local { local = Self; type_ = self_type; origin } in
          let is variant : Core.pattern = pattern self_type (Variant { variant; fields = [] }) in
          (* Applies [each] to the fields of [self]: to the fields of a
             record, or, for a sum type, to the fields of each variant in a
             [match] with one arm per variant. *)
          let of_self type_
              (each : string option -> int -> (Types.field * Core.place) list -> Core.block) =
            match variants with
            | None -> each None 0 (record_parts self_place)
            | Some variants ->
                giving
                  (node type_
                     (Match
                        {
                          scrutinees = [ Place self_place ];
                          arms =
                            List.mapi
                              (fun index (variant, fields) ->
                                let mine = bound Fun.id fields in
                                arm (binding variant mine) (each (Some variant) index (parts mine)))
                              variants;
                        }))
          in
          (* Matches [other]. If [other] is the same variant as [self], the
             result is [same] applied to the fields of [other]. If it is a
             different variant, the result is [different ()]. *)
          let of_other other type_ variant (mine : (Types.field * Core.place) list) ~same ~different
              =
            match variant with
            | None -> same (record_parts other)
            | Some variant ->
                let theirs = bound (fun name -> "other_" ^ name) (List.map fst mine) in
                node type_
                  (Match
                     {
                       scrutinees = [ Place other ];
                       arms =
                         arm (binding variant theirs) (giving (same (parts theirs)))
                         ::
                         (if alone then []
                          else [ arm (pattern self_type Wildcard) (giving (different ())) ]);
                     })
          in
          let bool = Types.bool and unit = Types.unit in
          let trait_name = match trait with Top { name; _ } -> name | _ -> Path.show trait in
          let body : Core.block =
            match (trait_name, name) with
            | "Equal", "equal" ->
                let other = other_place () in
                let each_equal mine theirs =
                  List.fold_left2
                    (fun so_far ((field : Types.field), mine) (_, theirs) ->
                      let this =
                        method_of trait "equal" Read field.field_type
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
                    giving
                      (match (variant, mine) with
                      | Some variant, [] ->
                          node bool (Matches { value = Place other; pattern = is variant })
                      | _ ->
                          of_other other bool variant mine ~same:(each_equal mine)
                            ~different:(fun () -> node bool (Boolean false))))
            | "Hash", "hash" ->
                let hasher, hasher_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      (Core.Local { local; type_; origin }, type_)
                  | [] -> bug "`hash` takes a hasher"
                in
                let hasher_path =
                  match hasher_type with
                  | Named { path; _ } -> path
                  | _ -> bug "a hasher that is not a named type"
                in
                let changed : Core.argument =
                  Passed { mode = Mut; value = Place hasher; mark = None }
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
                                           (node (Types.builtin UInt64) (Integer (Z.of_int number)));
                                       mark = None;
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
                                   (method_of trait "hash" Read field.field_type
                                      [ read mine; changed ]
                                      unit)))
                            mine;
                      value = None;
                    })
            | "Ordered", "compare" -> (
                let other = other_place () in
                let ordering name = node result (Construct { variant = Some name; fields = [] }) in
                let declared variant fields =
                  Environment.in_declared_order database type_ ~variant
                    ~name:(fun ((field : Types.field), _) -> field.field_name)
                    fields
                in
                (* Compares field by field, in declaration order. The first
                   pair of fields that is not equal decides. *)
                let rec in_turn mine theirs =
                  match (mine, theirs) with
                  | [], _ | _, [] -> ordering "Equal"
                  | ((field : Types.field), mine) :: rest, (_, theirs) :: rest_of_theirs -> (
                      let compared =
                        method_of trait "compare" Read field.field_type
                          [ read mine; read theirs ]
                          result
                      in
                      match rest with
                      | [] -> compared
                      | rest ->
                          let decided = local () in
                          node result
                            (Match
                               {
                                 scrutinees = [ Value compared ];
                                 arms =
                                   [
                                     arm
                                       (pattern result (Variant { variant = "Equal"; fields = [] }))
                                       (giving (in_turn rest rest_of_theirs));
                                     arm
                                       (pattern result
                                          (Bind
                                             {
                                               local = decided;
                                               name = "decided";
                                               is_var = false;
                                               mode = Own;
                                             }))
                                       (giving
                                          (node result
                                             (Use
                                                (Local { local = decided; type_ = result; origin }))));
                                   ];
                               }))
                in
                let number = Types.builtin UInt32 in
                match variants with
                | None | Some [ _ ] ->
                    of_self result (fun variant _ mine ->
                        giving
                          (of_other other result variant mine
                             ~same:(fun theirs ->
                               in_turn (declared variant mine) (declared variant theirs))
                             ~different:(fun () -> ordering "Equal")))
                | Some variants ->
                    (* The index of the other value's variant, to compare
                       with the index of this value's variant when the two
                       differ. *)
                    let theirs = local () in
                    let numbered =
                      node number
                        (Match
                           {
                             scrutinees = [ Place other ];
                             arms =
                               List.mapi
                                 (fun index (variant, _) ->
                                   arm (is variant)
                                     (giving (node number (Integer (Z.of_int index)))))
                                 variants;
                           })
                    in
                    let by_number index =
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
                             then_ = giving (ordering "Less");
                             else_ = Some (giving (ordering "Greater"));
                           })
                    in
                    let compared =
                      of_self result (fun variant index mine ->
                          giving
                            (of_other other result variant mine
                               ~same:(fun theirs ->
                                 in_turn (declared variant mine) (declared variant theirs))
                               ~different:(fun () -> by_number index)))
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
                                 value = Value numbered;
                                 else_ = None;
                               });
                        ];
                    })
            | "Default", "default" ->
                giving
                  (node self_type
                     (Construct
                        {
                          variant = None;
                          fields =
                            List.map
                              (fun (field : Types.field) ->
                                ( field.field_name,
                                  Some
                                    (Core.Value
                                       (method_of trait "default" Static field.field_type []
                                          field.field_type)) ))
                              (record_fields ());
                        }))
            | "Serialize", "serialize" ->
                let sink, sink_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ ->
                      (Core.Local { local; type_; origin }, type_)
                  | [] -> bug "`serialize` takes a serializer"
                in
                let sink_argument : Core.argument =
                  Passed { mode = Mut; value = Place sink; mark = None }
                in
                let serializer = Well_known.path Serializer in
                let call name arguments =
                  statement
                    (Evaluate
                       (trait_call ~trait:serializer ~name ~receiver:Mut ~self_type:sink_type
                          ~evidence:Bound (sink_argument :: arguments) unit))
                in
                let serialized ((field : Types.field), place) =
                  [
                    call "field" [ text_argument field.field_name ];
                    statement
                      (Evaluate
                         (method_of trait "serialize" Read field.field_type
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
                      Environment.in_declared_order database type_ ~variant
                        ~name:(fun ((field : Types.field), _) -> field.field_name)
                        mine
                    in
                    {
                      statements = begin_ @ List.concat_map serialized mine @ [ call end_ [] ];
                      value = None;
                    })
            | "Deserialize", "deserialize" -> (
                let source, source_type =
                  match parameters with
                  | [ ({ local; type_; _ } : Core.parameter) ] ->
                      (Core.Local { local; type_; origin }, type_)
                  | _ -> bug "`deserialize` takes a deserializer"
                in
                let source_argument mode : Core.argument =
                  Passed { mode; value = Place source; mark = None }
                in
                let deserializer = Well_known.path Deserializer in
                let error_type =
                  match result with
                  | Named { arguments = [ _; Type error ]; _ } -> error
                  | _ -> bug "`deserialize` returns a `Result`"
                in
                let result_of ok = Types.named (Well_known.path Result) [ ok; error_type ] in
                let source_call name arguments type_ =
                  trait_call ~trait:deserializer ~name ~receiver:Mut ~self_type:source_type
                    ~evidence:Bound
                    (source_argument Mut :: arguments)
                    type_
                in
                let finish name = statement (Evaluate (source_call name [] unit)) in
                (* [call?]: the value of [call]'s [Ok], or a return of its
                   [Err]. *)
                let attempted ok call =
                  let value = local () and error = local () in
                  node ok
                    (Match
                       {
                         scrutinees = [ Value call ];
                         arms =
                           [
                             arm
                               (pattern (result_of ok)
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
                               (giving
                                  (node ok (Use (Local { local = value; type_ = ok; origin }))));
                             arm
                               (pattern (result_of ok)
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
                               (giving
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
                  attempted ok
                    (node (result_of ok)
                       (Call
                          {
                            callee =
                              Function
                                {
                                  path = Well_known.path function_;
                                  type_arguments =
                                    [ Types.Type field.field_type; Types.Type source_type ];
                                };
                            arguments = [ source_argument Mut; text_argument field.field_name ];
                            lends = None;
                            uses = Types.no_capabilities;
                          }))
                in
                let bind_local local name type_ ~is_var value =
                  statement
                    (Let
                       {
                         pattern = pattern type_ (Bind { local; name; is_var; mode = Own });
                         value = Value value;
                         else_ = None;
                       })
                in
                (* Reads the fields of a record or of a variant, then builds
                   the value. A field without a default is read before the
                   value is built, and one with a default after, into the
                   value that its default built. *)
                let fields_then_built variant (fields : Types.field list) end_ : Core.block =
                  let required, defaulted =
                    match variant with
                    | None ->
                        List.partition
                          (fun (field : Types.field) -> not field.field_has_default)
                          fields
                    | Some _ -> (fields, [])
                  in
                  let read = List.map (fun (field : Types.field) -> (field, local ())) required in
                  let built = local () in
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
                        let optional = Types.named (Well_known.path Option) [ field.field_type ] in
                        let present = local () in
                        statement
                          (Evaluate
                             (node unit
                                (Match
                                   {
                                     scrutinees =
                                       [ Value (read_field Deserialize_optional field optional) ];
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
                                                              bug "a variant's field with a default");
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
                      @ [ finish end_ ];
                    value =
                      Some
                        (node result
                           (Construct
                              {
                                variant = Some "Ok";
                                fields =
                                  [
                                    ("value", Some (Core.Value (node self_type (Use built_place))));
                                  ];
                              }));
                  }
                in
                let begun name =
                  statement (Evaluate (attempted unit (source_call name [] (result_of unit))))
                in
                match variants with
                | None ->
                    let body = fields_then_built None (record_fields ()) "end_record" in
                    { body with statements = begun "begin_record" :: body.statements }
                | Some variants ->
                    let string_type = Types.named (Well_known.path String) [] in
                    let name = local () in
                    let name_place : Core.place =
                      Local { local = name; type_ = string_type; origin }
                    in
                    let equal =
                      let reference : Types.trait_reference =
                        { trait = Well_known.path Equal; trait_arguments = []; associated = [] }
                      in
                      match Impls.implements database ~bounds string_type reference with
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
                      | _ -> bug "`String` has no `Equal`"
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
                                                                 Well_known.path Unknown_variant;
                                                               type_arguments =
                                                                 [ Types.Type source_type ];
                                                             };
                                                         arguments =
                                                           [ source_argument Read; read name_place ];
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
                            (attempted string_type
                               (source_call "variant" [] (result_of string_type)));
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
                                             (Equal_to
                                                { value = node string_type (String variant); equal }))
                                          (fields_then_built (Some variant) fields "end_variant"))
                                      variants
                                    @ [ arm (pattern string_type Wildcard) (giving unknown) ];
                                }));
                    })
            | _ -> bug "`%s` cannot be derived" (Path.show path)
          in
          Some
            {
              definition =
                Function
                  {
                    parameters;
                    contract = { requires = []; ensures = []; decreases = []; costs = [] };
                    body = Some body;
                  };
            }
      | _ -> None)
  | _ -> None

(* The core form of a method of a derived [impl], by the method's path. It
   is generated once, however many instances of the method are compiled. *)
let core = Query.query ~name:"derived" ~phase:Phases.bodies ~show:Path.show form
