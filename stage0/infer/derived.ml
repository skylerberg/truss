(* The core form of the methods a derived [impl] gives: what [derives]
   means, as the body each would have if it were written. A type's [equal]
   compares its variant and then each field; its [hash] writes its variant's
   number and then hashes each field; its [compare] orders by variant, in
   the order they are declared, and then by each field in turn; and its
   [default] is each field's. A method the trait gives a body, such as
   [not_equal], is the trait's, and has no form here. *)

module T = Types
module Impls = Interface.Impls
module Environment = Interface.Environment

let bug format = Compiler_bug.bug ~stage:"Infer" format

let gives (trait : Path.t) name =
  match trait with
  | Top { module_ = { package = "standard"; modules = [ "core" ] }; name = trait } ->
      List.mem (trait, name)
        [ ("Equal", "equal"); ("Hash", "hash"); ("Ordered", "compare"); ("Default", "default") ]
  | _ -> false

let core database (path : Path.t) : Core.t option =
  match path with
  | Method { owner = Derived { type_; trait } as impl; name; receiver = _ } when gives trait name
    -> (
      match
        ( Impls.impl_interface database impl,
          Query.demand database Environment.type_interface type_,
          Impls.signature database path )
      with
      | Some interface, Some { shape; _ }, Some signature ->
          let nodes = ref 0 and made = ref 0 in
          let id () =
            let id = !nodes in
            incr nodes;
            id
          in
          let local () : Core.local =
            let local = !made in
            incr made;
            Made local
          in
          (* The code has no text of its own: every node comes from where the
             type is declared. *)
          let origin = 0 in
          let node type_ kind : Core.expression = { id = id (); origin; type_; kind } in
          let pattern type_ kind : Core.pattern = { id = id (); origin; type_; kind } in
          let statement kind : Core.statement = { id = id (); origin; kind } in
          let giving value : Core.block = { statements = []; value = Some value; ends = true } in
          let self_type = interface.for_type in
          let bounds (parameter : T.parameter) =
            List.concat_map
              (fun (generic : T.generic) ->
                match generic.kind with
                | Type_generic bounds when generic.generic = parameter -> bounds
                | _ -> [])
              interface.impl_generics
          in
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
                      accepts = None;
                    };
                  ]
              | Some (Static, _) | None -> [])
            @ List.map
                (fun (info : T.parameter_info) : Core.parameter ->
                  {
                    local = local ();
                    name = info.name;
                    mode = info.mode;
                    type_ = info.type_;
                    default = None;
                    accepts = None;
                  })
                signature.parameters
          in
          let given () : Core.place =
            match List.filter (fun (p : Core.parameter) -> p.local <> Self) parameters with
            | [ parameter ] -> Local parameter.local
            | _ -> bug "`%s` takes one value beside its own" (Path.show path)
          in
          (* A method of [wanted] on a value of [of_type], by the [impl] the
             type has of it, or by a bound where the type is a parameter. *)
          let method_of (wanted : Path.t) name (receiver : Path.receiver) of_type arguments type_ =
            let reference : T.trait_reference =
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
                         type_arguments = [];
                         evidence;
                       };
                   arguments;
                   lends = None;
                   uses = [];
                   capability_arguments = [];
                 })
          in
          let read place : Core.argument = Passed { mode = Read; value = Place place } in
          let field_of base variant (field : T.field) : Core.place =
            Field { base; variant; field = field.field_name; type_ = field.field_type }
          in
          let variants =
            match shape with
            | Sum variants ->
                Some
                  (List.map
                     (fun (variant : T.variant) ->
                       (variant.variant_name, Option.value variant.fields ~default:[]))
                     variants)
            | Record _ -> None
            | Todo_type | Builtin_type _ | Error_shape _ ->
                bug "`%s` is derived for a type with no fields" (Path.show trait)
          in
          let record_fields () =
            match shape with Record fields -> fields | _ -> bug "a record's fields of a sum type"
          in
          let is variant : Core.pattern = pattern self_type (Variant { variant; fields = [] }) in
          (* One arm for each variant of the value at [place], or [each] of a
             record's fields alone. *)
          let by_variant type_ place (each : string option -> int -> T.field list -> Core.block) =
            match variants with
            | None -> each None 0 (record_fields ())
            | Some variants ->
                giving
                  (node type_
                     (Match
                        {
                          scrutinees = [ Place place ];
                          arms =
                            List.mapi
                              (fun index (variant, fields) : Core.arm ->
                                {
                                  patterns = [ is variant ];
                                  guard = None;
                                  body = each (Some variant) index fields;
                                  origin;
                                })
                              variants;
                          guards_cover = false;
                        }))
          in
          let bool = T.bool and unit = T.unit in
          let trait_name = match trait with Top { name; _ } -> name | _ -> Path.show trait in
          let body : Core.block =
            match (trait_name, name) with
            | "Equal", "equal" ->
                let other = given () in
                by_variant bool (Local Self) (fun variant _ fields ->
                    let equal (field : T.field) =
                      method_of trait "equal" Read field.field_type
                        [
                          read (field_of (Local Self) variant field);
                          read (field_of other variant field);
                        ]
                        bool
                    in
                    let same_variant =
                      Option.map
                        (fun variant ->
                          node bool (Matches { value = Place other; pattern = is variant }))
                        variant
                    in
                    let all =
                      List.fold_left
                        (fun so_far field ->
                          let this = equal field in
                          match so_far with
                          | None -> Some this
                          | Some so_far -> Some (node bool (Both (so_far, this))))
                        same_variant fields
                    in
                    giving (match all with Some all -> all | None -> node bool (Boolean true)))
            | "Hash", "hash" ->
                let hasher, hasher_type =
                  match List.rev parameters with
                  | ({ local; type_; _ } : Core.parameter) :: _ -> (Core.Local local, type_)
                  | [] -> bug "`hash` takes a hasher"
                in
                let hasher_path =
                  match hasher_type with
                  | Named { path; _ } -> path
                  | _ -> bug "a hasher that is not a named type"
                in
                let changed : Core.argument = Passed { mode = Mut; value = Place hasher } in
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
                                         Value (node (T.builtin UInt64) (Integer (Z.of_int number)));
                                     };
                                 ];
                               lends = None;
                               uses = [];
                               capability_arguments = [];
                             })))
                in
                by_variant unit (Local Self) (fun variant index fields ->
                    {
                      statements =
                        (if variant = None then [] else [ write index ])
                        @ List.map
                            (fun (field : T.field) ->
                              statement
                                (Evaluate
                                   (method_of trait "hash" Read field.field_type
                                      [ read (field_of (Local Self) variant field); changed ]
                                      unit)))
                            fields;
                      value = None;
                      ends = true;
                    })
            | "Ordered", "compare" -> (
                let other = given () in
                let ordering name = node result (Construct { variant = Some name; fields = [] }) in
                (* Field by field: the first that is not equal decides. *)
                let rec by_fields variant (fields : T.field list) =
                  match fields with
                  | [] -> ordering "Equal"
                  | field :: rest -> (
                      let compared =
                        method_of trait "compare" Read field.field_type
                          [
                            read (field_of (Local Self) variant field);
                            read (field_of other variant field);
                          ]
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
                                     {
                                       patterns =
                                         [
                                           pattern result
                                             (Variant { variant = "Equal"; fields = [] });
                                         ];
                                       guard = None;
                                       body = giving (by_fields variant rest);
                                       origin;
                                     };
                                     {
                                       patterns =
                                         [
                                           pattern result
                                             (Bind
                                                {
                                                  local = decided;
                                                  name = "decided";
                                                  mutable_ = false;
                                                  mode = Own;
                                                });
                                         ];
                                       guard = None;
                                       body = giving (node result (Use (Local decided)));
                                       origin;
                                     };
                                   ];
                                 guards_cover = false;
                               }))
                in
                let number = T.builtin UInt32 in
                match variants with
                | None -> giving (by_fields None (record_fields ()))
                | Some variants ->
                    (* The other's variant as a number, which this one's is
                       compared with when the two differ. *)
                    let theirs = local () in
                    let numbered =
                      node number
                        (Match
                           {
                             scrutinees = [ Place other ];
                             arms =
                               List.mapi
                                 (fun index (variant, _) : Core.arm ->
                                   {
                                     patterns = [ is variant ];
                                     guard = None;
                                     body = giving (node number (Integer (Z.of_int index)));
                                     origin;
                                   })
                                 variants;
                             guards_cover = false;
                           })
                    in
                    let arm index (variant, fields) : Core.arm =
                      let same =
                        node bool (Matches { value = Place other; pattern = is variant })
                      in
                      let before =
                        node bool
                          (Compare
                             {
                               comparison = Less;
                               left = node number (Integer (Z.of_int index));
                               right = node number (Use (Local theirs));
                             })
                      in
                      let by_number =
                        node result
                          (If
                             {
                               condition = before;
                               then_ = giving (ordering "Less");
                               else_ = Some (giving (ordering "Greater"));
                             })
                      in
                      {
                        patterns = [ is variant ];
                        guard = None;
                        body =
                          giving
                            (node result
                               (If
                                  {
                                    condition = same;
                                    then_ = giving (by_fields (Some variant) fields);
                                    else_ = Some (giving by_number);
                                  }));
                        origin;
                      }
                    in
                    {
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
                                          mutable_ = false;
                                          mode = Own;
                                        });
                                 value = Value numbered;
                                 otherwise = None;
                               });
                        ];
                      value =
                        Some
                          (node result
                             (Match
                                {
                                  scrutinees = [ Place (Local Self) ];
                                  arms = List.mapi arm variants;
                                  guards_cover = false;
                                }));
                      ends = true;
                    })
            | "Default", "default" ->
                giving
                  (node self_type
                     (Construct
                        {
                          variant = None;
                          fields =
                            List.map
                              (fun (field : T.field) ->
                                ( field.field_name,
                                  Some
                                    (method_of trait "default" Static field.field_type []
                                       field.field_type) ))
                              (record_fields ());
                        }))
            | _ -> bug "`%s` cannot be derived" (Path.show path)
          in
          Some
            {
              parts =
                Function
                  {
                    parameters;
                    contract = { requires = []; ensures = []; decreases = []; costs = [] };
                    body = Some body;
                  };
              nodes = !nodes;
              made = !made;
            }
      | _ -> None)
  | _ -> None
