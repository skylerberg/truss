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

let form database (path : Path.t) : Core.t option =
  match path with
  | Method { owner = Derived { type_; trait } as impl; name; receiver = _ } when gives trait name
    -> (
      match
        ( Impls.impl_interface database impl,
          Query.demand database Environment.type_interface type_,
          Impls.signature database path )
      with
      (* A type still to be written has nothing to derive from yet. *)
      | _, Some { shape = Todo_type; _ }, _ -> None
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
            Synthetic local
          in
          (* The code has no text of its own: every node comes from where the
             type is declared. *)
          let origin = 0 in
          let node type_ kind : Core.expression = { id = id (); origin; type_; kind } in
          let pattern type_ kind : Core.pattern = { id = id (); origin; type_; kind } in
          let statement kind : Core.statement = { id = id (); origin; kind } in
          let giving value : Core.block =
            { statements = []; value = Some value; diverges = false }
          in
          let arm found body : Core.arm = { patterns = [ found ]; guard = None; body; origin } in
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
                      callback_contract = None;
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
                    callback_contract = None;
                  })
                signature.parameters
          in
          let given () : Core.place =
            match List.filter (fun (p : Core.parameter) -> p.local <> Self) parameters with
            | [ parameter ] -> Local { local = parameter.local; type_ = parameter.type_ }
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
                 })
          in
          let read place : Core.argument = Passed { mode = Read; value = Place place } in
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
          let alone = match variants with Some [ _ ] -> true | _ -> false in
          let record_fields () =
            match shape with Record fields -> fields | _ -> bug "a record's fields of a sum type"
          in
          (* A record's fields, each where it is in the record at [base]. *)
          let record_parts base =
            List.map
              (fun (field : T.field) ->
                (field, Core.Field { base; field = field.field_name; type_ = field.field_type }))
              (record_fields ())
          in
          (* A variant's fields are reached by a pattern that binds each,
             lent from the value matched. *)
          let bound named (fields : T.field list) =
            List.map (fun (field : T.field) -> (field, local (), named field.field_name)) fields
          in
          let binding variant bound : Core.pattern =
            pattern self_type
              (Variant
                 {
                   variant;
                   fields =
                     List.map
                       (fun ((field : T.field), local, name) ->
                         ( field.field_name,
                           pattern field.field_type
                             (Bind { local; name; mutable_ = false; mode = Read }) ))
                       bound;
                 })
          in
          let parts bound =
            List.map
              (fun ((field : T.field), local, _) ->
                (field, Core.Local { local; type_ = field.field_type }))
              bound
          in
          let self_place : Core.place = Local { local = Self; type_ = self_type } in
          let is variant : Core.pattern = pattern self_type (Variant { variant; fields = [] }) in
          (* What [each] gives of the parts of [self]: of a record's fields,
             or of the fields of the variant it is, by an arm for each. *)
          let of_self type_
              (each : string option -> int -> (T.field * Core.place) list -> Core.block) =
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
                          guards_exhaustive = false;
                        }))
          in
          (* Matches [other]. If [other] is the same variant as [self], the
             result is [same] applied to the fields of [other]. If it is a
             different variant, the result is [different ()]. *)
          let of_other other type_ variant (mine : (T.field * Core.place) list) ~same ~different =
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
                       guards_exhaustive = false;
                     })
          in
          let bool = T.bool and unit = T.unit in
          let trait_name = match trait with Top { name; _ } -> name | _ -> Path.show trait in
          let body : Core.block =
            match (trait_name, name) with
            | "Equal", "equal" ->
                let other = given () in
                let each_equal mine theirs =
                  List.fold_left2
                    (fun so_far ((field : T.field), mine) (_, theirs) ->
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
                      (Core.Local { local; type_ }, type_)
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
                             })))
                in
                of_self unit (fun variant index mine ->
                    {
                      statements =
                        (if variant = None then [] else [ write index ])
                        @ List.map
                            (fun ((field : T.field), mine) ->
                              statement
                                (Evaluate
                                   (method_of trait "hash" Read field.field_type
                                      [ read mine; changed ]
                                      unit)))
                            mine;
                      value = None;
                      diverges = false;
                    })
            | "Ordered", "compare" -> (
                let other = given () in
                let ordering name = node result (Construct { variant = Some name; fields = [] }) in
                (* Field by field: the first that is not equal decides. *)
                let rec in_turn mine theirs =
                  match (mine, theirs) with
                  | [], _ | _, [] -> ordering "Equal"
                  | ((field : T.field), mine) :: rest, (_, theirs) :: rest_of_theirs -> (
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
                                               mutable_ = false;
                                               mode = Own;
                                             }))
                                       (giving
                                          (node result
                                             (Use (Local { local = decided; type_ = result }))));
                                   ];
                                 guards_exhaustive = false;
                               }))
                in
                let number = T.builtin UInt32 in
                match variants with
                | None | Some [ _ ] ->
                    of_self result (fun variant _ mine ->
                        giving
                          (of_other other result variant mine ~same:(in_turn mine)
                             ~different:(fun () -> ordering "Equal")))
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
                                 (fun index (variant, _) ->
                                   arm (is variant)
                                     (giving (node number (Integer (Z.of_int index)))))
                                 variants;
                             guards_exhaustive = false;
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
                                        node number (Use (Local { local = theirs; type_ = number }));
                                    });
                             then_ = giving (ordering "Less");
                             else_ = Some (giving (ordering "Greater"));
                           })
                    in
                    let compared =
                      of_self result (fun variant index mine ->
                          giving
                            (of_other other result variant mine ~same:(in_turn mine)
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
                                          mutable_ = false;
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
              definition =
                Function
                  {
                    parameters;
                    contract = { requires = []; ensures = []; decreases = []; costs = [] };
                    body = Some body;
                  };
              node_count = !nodes;
              synthetic_local_count = !made;
            }
      | _ -> None)
  | _ -> None

(* The form of a method a derived [impl] gives, by the method's path, made
   once however many of its instances are compiled. *)
let core = Query.query ~name:"derived" ~phase:Bodies ~show:Path.show form
