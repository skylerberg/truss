type entered =
  [ `Default of Path.t * string option * string | `Invariant of Path.t * Z.t | `Requires of Path.t ]

module Entered_table = Hashtbl.Make (Structural_key.Make (struct
  type t = entered
end))

type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

let find_head (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

let rec list_traits_with_required interface (trait : Path.t) =
  trait
  :: List.concat_map
       (fun (required : Types.trait_reference) ->
         list_traits_with_required interface required.trait)
       (Interface.Definition.read_trait_interface interface trait).requires

let list_written_methods (names : Resolve.Names.lookups) impl =
  match names.find_key impl with
  | Some impl_key ->
      List.map (fun (member : Resolve.Names.key) -> member.path) (names.list_contained impl_key)
  | None -> []

let defines (names : Resolve.Names.lookups) (impl : Path.t) (method_ : Path.t) =
  match (impl, method_) with
  | Derived { trait; _ }, Method { name; _ } -> Infer.derives trait name
  | _ -> List.exists (Path.equal method_) (list_written_methods names impl)

let list_impl_methods (interface : Interface.Lookups.t) impl =
  let implementation = Interface.Definition.read_impl_interface interface impl in
  let trait = implementation.implements.trait in
  let trait_interface = Interface.Definition.read_trait_interface interface trait in
  List.map
    (fun (declared : Types.trait_method) ->
      let name = declared.method_name in
      let inherited = Path.Method { owner = trait; name; receiver = declared.method_receiver } in
      match Types.find_implementing_receiver trait_interface implementation declared with
      | Some receiver ->
          let own = Path.Method { owner = impl; name; receiver } in
          if defines interface.names impl own then own else inherited
      | None -> inherited)
    trait_interface.methods

let list_impls_for interface package traits ty =
  match find_head ty with
  | Some head ->
      List.concat_map
        (fun trait ->
          Interface.Impls.list_impls_of_trait_for_type interface ~trait ~type_:head package)
        (List.sort_uniq Path.compare traits)
  | None -> []

let list_impls_used interface package (callee : _ Core.target) =
  match callee with
  | Function { path; instantiation = { type_arguments; _ } } -> (
      match Interface.Impls.read_signature interface path with
      | Some (signature : Types.signature) ->
          let rec pair_generics generics arguments =
            match (generics, arguments) with
            | (generic : Types.generic) :: generics, Types.Type ty :: arguments ->
                (generic, ty) :: pair_generics generics arguments
            | _ :: generics, _ :: arguments -> pair_generics generics arguments
            | _ -> []
          in
          List.concat_map
            (fun ((generic : Types.generic), ty) ->
              match generic.kind with
              | Type_generic bounds ->
                  list_impls_for interface package
                    (List.concat_map
                       (fun (bound : Types.trait_reference) ->
                         list_traits_with_required interface bound.trait)
                       bounds)
                    ty
              | Value_generic -> [])
            (pair_generics signature.generics type_arguments)
      | None -> [])
  | _ -> []

let is_integer_trait owner =
  Well_known.is Fixed_width_integer owner
  || Well_known.is Signed_integer owner
  || Well_known.is Unsigned_integer owner

let integer_types =
  List.filter (fun builtin -> Types.is_integer_type (Types.make_builtin builtin)) Intrinsic.builtins

let is_dispatched (called : _ Core.target) =
  match called with
  | Trait_method { evidence = Dynamic; _ } -> true
  | Trait_method
      { evidence = Bound; self_type = Parameter self | Projection { base = Parameter self; _ }; _ }
    when Types.is_self_parameter self ->
      true
  | _ -> false

let list_edges (lookups : lookups) ~package ~may_panic (code : Tree.t) =
  let callees = ref [] in
  let add paths = callees := List.rev_append paths !callees in
  let add_impl_uses impls = add (List.concat_map (list_impl_methods lookups.interface) impls) in
  let list_package_impls_for = list_impls_for lookups.interface package in
  let add_callee (callee : Tree.callee) =
    let called = callee.target in
    match called with
    | Function { path; _ } ->
        add [ path ];
        add_impl_uses (list_impls_used lookups.interface package called)
    | Trait_method { evidence = Impl { impl; _ }; trait; name; receiver; _ } ->
        let own = Path.Method { owner = impl; name; receiver } in
        add
          [
            (if defines lookups.interface.names impl own then own
             else Path.Method { owner = trait.trait; name; receiver });
          ]
    | Trait_method
        { trait; name; receiver; evidence = Bound; self_type = Parameter ({ owner; _ } as self); _ }
      when Types.is_self_parameter self && is_integer_trait owner -> (
        let own =
          List.concat_map
            (fun builtin ->
              List.filter_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if defines lookups.interface.names impl method_ then Some method_ else None)
                (list_package_impls_for [ trait.trait ] (Types.make_builtin builtin)))
            integer_types
        in
        match own with
        | [] -> add [ Path.Method { owner = trait.trait; name; receiver } ]
        | own -> add own)
    | Trait_method { trait; name; receiver; _ } when is_dispatched called ->
        add [ Path.Method { owner = trait.trait; name; receiver } ]
    | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> ()
  in
  let entered = Entered_table.create 4 in
  let enters code =
    if Entered_table.mem entered code then false
    else (
      Entered_table.replace entered code ();
      true)
  in
  let rec visit_statement (statement : Tree.statement) =
    Option.iter add_callee (Walk.find_callee statement);
    match statement.kind with
    | Basic (Call { call; _ } | Lend { call; _ }) ->
        add_invariant_check call;
        add_index_requires_check call
    | Basic (Template { call; _ }) -> add_invariant_check call
    | Basic (Slice { call; _ }) -> (
        add_invariant_check call;
        match call.callee.target with Function { path; _ } -> add_requires_check path | _ -> ())
    | Basic (Assign { value = Function_value { path; _ }; _ }) -> add [ path ]
    | Basic (Assign { value = To_any { value; trait; _ }; _ }) ->
        add_impl_uses
          (list_package_impls_for
             (list_traits_with_required lookups.interface trait.trait)
             (Walk.extract_operand_type value))
    | Basic (Assign { value = Construct { variant; fields; type_ }; _ }) -> (
        match find_head type_ with
        | Some head ->
            let omitted =
              List.filter_map
                (fun (field, value) -> if Option.is_none value then Some field else None)
                fields
            in
            if omitted <> [] then visit_field_defaults head variant omitted
        | None -> ())
    | Basic (Provide { provided; _ }) ->
        List.iter
          (fun (implementation : Tree.provided) ->
            List.iter
              (fun (provided : Core.provided) ->
                add (list_written_methods lookups.interface.names provided.impl))
              implementation.provides)
          provided
    | Basic
        ( Assign
            {
              value =
                ( Operand _ | Operation _ | Compare _ | Not _ | Array _ | Is_variant _ | Convert _
                | Copy _ | Lambda _ | Value_parameter _ | Specification _ );
              _;
            }
        | Live _ | Dead _ | Assert _ | Echo _ | Provide_end | Loan_start _ | Loan_end _
        | Ghost_assert _ | Matched _ | Proof _ )
    | For _
    | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo)
    | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ ->
        ()
  and visit_field_defaults type_ variant omitted =
    match Parts.read_defaults lookups.mir type_ with
    | Some { form = Field_defaults defaults; _ } ->
        List.iter
          (fun (default : Tree.t Tree.field_default) ->
            if
              default.variant = variant && List.mem default.field omitted
              && enters (`Default (type_, variant, default.field))
            then Walk.iter_code visit_statement default.value)
          defaults
    | Some { form = Parameter_defaults _; _ } | None -> ()
  and add_index_requires_check (call : Tree.call) =
    match call.callee.target with
    | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ }
      when Parts.is_index_call call.callee.target ->
        add_requires_check (Path.Method { owner = impl; name; receiver })
    | _ -> ()
  and add_requires_check path =
    if may_panic && enters (`Requires path) then
      Option.iter
        (fun ({ form = requires; _ } : Tree.requirement list Parts.sourced) ->
          List.iter
            (fun (requirement : Tree.requirement) ->
              Walk.iter_formula visit_statement requirement.clause)
            requires)
        (Parts.find_checked_requires lookups.mir path)
  and add_invariant_check (call : Tree.call) =
    match (call.callee.target, call.arguments) with
    | ( Intrinsic { operation = Runtime Holds_invariant; type_arguments = [ Type checked ] },
        [ _; Passed { value = Constant { value = Integer index; _ }; _ } ] ) -> (
        match
          (find_head checked, Option.bind (find_head checked) (Parts.read_type_clauses lookups.mir))
        with
        | Some type_, Some { form = clauses; _ } -> (
            match List.nth_opt clauses.invariants (Z.to_int index) with
            | Some { clause; is_executable = true; _ } when enters (`Invariant (type_, index)) ->
                Walk.iter_formula visit_statement clause
            | Some _ | None -> ())
        | _ -> ())
    | _ -> ()
  in
  Walk.iter_code visit_statement code;
  List.rev !callees

let list_path_edges (lookups : lookups) path =
  let defaults =
    match Parts.read_defaults lookups.mir path with
    | Some { form = Parameter_defaults defaults; _ } -> List.map snd defaults
    | Some { form = Field_defaults _; _ } | None -> []
  in
  let code =
    match Parts.read_body_part lookups.mir path with
    | Some { form = Body code | Initializer code; _ } -> [ code.tree ]
    | Some { form = No_code; _ } | None -> []
  in
  let may_panic =
    match Interface.Impls.read_signature lookups.interface path with
    | Some (signature : Types.signature) -> Types.may_panic signature.uses
    | None -> false
  in
  List.sort_uniq Path.compare
    (List.concat_map
       (list_edges lookups ~package:(Path.locate_package path) ~may_panic)
       (code @ defaults))

let list_implementations (lookups : lookups) ~calling_package (path : Path.t) =
  match path with
  | Method { owner; name; receiver } -> (
      match Interface.Definition.find_interface lookups.interface owner with
      | Some (Interface.Environment.Trait_interface _) ->
          List.concat_map
            (fun package ->
              List.filter_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if defines lookups.interface.names impl method_ then Some method_ else None)
                (Interface.Impls.list_impls_of_trait lookups.interface ~trait:owner package))
            (calling_package
            :: Resolve.Names.list_transitive_dependencies lookups.interface.names calling_package)
      | _ -> [])
  | _ -> []
