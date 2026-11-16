let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

type entered =
  [ `Default of Path.t * string option * string | `Invariant of Path.t * Z.t | `Requires of Path.t ]

module Entered_table = Hashtbl.Make (Structural_key.Make (struct
  type t = entered
end))

type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

let find_head (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

let rec list_traits_with_required interface (trait : Path.t) =
  match Interface.Definition.read_interface interface trait with
  | Some (Interface.Environment.Trait_interface trait_interface) ->
      trait
      :: List.concat_map
           (fun (required : Types.trait_reference) ->
             list_traits_with_required interface required.trait)
           trait_interface.requires
  | _ -> [ trait ]

let list_written_methods (names : Resolve.Names.lookups) impl =
  match names.key impl with
  | Some impl_key ->
      List.map (fun (member : Resolve.Names.key) -> member.path) (names.contained impl_key)
  | None -> []

let list_impl_methods (interface : Interface.Lookups.t) impl =
  match Interface.Definition.read_impl_interface interface impl with
  | Some implementation -> (
      let trait = implementation.implements.trait in
      match Interface.Definition.read_trait_interface interface trait with
      | Some trait_interface ->
          List.map
            (fun (declared : Types.trait_method) ->
              let name = declared.method_name in
              match
                Types.find_implementing_receiver ~is_capability:trait_interface.is_capability
                  implementation declared
              with
              | Some receiver -> Path.Method { owner = impl; name; receiver }
              | None -> Path.Method { owner = trait; name; receiver = declared.method_receiver })
            trait_interface.methods
      | None -> list_written_methods interface.names impl)
  | None -> list_written_methods interface.names impl

let writes (lookups : lookups) impl method_ =
  List.exists (Path.equal method_) (list_written_methods lookups.interface.names impl)

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
  | Function { path; type_arguments } -> (
      match Interface.Impls.read_signature interface path with
      | Some (signature : Types.signature) ->
          let rec pairs generics arguments =
            match (generics, arguments) with
            | (generic : Types.generic) :: generics, Types.Type ty :: arguments ->
                (generic, ty) :: pairs generics arguments
            | _ :: generics, _ :: arguments -> pairs generics arguments
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
              | Value_generic | Capability_generic -> [])
            (pairs signature.generics type_arguments)
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
  let uses_impls impls = add (List.concat_map (list_impl_methods lookups.interface) impls) in
  let impls_for = list_impls_for lookups.interface package in
  let callee (called : Tree.callee) =
    match called with
    | Function { path; _ } ->
        add [ path ];
        uses_impls (list_impls_used lookups.interface package called)
    | Trait_method { evidence = Impl { impl; _ }; trait; name; receiver; _ } ->
        let own = Path.Method { owner = impl; name; receiver } in
        add
          [
            (if writes lookups impl own then own
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
                  if writes lookups impl method_ then Some method_ else None)
                (impls_for [ trait.trait ] (Types.make_builtin builtin)))
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
  let rec statement (locals : Tree.local_info array) (statement : Tree.statement) =
    match statement.kind with
    | Basic (Call { call; _ } | Template { call; _ }) ->
        callee call.callee;
        invariant_checked call
    | Basic (Lend { call; _ }) -> (
        callee call.callee;
        invariant_checked call;
        match call.callee with
        | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ }
          when Parts.is_index_call call.callee ->
            requires_checked (Path.Method { owner = impl; name; receiver })
        | _ -> ())
    | Basic (Slice { call; _ }) -> (
        callee call.callee;
        invariant_checked call;
        match call.callee with Function { path; _ } -> requires_checked path | _ -> ())
    | For { iteration = Pull { next; _ }; _ } -> callee next
    | Basic (Assign { value = Function_value { path; _ }; _ }) -> add [ path ]
    | Basic (Assign { value = To_any { value; trait; _ }; _ }) ->
        uses_impls
          (impls_for
             (list_traits_with_required lookups.interface trait.trait)
             (Walk.extract_operand_type value))
    | Basic
        (Assign
           {
             target = { root = Local local; projections = [] };
             value = Construct { variant; fields };
             _;
           }) -> (
        match find_head locals.(local).type_ with
        | Some type_ ->
            let omitted =
              List.filter_map
                (fun (field, value) -> if Option.is_none value then Some field else None)
                fields
            in
            if omitted <> [] then field_defaults type_ variant omitted
        | None -> ())
    | Basic (Assign { value = Construct _; _ }) -> raise_bug "a construction outside a temporary"
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
    | For { iteration = Range _; _ }
    | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo)
    | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ ->
        ()
  and field_defaults type_ variant omitted =
    match Parts.read_defaults lookups.mir type_ with
    | Some { form = Field_defaults defaults; _ } ->
        List.iter
          (fun (default : Tree.t Tree.field_default) ->
            if
              default.variant = variant && List.mem default.field omitted
              && enters (`Default (type_, variant, default.field))
            then Walk.iter_code_with_locals statement default.value)
          defaults
    | Some { form = Parameter_defaults _; _ } | None -> ()
  and requires_checked path =
    if may_panic && enters (`Requires path) then
      List.iter
        (fun (requirement : Tree.requirement) ->
          Walk.iter_formula_with_locals statement requirement.clause)
        (Parts.list_checked_requires lookups.mir path)
  and invariant_checked (call : Tree.call) =
    match (call.callee, call.arguments) with
    | ( Intrinsic { operation = Holds_invariant; type_arguments = [ Type checked ] },
        [ _; Passed { value = Constant { value = Integer index; _ }; _ } ] ) -> (
        match
          (find_head checked, Option.bind (find_head checked) (Parts.read_type_clauses lookups.mir))
        with
        | Some type_, Some { form = clauses; _ } -> (
            match List.nth_opt clauses.invariants (Z.to_int index) with
            | Some { clause; is_executable = true; _ } when enters (`Invariant (type_, index)) ->
                Walk.iter_formula_with_locals statement clause
            | Some _ | None -> ())
        | _ -> ())
    | _ -> ()
  in
  Walk.iter_code_with_locals statement code;
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

let list_implementations (lookups : lookups) ~viewer (path : Path.t) =
  match path with
  | Method { owner; name; receiver } -> (
      match Interface.Definition.read_interface lookups.interface owner with
      | Some (Interface.Environment.Trait_interface _) ->
          List.concat_map
            (fun package ->
              List.filter_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if writes lookups impl method_ then Some method_ else None)
                (Interface.Impls.list_impls_of_trait lookups.interface ~trait:owner package))
            (viewer :: Resolve.Names.list_transitive_dependencies lookups.interface.names viewer)
      | _ -> [])
  | _ -> []
