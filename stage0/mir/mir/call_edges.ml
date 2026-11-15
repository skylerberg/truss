module Names = Resolve.Names

type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

let head_of (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

let rec traits_with_required interface (trait : Path.t) =
  match Interface.Definition.interface interface trait with
  | Some (Interface.Environment.Trait_interface trait_interface) ->
      trait
      :: List.concat_map
           (fun (required : Types.trait_reference) -> traits_with_required interface required.trait)
           trait_interface.requires
  | _ -> [ trait ]

let written_methods (names : Names.lookups) impl =
  match names.key impl with
  | Some impl_key -> List.map (fun (member : Names.key) -> member.path) (names.contained impl_key)
  | None -> []

let impl_methods (interface : Interface.Lookups.t) impl =
  let written = written_methods interface.names impl in
  match
    Option.bind (Interface.Impls.impl_interface interface impl)
      (fun (implemented : Types.impl_interface) -> interface.names.key implemented.implements.trait)
  with
  | Some trait_key ->
      List.filter_map
        (fun (member : Names.key) ->
          match member.path with
          | Method { name; receiver; _ } as trait_method ->
              let own = Path.Method { owner = impl; name; receiver } in
              Some (if List.exists (Path.equal own) written then own else trait_method)
          | _ -> None)
        (interface.names.contained trait_key)
  | None -> written

let writes (lookups : lookups) impl method_ =
  List.exists (Path.equal method_) (written_methods lookups.interface.names impl)

let impls_for interface package traits ty =
  match head_of ty with
  | Some head ->
      List.concat_map
        (fun trait -> Interface.Impls.impls_in interface ~trait ~type_:head package)
        (List.sort_uniq Path.compare traits)
  | None -> []

let impls_used interface package (callee : _ Core.target) =
  match callee with
  | Function { path; type_arguments } -> (
      match Interface.Impls.signature interface path with
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
                  impls_for interface package
                    (List.concat_map
                       (fun (bound : Types.trait_reference) ->
                         traits_with_required interface bound.trait)
                       bounds)
                    ty
              | Value_generic | Capability_generic -> [])
            (pairs signature.generics type_arguments)
      | None -> [])
  | _ -> []

let integer_trait owner =
  Well_known.is Fixed_width_integer owner
  || Well_known.is Signed_integer owner
  || Well_known.is Unsigned_integer owner

let integer_types =
  List.filter (fun builtin -> Types.is_integer_type (Types.builtin builtin)) Intrinsic.builtins

let dispatched (called : _ Core.target) =
  match called with
  | Trait_method { evidence = Dynamic; _ } -> true
  | Trait_method
      {
        evidence = Bound;
        self_type =
          Parameter { name = "Self"; _ } | Projection { base = Parameter { name = "Self"; _ }; _ };
        _;
      } ->
      true
  | _ -> false

let edges (lookups : lookups) ~package (code : Tree.t) =
  let callees = ref [] in
  let add paths = callees := List.rev_append paths !callees in
  let uses_impls impls = add (List.concat_map (impl_methods lookups.interface) impls) in
  let impls_for = impls_for lookups.interface package in
  let callee (called : Tree.callee) =
    match called with
    | Function { path; _ } ->
        add [ path ];
        uses_impls (impls_used lookups.interface package called)
    | Trait_method { evidence = Impl { impl; _ }; trait; name; receiver; _ } ->
        let own = Path.Method { owner = impl; name; receiver } in
        add
          [
            (if writes lookups impl own then own
             else Path.Method { owner = trait.trait; name; receiver });
          ]
    | Trait_method
        {
          trait;
          name;
          receiver;
          evidence = Bound;
          self_type = Parameter { owner; name = "Self" };
          _;
        }
      when integer_trait owner -> (
        let own =
          List.concat_map
            (fun builtin ->
              List.filter_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if writes lookups impl method_ then Some method_ else None)
                (impls_for [ trait.trait ] (Types.builtin builtin)))
            integer_types
        in
        match own with
        | [] -> add [ Path.Method { owner = trait.trait; name; receiver } ]
        | own -> add own)
    | Trait_method { trait; name; receiver; _ } when dispatched called ->
        add [ Path.Method { owner = trait.trait; name; receiver } ]
    | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> ()
  in
  let entered = Hashtbl.create 4 in
  let enters code =
    if Hashtbl.mem entered code then false
    else (
      Hashtbl.replace entered code ();
      true)
  in
  let rec statement (locals : Tree.local_info array) (statement : Tree.statement) =
    match statement.kind with
    | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
        callee call.callee;
        invariant_checked call
    | For { iteration = Pull { next; _ }; _ } -> callee next
    | Assign { value = Function_value { path; _ }; _ } -> add [ path ]
    | Assign { value = To_any { value; trait; _ }; _ } ->
        uses_impls
          (impls_for (traits_with_required lookups.interface trait.trait) (Walk.operand_type value))
    | Assign
        {
          target = { root = Local local; projections = [] };
          value = Construct { variant; fields };
          _;
        } -> (
        match head_of locals.(local).type_ with
        | Some type_ ->
            let omitted =
              List.filter_map
                (fun (field, value) -> if Option.is_none value then Some field else None)
                fields
            in
            if omitted <> [] then field_defaults type_ variant omitted
        | None -> ())
    | _ -> ()
  and field_defaults type_ variant omitted =
    match Parts.defaults_of_path lookups.mir type_ with
    | Some (Field_defaults defaults) ->
        List.iter
          (fun (default : Tree.t Tree.field_default) ->
            if
              default.variant = variant && List.mem default.field omitted
              && enters (`Default (type_, variant, default.field))
            then Walk.iter_code_with_locals statement default.value)
          defaults
    | Some (Parameter_defaults _) | None -> ()
  and invariant_checked (call : Tree.call) =
    match (call.callee, call.arguments) with
    | ( Intrinsic { operation = Holds_invariant; type_arguments = [ Type checked ] },
        [ _; Passed { value = Constant { value = Integer index; _ }; _ } ] ) -> (
        match
          (head_of checked, Option.bind (head_of checked) (Parts.type_clauses_of_path lookups.mir))
        with
        | Some type_, Some clauses -> (
            match List.nth_opt clauses.invariants (Z.to_int index) with
            | Some { clause; is_executable = true; _ } when enters (`Invariant (type_, index)) ->
                Walk.iter_formula_with_locals statement clause
            | Some _ | None -> ())
        | _ -> ())
    | _ -> ()
  in
  Walk.iter_code_with_locals statement code;
  List.rev !callees

let of_path (lookups : lookups) path =
  let defaults =
    match Parts.defaults_of_path lookups.mir path with
    | Some (Parameter_defaults defaults) -> List.map snd defaults
    | Some (Field_defaults _) | None -> []
  in
  let code =
    match Parts.body_part_of_path lookups.mir path with
    | Body code | Initializer code -> [ code.tree ]
    | No_code -> []
  in
  List.sort_uniq Path.compare
    (List.concat_map (edges lookups ~package:(Path.package path)) (code @ defaults))

let implementations (lookups : lookups) ~visible (path : Path.t) =
  match path with
  | Method { owner; name; receiver } -> (
      match Interface.Definition.interface lookups.interface owner with
      | Some (Interface.Environment.Trait_interface _) ->
          List.concat_map
            (fun package ->
              List.filter_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if writes lookups impl method_ then Some method_ else None)
                (Interface.Impls.impls_of lookups.interface ~trait:owner package))
            visible
      | _ -> [])
  | _ -> []
