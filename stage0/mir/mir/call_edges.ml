type entered = [ `Default of Path.t * string option * string | `Invariant of Path.t * Z.t ]

module Entered_table = Hashtbl.Make (Structural_key.Make (struct
  type t = entered
end))

type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

let find_head (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

type resolution = {
  target : Path.t option;
  evidence : Core.evidence option;
  supplied : Path.t list Lazy.t;
}

let normalize interface ty =
  Interface.Impls.normalize interface ~list_bounds:Interface.Impls.list_no_bounds ty

let normalize_argument interface (argument : Types.argument) =
  match argument with Type ty -> Types.Type (normalize interface ty) | argument -> argument

let substitute_type interface instance ty = normalize interface (Types.substitute instance ty)

let substitute_argument interface instance argument =
  normalize_argument interface (Types.substitute_argument instance argument)

let substitute_trait interface instance (trait : Types.trait_reference) =
  let trait = Types.substitute_trait instance trait in
  { trait with trait_arguments = List.map (normalize_argument interface) trait.trait_arguments }

let find_evidence interface type_ trait =
  Interface.Impls.find_evidence interface ~list_bounds:Interface.Impls.list_no_bounds
    ~checks_conditions:false type_ trait

let list_trait_methods interface trait =
  List.map
    (fun (declared : Types.trait_method) ->
      Path.Method
        { owner = trait; name = declared.method_name; receiver = declared.method_receiver })
    (Interface.Definition.read_trait_interface interface trait).methods

let make_impl_method trait_interface impl_interface impl (declared : Types.trait_method) =
  Path.Method
    {
      owner = impl;
      name = declared.method_name;
      receiver =
        Option.value
          (Types.find_implementing_receiver trait_interface impl_interface declared)
          ~default:declared.method_receiver;
    }

let list_impl_methods (interface : Interface.Lookups.t) impl =
  let impl_interface = Interface.Definition.read_impl_interface interface impl in
  let trait_interface =
    Interface.Definition.read_trait_interface interface impl_interface.implements.trait
  in
  List.map (make_impl_method trait_interface impl_interface impl) trait_interface.methods

let is_self_of_enclosing_trait (type_ : Types.ty) =
  match type_ with
  | Parameter self | Projection { base = Parameter self; _ } -> Types.is_self_parameter self
  | _ -> false

let rec list_code_of_impl_for interface ((type_ : Types.ty), (bound : Types.trait_reference)) =
  List.concat_map
    (fun (required : Types.trait_reference) ->
      if is_self_of_enclosing_trait type_ then list_trait_methods interface required.trait
      else
        match find_evidence interface type_ required with
        | Some (From_impl { impl; substitution }) ->
            list_impl_methods interface impl
            @ List.concat_map (list_code_of_impl_for interface)
                (Interface.Impls.list_required_bounds
                   (Interface.Definition.read_impl_interface interface impl).impl_generics
                   substitution)
        | Some From_any -> list_trait_methods interface required.trait
        | Some (From_bound | Built_in | Undetermined | Absorbed _ | For_every_type_of_kind _) | None
          ->
            [])
    (Interface.Properties.list_bound_closure interface ~self:type_ bound)

let list_code_supplied_to_bound interface instance (type_, bound) =
  list_code_of_impl_for interface
    (substitute_type interface instance type_, substitute_trait interface instance bound)

let list_code_supplied_to_generics interface ?(instance = Types.no_substitution) generics
    substitution =
  List.concat_map
    (list_code_supplied_to_bound interface instance)
    (Interface.Impls.list_required_bounds generics substitution)

let list_code_supplied_to_callee interface instance path ~bound_by_owner type_arguments =
  match Interface.Impls.read_signature interface path with
  | Some (signature : Types.signature) ->
      let rec bind_generics substitution (generics : Types.generic list) arguments =
        match (generics, arguments) with
        | generic :: generics, argument :: arguments ->
            bind_generics
              (Types.bind_argument generic.generic argument substitution)
              generics arguments
        | _ -> substitution
      in
      list_code_supplied_to_generics interface ~instance signature.generics
        (bind_generics bound_by_owner
           (List.filter
              (fun (generic : Types.generic) ->
                Option.is_none (Types.find_argument generic.generic bound_by_owner))
              signature.generics)
           type_arguments)
  | None -> []

let list_code_supplied_by_function_value interface instance path
    (instantiation : Types.instantiation) =
  list_code_supplied_to_callee interface instance path ~bound_by_owner:Types.no_substitution
    instantiation.type_arguments

let resolve_callee (interface : Interface.Lookups.t) instance (callee : _ Core.target) =
  match callee with
  | Function { path; instantiation } ->
      {
        target = Some path;
        evidence = None;
        supplied = lazy (list_code_supplied_by_function_value interface instance path instantiation);
      }
  | Trait_method { trait; name; receiver; self_type; evidence; instantiation } ->
      let self_type = substitute_type interface instance self_type in
      let trait = substitute_trait interface instance trait in
      let declaration = Path.Method { owner = trait.trait; name; receiver } in
      let type_arguments =
        List.map (substitute_argument interface instance) instantiation.type_arguments
      in
      let evidence : Core.evidence =
        match evidence with
        | Impl { impl; substitution } ->
            Impl { impl; substitution = Types.substitute_substitution instance substitution }
        | Bound -> (
            match find_evidence interface self_type trait with
            | Some (From_impl { impl; substitution }) -> Impl { impl; substitution }
            | Some
                ( From_bound | From_any | Built_in | Undetermined | Absorbed _
                | For_every_type_of_kind _ )
            | None ->
                Bound)
        | Dynamic -> Dynamic
      in
      let list_code_supplied_to path ~bound_by_owner =
        list_code_supplied_to_callee interface Types.no_substitution path ~bound_by_owner
          type_arguments
      in
      let list_code_supplied_to_declaration () =
        list_code_supplied_to declaration
          ~bound_by_owner:
            (Types.make_trait_substitution
               (Interface.Definition.read_trait_interface interface trait.trait).trait_generics
               ~self:self_type trait)
      in
      let target, supplied =
        match evidence with
        | Impl { impl; substitution } ->
            let method_ = Path.Method { owner = impl; name; receiver } in
            (Some method_, lazy (list_code_supplied_to method_ ~bound_by_owner:substitution))
        | Dynamic -> (Some declaration, lazy (list_code_supplied_to_declaration ()))
        | Bound ->
            ( (if is_self_of_enclosing_trait self_type then Some declaration else None),
              lazy (list_code_supplied_to_declaration ()) )
      in
      { target; evidence = Some evidence; supplied }
  | Capability_method _ | Intrinsic _ | Indirect _ ->
      { target = None; evidence = None; supplied = lazy [] }

let resolve_node (lookups : lookups) (declaration : Path.t) instance =
  let find_inheriting_method owner name receiver =
    let ( let* ) = Option.bind in
    let* trait_interface = Interface.Definition.find_trait_interface lookups.interface owner in
    let* self =
      match Types.find_argument (Types.make_self_parameter owner) instance with
      | Some (Type self) -> Some self
      | Some (Value _) | None -> None
    in
    let trait : Types.trait_reference =
      {
        trait = owner;
        trait_arguments =
          List.filter_map
            (fun (generic : Types.generic) -> Types.find_argument generic.generic instance)
            trait_interface.trait_generics;
        associated = [];
      }
    in
    let* method_ =
      match find_evidence lookups.interface self trait with
      | Some (From_impl { impl; _ }) -> Some (Path.Method { owner = impl; name; receiver })
      | Some
          (From_bound | From_any | Built_in | Undetermined | Absorbed _ | For_every_type_of_kind _)
      | None ->
          None
    in
    match lookups.mir.find_form_origin method_ with
    | Some (Inherited key, _) when Path.equal key.path declaration -> Some method_
    | Some ((Inherited _ | Written _ | Derived _), _) | None -> None
  in
  match declaration with
  | Method { owner; name; receiver } ->
      Option.value (find_inheriting_method owner name receiver) ~default:declaration
  | _ -> declaration

type supplier = Call | Named_function of Path.t | Conversion_to_any | Provide
type edge = Calls of Path.t | Supplies of { supplier : supplier; code : Path.t list }

let list_statement_edges interface instance (statement : Tree.statement) =
  let supply supplier code = if code = [] then [] else [ Supplies { supplier; code } ] in
  (match Walk.find_callee statement with
    | Some callee ->
        let resolution = resolve_callee interface instance callee.target in
        List.map (fun target -> Calls target) (Option.to_list resolution.target)
        @ supply Call (Lazy.force resolution.supplied)
    | None -> [])
  @
  match statement.kind with
  | Basic (Assign { value = Function_value { path; instantiation; _ }; _ }) ->
      supply (Named_function path)
        (path :: list_code_supplied_by_function_value interface instance path instantiation)
  | Basic (Assign { value = To_any { value; trait; _ }; _ }) ->
      supply Conversion_to_any
        (list_code_supplied_to_bound interface instance (Walk.extract_operand_type value, trait))
  | Basic (Provide { provided; _ }) ->
      supply Provide
        (List.concat_map
           (fun (implementation : Tree.provided) ->
             List.concat_map
               (fun (provided : Core.provided) -> list_impl_methods interface provided.impl)
               implementation.provides)
           provided)
  | Basic
      ( Assign
          {
            value =
              ( Operand _ | Operation _ | Compare _ | Not _ | Construct _ | Array _ | Is_variant _
              | Convert _ | Copy _ | Lambda _ | Value_parameter _ | Specification _ );
            _;
          }
      | Call _ | Lend _ | Slice _ | Template _ | Live _ | Dead _ | Assert _ | Echo _ | Provide_end
      | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ )
  | For _
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo)
  | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ ->
      []

let list_edges (lookups : lookups) instance (code : Tree.t) =
  let callees = ref [] in
  let add paths = callees := List.rev_append paths !callees in
  let entered = Entered_table.create 4 in
  let enters code =
    if Entered_table.mem entered code then false
    else (
      Entered_table.replace entered code ();
      true)
  in
  let rec visit_statement (statement : Tree.statement) =
    List.iter
      (function Calls target -> add [ target ] | Supplies { code; _ } -> add code)
      (list_statement_edges lookups.interface instance statement);
    match statement.kind with
    | Basic (Call { call; _ } | Lend { call; _ } | Template { call; _ } | Slice { call; _ }) ->
        add_invariant_check call
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
    | Basic
        ( Assign
            {
              value =
                ( Operand _ | Operation _ | Compare _ | Not _ | Array _ | Is_variant _ | Convert _
                | To_any _ | Copy _ | Function_value _ | Lambda _ | Value_parameter _
                | Specification _ );
              _;
            }
        | Provide _ | Live _ | Dead _ | Assert _ | Echo _ | Provide_end | Loan_start _ | Loan_end _
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
  and add_invariant_check (call : Tree.call) =
    match (call.callee.target, call.arguments) with
    | ( Intrinsic { operation = Runtime Holds_invariant; type_arguments = [ Type checked ] },
        [ _; Passed { value = Immediate { value = Integer index; _ }; _ } ] ) -> (
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
  let instance =
    match lookups.mir.find_form_origin path with
    | Some (_, substitution) -> substitution
    | None -> Types.no_substitution
  in
  List.sort_uniq Path.compare (List.concat_map (list_edges lookups instance) (code @ defaults))

let list_implementations (lookups : lookups) ~calling_package (path : Path.t) =
  match path with
  | Method { owner; name; receiver } -> (
      match Interface.Definition.find_interface lookups.interface owner with
      | Some (Interface.Environment.Trait_interface trait_interface) ->
          let declared =
            List.filter
              (fun (declared : Types.trait_method) ->
                declared.method_name = name && declared.method_receiver = receiver)
              trait_interface.methods
          in
          List.concat_map
            (fun package ->
              List.concat_map
                (fun impl ->
                  List.map
                    (make_impl_method trait_interface
                       (Interface.Definition.read_impl_interface lookups.interface impl)
                       impl)
                    declared)
                (Interface.Impls.list_impls_of_trait lookups.interface ~trait:owner package))
            (calling_package
            :: Resolve.Names.list_transitive_dependencies lookups.interface.names calling_package)
      | _ -> [])
  | _ -> []
