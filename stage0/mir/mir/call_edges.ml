type entered =
  [ `Field_default of Path.t * string option * string
  | `Parameter_default of Path.t * int
  | `Invariant of Path.t * Z.t ]

module Entered_table = Hashtbl.Make (Structural_key.Make (struct
  type t = entered
end))

type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

let find_head (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

type resolution = { target : Path.t option; supplied : Path.t list Lazy.t }

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

let list_methods_of_evidence (interface : Interface.Lookups.t) ~trait (evidence : Types.evidence) =
  let trait_interface = Interface.Definition.read_trait_interface interface trait in
  List.filter_map
    (fun (declared : Types.trait_method) ->
      Option.map
        (function
          | Interface.Impls.Declaration_for_view ->
              Path.Method
                { owner = trait; name = declared.method_name; receiver = declared.method_receiver }
          | Method_of_impl { impl; _ } ->
              make_impl_method trait_interface
                (Interface.Definition.read_impl_interface interface impl)
                impl declared)
        (Interface.Impls.locate_method interface evidence ~name:declared.method_name
           ~receiver:declared.method_receiver))
    trait_interface.methods

let is_self_of_enclosing_trait (type_ : Types.ty) =
  match type_ with
  | Parameter self | Projection { base = Parameter self; _ } -> Types.is_self_parameter self
  | _ -> false

let rec list_code_of_impl_for interface ((type_ : Types.ty), (bound : Types.trait_reference)) =
  List.concat_map
    (fun (required : Types.trait_reference) ->
      if is_self_of_enclosing_trait type_ then list_trait_methods interface required.trait
      else
        match
          Interface.Impls.resolve_evidence interface Types.no_substitution ~self_type:type_
            ~trait:required Bound
        with
        | (Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution }) as
          evidence ->
            list_methods_of_evidence interface ~trait:required.trait evidence
            @ List.concat_map (list_code_of_impl_for interface)
                (Interface.Impls.list_required_bounds
                   (Interface.Definition.read_impl_interface interface impl).impl_generics
                   substitution)
        | Bound -> [])
    (Interface.Properties.list_bound_closure interface ~self:type_ bound)

let list_code_supplied_to_self (interface : Interface.Lookups.t) ~trait substitution =
  match Types.find_argument (Types.make_self_parameter trait) substitution with
  | Some (Type self) ->
      list_code_of_impl_for interface
        ( self,
          {
            trait;
            trait_arguments =
              List.filter_map
                (fun (generic : Types.generic) -> Types.find_argument generic.generic substitution)
                (Interface.Definition.read_trait_interface interface trait).trait_generics;
            associated = [];
          } )
  | Some (Value _) | None -> []

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
        supplied = lazy (list_code_supplied_by_function_value interface instance path instantiation);
      }
  | Trait_method { trait; name; receiver; self_type; evidence; instantiation } ->
      let evidence =
        Interface.Impls.resolve_evidence interface instance ~self_type ~trait evidence
      in
      let self_type = substitute_type interface instance self_type in
      let trait = substitute_trait interface instance trait in
      let declaration = Path.Method { owner = trait.trait; name; receiver } in
      let type_arguments =
        List.map (substitute_argument interface instance) instantiation.type_arguments
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
        match Interface.Impls.locate_method interface evidence ~name ~receiver with
        | Some Declaration_for_view ->
            (Some declaration, lazy (list_code_supplied_to_declaration ()))
        | Some (Method_of_impl { impl; substitution }) ->
            let method_ = Path.Method { owner = impl; name; receiver } in
            (Some method_, lazy (list_code_supplied_to method_ ~bound_by_owner:substitution))
        | None ->
            ( (if is_self_of_enclosing_trait self_type then Some declaration else None),
              lazy (list_code_supplied_to_declaration ()) )
      in
      { target; supplied }
  | Capability_method _ | Intrinsic _ | Indirect _ -> { target = None; supplied = lazy [] }

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
      match
        Interface.Impls.resolve_evidence lookups.interface Types.no_substitution ~self_type:self
          ~trait Bound
      with
      | Impl { impl; _ } -> Some (Path.Method { owner = impl; name; receiver })
      | Derived_for_view _ | Bound -> None
    in
    match lookups.mir.find_form_origin method_ with
    | Some (Inherited key, _) when Path.equal key.path declaration -> Some method_
    | Some ((Inherited _ | Written _ | Derived _), _) | None -> None
  in
  match declaration with
  | Method { owner; name; receiver } ->
      Option.value (find_inheriting_method owner name receiver) ~default:declaration
  | _ -> declaration

type supplier = Call | Named_function of Path.t | Provide
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
  | Provide { provided; _ } ->
      supply Provide
        (List.concat_map
           (fun (implementation : Tree.provided) ->
             List.concat_map
               (fun (provided : Core.provided) ->
                 list_methods_of_evidence interface ~trait:provided.capability
                   (Impl { impl = provided.impl; substitution = provided.arguments }))
               implementation.provides)
           provided)
  | Basic
      ( Assign
          {
            value =
              ( Operand _ | Operation _ | Compare _ | Not _ | Construct _ | Array _ | Is_variant _
              | Convert _ | Copy _ | Lambda _ | Value_parameter _ | Parameter_default _
              | Specification _ );
            _;
          }
      | Call _ | Lend _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _
      | Ghost_assert _ | Path_note _ | Proof _ | Evaluated_assert _ )
  | For _
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo)
  | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ ->
      []

type dependency_kind = Read | Direct_call | Supplied of supplier
type omitted = Field of string | Argument of string

type dependency = {
  path : Path.t;
  kind : dependency_kind;
  origin : Core.origin;
  omitted : omitted option;
}

let list_dependencies (lookups : lookups) instance (code : Tree.t) =
  let dependencies = ref [] in
  let entered = Entered_table.create 4 in
  let enters code =
    if Entered_table.mem entered code then false
    else (
      Entered_table.replace entered code ();
      true)
  in
  let add ~through origin kind path =
    let origin, omitted =
      match through with Some (origin, omitted) -> (origin, Some omitted) | None -> (origin, None)
    in
    dependencies := { path; kind; origin; omitted } :: !dependencies
  in
  let add_constant ~through origin (place : Tree.place) =
    match place.root with
    | Constant path -> add ~through origin Read path
    | Local _ | Literal _ -> ()
  in
  let rec visit_code ~through ~instance (code : Tree.t) =
    Walk.iter_places (add_constant ~through) code;
    Walk.iter_code (visit_statement ~through ~instance) code
  and visit_statement ~through ~instance (statement : Tree.statement) =
    List.iter
      (function
        | Calls target -> add ~through statement.origin Direct_call target
        | Supplies { supplier; code } ->
            List.iter (add ~through statement.origin (Supplied supplier)) code)
      (list_statement_edges lookups.interface instance statement);
    match statement.kind with
    | Basic (Call { call; _ } | Lend { call; _ }) -> add_invariant_check ~through ~instance call
    | Basic (Assign { value = Parameter_default { definition; position; substitution }; _ }) ->
        if enters (`Parameter_default (definition, position)) then
          visit_code
            ~through:
              (Some
                 (Option.value through
                    ~default:(statement.origin, Argument (read_parameter_name definition position))))
            ~instance:(Types.substitute_substitution instance substitution)
            (Parts.read_parameter_default lookups.mir ~definition ~position).form
    | Basic (Assign { value = Construct { variant; fields; type_ }; _ }) -> (
        match find_head type_ with
        | Some head ->
            List.iter
              (fun (field, value) ->
                if Option.is_none value then
                  visit_field_default
                    ~through:(Some (Option.value through ~default:(statement.origin, Field field)))
                    ~instance head variant field)
              fields
        | None -> ())
    | Basic
        ( Assign
            {
              value =
                ( Operand _ | Operation _ | Compare _ | Not _ | Array _ | Is_variant _ | Convert _
                | Copy _ | Function_value _ | Lambda _ | Value_parameter _ | Specification _ );
              _;
            }
        | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _
        | Path_note _ | Proof _ | Evaluated_assert _ )
    | For _
    | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo)
    | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Provide _ | Resume _ | Yield _ ->
        ()
  and visit_field_default ~through ~instance type_ variant field =
    match Parts.read_defaults lookups.mir type_ with
    | Some { form = Field_defaults defaults; _ } ->
        List.iter
          (fun (default : Tree.t Tree.field_default) ->
            if
              default.variant = variant && default.field = field
              && enters (`Field_default (type_, variant, field))
            then visit_code ~through ~instance default.value)
          defaults
    | Some { form = Parameter_defaults _; _ } | None -> ()
  and read_parameter_name definition position =
    match Parts.read_contract lookups.mir definition with
    | Some { form = contract; _ } -> (
        match
          Option.bind (List.nth_opt contract.parameters position)
            (fun (parameter : Tree.parameter) -> Core_walk.find_local_name parameter.local)
        with
        | Some name -> name
        | None ->
            Compiler_bug.raise_bug ~stage:"MIR" "the parameter at position %d of `%s` has no name"
              position (Path.show definition))
    | None -> Compiler_bug.raise_bug ~stage:"MIR" "`%s` has no contract" (Path.show definition)
  and add_invariant_check ~through ~instance (call : Tree.call) =
    match (call.callee.target, call.arguments) with
    | ( Intrinsic { operation = Runtime Holds_invariant; type_arguments = [ Type checked ] },
        [ _; { value = Immediate { value = Integer index; _ }; _ } ] ) -> (
        match
          (find_head checked, Option.bind (find_head checked) (Parts.read_type_clauses lookups.mir))
        with
        | Some type_, Some { form = clauses; _ } -> (
            match List.nth_opt clauses.invariants (Z.to_int index) with
            | Some { clause; is_executable = true; _ } when enters (`Invariant (type_, index)) ->
                Walk.iter_formula_places (add_constant ~through) clause;
                Walk.iter_formula (visit_statement ~through ~instance) clause
            | Some _ | None -> ())
        | _ -> ())
    | _ -> ()
  in
  visit_code ~through:None ~instance code;
  List.rev !dependencies

let list_path_edges (lookups : lookups) path =
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
  List.sort_uniq Path.compare
    (List.concat_map
       (fun code ->
         List.map
           (fun (dependency : dependency) -> dependency.path)
           (list_dependencies lookups instance code))
       code)
