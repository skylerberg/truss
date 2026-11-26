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

let find_method_of_evidence (interface : Interface.Lookups.t) ~trait (evidence : Types.evidence)
    (declared : Types.trait_method) =
  Option.map
    (function
      | Interface.Impls.Declaration_for_view ->
          Path.Method
            { owner = trait; name = declared.method_name; receiver = declared.method_receiver }
      | Method_of_impl { impl; _ } ->
          make_impl_method
            (Interface.Definition.read_trait_interface interface trait)
            (Interface.Definition.read_impl_interface interface impl)
            impl declared)
    (Interface.Impls.locate_method interface evidence ~name:declared.method_name
       ~receiver:declared.method_receiver)

let list_methods_of_evidence (interface : Interface.Lookups.t) ~trait (evidence : Types.evidence) =
  List.filter_map
    (find_method_of_evidence interface ~trait evidence)
    (Interface.Definition.read_trait_interface interface trait).methods

let is_self_of_enclosing_trait (type_ : Types.ty) =
  match type_ with
  | Parameter self | Projection { base = Parameter self; _ } -> Types.is_self_parameter self
  | _ -> false

let list_bounds_that_an_impl_assumes interface impl substitution =
  let impl_interface = Interface.Definition.read_impl_interface interface impl in
  Interface.Impls.list_required_bounds impl_interface.impl_generics substitution
  @ Interface.Impls.list_associated_type_bounds interface impl_interface substitution

let has_entered entered (trait : Types.trait_reference) type_ =
  List.exists
    (fun (entered_trait, entered_type) ->
      Path.equal entered_trait trait.trait && Types.equal entered_type type_)
    entered

let rec list_code_of_impl_for ?(entered = []) interface
    ((type_ : Types.ty), (bound : Types.trait_reference)) =
  List.concat_map
    (fun (required : Types.trait_reference) ->
      if is_self_of_enclosing_trait type_ then list_trait_methods interface required.trait
      else if has_entered entered required type_ then []
      else
        match
          Interface.Impls.resolve_evidence interface Types.no_substitution ~self_type:type_
            ~trait:required Bound
        with
        | (Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution }) as
          evidence ->
            list_methods_of_evidence interface ~trait:required.trait evidence
            @ List.concat_map
                (list_code_of_impl_for ~entered:((required.trait, type_) :: entered) interface)
                (list_bounds_that_an_impl_assumes interface impl substitution)
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

let rec bind_generics substitution (generics : Types.generic list) arguments =
  match (generics, arguments) with
  | generic :: generics, argument :: arguments ->
      bind_generics (Types.bind_argument generic.generic argument substitution) generics arguments
  | _ -> substitution

let list_code_supplied_to_callee interface instance path ~bound_by_owner type_arguments =
  match Interface.Impls.read_signature interface path with
  | Some (signature : Types.signature) ->
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
  | Intrinsic { operation; _ } when Intrinsic.has_contract operation ->
      { target = Some (Intrinsic.make_contract_path operation); supplied = lazy [] }
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
      | Ghost_assert _ | Proof _ | Evaluated_assert _ )
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

type assumed_laws = {
  impl : Path.t;
  trait : Types.trait_reference;
  type_ : Types.ty;
  origin : Core.origin option;
  is_assumed_by_the_callee : bool;
}

let states_laws (interface : Interface.Lookups.t) trait =
  match interface.find_trait_header trait with Some header -> header.laws <> [] | None -> false

let list_instance_field_types (interface : Interface.Lookups.t) (ty : Types.ty) =
  match Types.strip_view ty with
  | Named { path; arguments } -> (
      match Interface.Definition.find_interface interface path with
      | Some (Interface.Environment.Type_interface type_interface) ->
          List.map
            (fun (field : Types.field) -> field.field_type)
            (Option.value ~default:[] (Types.instantiate_fields type_interface arguments)
            @ List.concat_map
                (fun (variant : Types.variant) -> Option.value ~default:[] variant.fields)
                (Option.value ~default:[] (Types.instantiate_variants type_interface arguments)))
      | Some _ | None -> [])
  | _ -> []

let rec list_laws_of_bound ?(entered = []) (interface : Interface.Lookups.t) ~self_type
    ~is_assumed_by_the_callee trait =
  List.concat_map
    (fun (required : Types.trait_reference) ->
      let is_entered = has_entered entered required self_type in
      let entered = (required.trait, self_type) :: entered in
      if is_entered then []
      else
        match
          Interface.Impls.resolve_evidence interface Types.no_substitution ~self_type
            ~trait:required Bound
        with
        | Bound -> []
        | Impl { impl = Derived _; _ } | Derived_for_view { viewed = Derived _; _ } ->
            List.concat_map
              (fun field_type ->
                list_laws_of_bound ~entered interface ~self_type:field_type
                  ~is_assumed_by_the_callee:true required)
              (list_instance_field_types interface self_type)
        | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
            (if states_laws interface required.trait then
               [
                 {
                   impl;
                   trait = required;
                   type_ = self_type;
                   origin = None;
                   is_assumed_by_the_callee;
                 };
               ]
             else [])
            @ List.concat_map
                (fun (assumed_of, assumed) ->
                  list_laws_of_bound ~entered interface ~self_type:assumed_of
                    ~is_assumed_by_the_callee:true assumed)
                (list_bounds_that_an_impl_assumes interface impl substitution))
    (Interface.Properties.list_bound_closure interface ~self:self_type trait)

let list_laws_of_generics (interface : Interface.Lookups.t) instance path
    (instantiation : Types.instantiation) =
  match Interface.Impls.read_signature interface path with
  | Some signature ->
      let arguments = Types.make_substitution signature.generics instantiation.type_arguments in
      List.concat_map
        (fun (generic : Types.generic) ->
          match Types.find_argument generic.generic arguments with
          | Some (Type argument) ->
              let self_type = substitute_type interface instance argument in
              List.concat_map
                (fun bound ->
                  list_laws_of_bound interface ~self_type ~is_assumed_by_the_callee:true
                    (substitute_trait interface instance (Types.substitute_trait arguments bound)))
                (Types.list_bounds signature.generics generic.generic)
          | Some (Value _) | None -> [])
        signature.generics
  | None -> []

let list_laws_assumed_at (interface : Interface.Lookups.t) instance (statement : Tree.statement) =
  (match Walk.find_callee statement with
    | Some { target = Trait_method { trait; self_type; name; receiver; instantiation; _ }; _ } ->
        list_laws_of_bound interface
          ~self_type:(substitute_type interface instance self_type)
          ~is_assumed_by_the_callee:false
          (substitute_trait interface instance trait)
        @ list_laws_of_generics interface instance
            (Path.Method { owner = trait.trait; name; receiver })
            instantiation
    | Some { target = Function { path; instantiation }; _ } ->
        list_laws_of_generics interface instance path instantiation
    | Some { target = Capability_method _ | Intrinsic _ | Indirect _; _ } | None -> [])
  @
  match statement.kind with
  | Basic (Assign { value = Function_value { path; instantiation; _ }; _ }) ->
      list_laws_of_generics interface instance path instantiation
  | _ -> []

let collect (lookups : lookups) instance visit_roots =
  let dependencies = ref [] in
  let laws = ref [] in
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
  and visit_formula ~through ~instance (formula : Tree.formula) =
    Walk.iter_formula_places (add_constant ~through) formula;
    Walk.iter_formula (visit_statement ~through ~instance) formula
  and visit_statement ~through ~instance (statement : Tree.statement) =
    List.iter
      (function
        | Calls target -> add ~through statement.origin Direct_call target
        | Supplies { supplier; code } ->
            List.iter (add ~through statement.origin (Supplied supplier)) code)
      (list_statement_edges lookups.interface instance statement);
    List.iter
      (fun (assumed : assumed_laws) ->
        let origin = match through with Some (origin, _) -> origin | None -> statement.origin in
        laws := { assumed with origin = Some origin } :: !laws)
      (list_laws_assumed_at lookups.interface instance statement);
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
        | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Proof _
        | Evaluated_assert _ )
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
                visit_formula ~through ~instance clause
            | Some _ | None -> ())
        | _ -> ())
    | _ -> ()
  in
  visit_roots
    ~code:(visit_code ~through:None ~instance)
    ~formula:(visit_formula ~through:None ~instance);
  (List.rev !dependencies, List.rev !laws)

let collect_dependencies lookups instance visit_roots = fst (collect lookups instance visit_roots)

let list_dependencies lookups instance (code : Tree.t) =
  collect_dependencies lookups instance (fun ~code:visit ~formula:_ -> visit code)

let list_formula_dependencies lookups instance (formula : Tree.formula) =
  collect_dependencies lookups instance (fun ~code:_ ~formula:visit -> visit formula)

let list_paths dependencies =
  List.map (fun (dependency : dependency) -> dependency.path) dependencies

let find_instance (lookups : lookups) path =
  match lookups.mir.find_form_origin path with
  | Some (_, substitution) -> substitution
  | None -> Types.no_substitution

let find_code (lookups : lookups) path =
  match Parts.read_body_part lookups.mir path with
  | Some { form = Body code | Initializer code; _ } -> Some code.tree
  | Some { form = No_code; _ } | None -> None

let is_specification_only (lookups : lookups) path =
  match Interface.Impls.read_signature lookups.interface path with
  | Some signature -> signature.specification_only
  | None -> false

let list_run_statements (lookups : lookups) path =
  let statements = ref [] in
  Option.iter
    (Walk.iter_run_code (fun statement -> statements := statement :: !statements))
    (find_code lookups path);
  !statements

let list_invariant_clauses (lookups : lookups) type_ =
  match Parts.read_type_clauses lookups.mir type_ with
  | Some { form = clauses; _ } ->
      List.map (fun (requirement : Tree.requirement) -> requirement.clause) clauses.invariants
  | None -> []

let is_abort_site (lookups : lookups) instance (statement : Tree.statement) =
  let states_no_allocation declaration =
    match Interface.Impls.read_signature lookups.interface declaration with
    | Some signature -> Types.states_no_allocation signature.costs
    | None -> false
  in
  match statement.kind with
  | Basic
      (Call
         {
           call =
             {
               callee = { target = Intrinsic { operation = Buffer Storage_with_capacity; _ }; _ };
               arguments = [ { value = Immediate { value = Integer capacity; _ }; _ } ];
               _;
             };
           _;
         }) ->
      not (Z.equal capacity Z.zero)
  | _ -> (
      match Walk.find_callee statement with
      | Some { target = Intrinsic { operation; _ }; _ } -> Intrinsic.may_abort operation
      | Some { target = Indirect called; _ } -> (
          match substitute_type lookups.interface instance (Walk.extract_operand_type called) with
          | Function function_type -> not (Types.states_no_allocation function_type.costs)
          | called_type ->
              Compiler_bug.raise_bug ~stage:"MIR" "a call through a value of type `%s`"
                (Types.show called_type))
      | Some { target = Trait_method { trait; name; receiver; _ } as target; _ } -> (
          let declaration = Path.Method { owner = trait.trait; name; receiver } in
          match (resolve_callee lookups.interface instance target).target with
          | Some resolved when not (Path.equal resolved declaration) -> false
          | Some _ | None -> not (states_no_allocation declaration))
      | Some { target = Function _ | Capability_method _; _ } | None -> false)

let rec body_may_abort (lookups : lookups) instance ~lambdas (body : Tree.body) ~may_abort =
  let nested_may_abort index =
    body_may_abort lookups instance ~lambdas lambdas.(index) ~may_abort
  in
  let aborts = ref false in
  Walk.iter_run_block
    (fun statement ->
      if
        is_abort_site lookups instance statement
        || List.exists
             (function
               | Calls callee -> may_abort callee
               | Supplies { code; _ } -> List.exists may_abort code)
             (list_statement_edges lookups.interface instance statement)
        ||
        match statement.kind with
        | Basic (Assign { value = Lambda { body = nested; _ }; _ }) -> nested_may_abort nested
        | Basic (Call { call; _ } | Lend { call; _ }) ->
            List.exists
              (fun (argument : Tree.argument) ->
                match argument.function_ with
                | Some (Lambda_expression { body = nested; _ }) -> nested_may_abort nested
                | Some (Function_reference _) | None -> false)
              call.arguments
        | _ -> false
      then aborts := true)
    body.code;
  !aborts

let has_abort_site (lookups : lookups) path =
  match Intrinsic.find_contract_operation path with
  | Some operation -> Intrinsic.may_abort operation
  | None ->
      List.exists
        (is_abort_site lookups (find_instance lookups path))
        (list_run_statements lookups path)

let list_callees_that_run (lookups : lookups) path =
  let instance = find_instance lookups path in
  List.sort_uniq Path.compare
    (List.concat_map
       (fun statement ->
         match Walk.find_callee statement with
         | Some { target = Intrinsic _; _ } -> []
         | Some _ | None ->
             List.concat_map
               (function Calls callee -> [ callee ] | Supplies { code; _ } -> code)
               (list_statement_edges lookups.interface instance statement))
       (list_run_statements lookups path))

let list_path_edges (lookups : lookups) path =
  List.sort_uniq Path.compare
    (List.concat_map
       (fun code -> list_paths (list_dependencies lookups (find_instance lookups path) code))
       (Option.to_list (find_code lookups path)))

let list_contract_formulas (contract : Tree.contract) =
  let list_clauses requirements =
    List.map (fun (requirement : Tree.requirement) -> requirement.clause) requirements
  in
  list_clauses contract.panics_unless
  @ list_clauses contract.requires @ contract.ensures @ contract.decreases
  @ List.map
      (fun (cost : Tree.cost) ->
        match cost.bound with Order_of amount | At_most amount | Exactly amount -> amount)
      contract.costs
  @ List.concat_map
      (fun (_, (callback : Tree.callback)) -> callback.requires @ callback.ensures)
      contract.callbacks

let find_contract (lookups : lookups) path =
  Option.map (fun (read : _ Parts.sourced) -> read.form) (Parts.read_contract lookups.mir path)

let list_contract_dependencies (lookups : lookups) path =
  List.concat_map
    (list_formula_dependencies lookups (find_instance lookups path))
    (Option.fold ~none:[] ~some:list_contract_formulas (find_contract lookups path))

let list_inherited_contract_dependencies (lookups : lookups) path =
  match Interface.Impls.find_implemented_method lookups.interface path with
  | Some implemented ->
      List.concat_map
        (list_formula_dependencies lookups implemented.implementation.substitution)
        (Option.fold ~none:[] ~some:list_contract_formulas
           (find_contract lookups implemented.declaration))
  | None -> []

let list_potential_clauses (lookups : lookups) type_ =
  match Parts.read_type_clauses lookups.mir type_ with
  | Some { form = clauses; _ } -> Option.to_list clauses.potential
  | None -> []

let list_invariant_dependencies lookups type_ =
  List.concat_map
    (list_formula_dependencies lookups Types.no_substitution)
    (list_invariant_clauses lookups type_)

let list_potential_dependencies lookups type_ =
  List.concat_map
    (list_formula_dependencies lookups Types.no_substitution)
    (list_potential_clauses lookups type_)

let list_field_types (interface : Interface.Lookups.t) path =
  match Interface.Definition.find_type_interface interface path with
  | Some { shape = Record fields; _ } ->
      List.map (fun (field : Types.field) -> field.field_type) fields
  | Some { shape = Sum variants; _ } ->
      List.concat_map
        (fun (variant : Types.variant) ->
          List.map
            (fun (field : Types.field) -> field.field_type)
            (Option.value ~default:[] variant.fields))
        variants
  | Some _ | None -> []

let list_signature_types (lookups : lookups) path =
  match Interface.Definition.find_interface lookups.interface path with
  | Some (Function_interface signature | Test_interface signature | Theorem_interface signature) ->
      List.map snd (Option.to_list signature.receiver)
      @ List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
      @ [ (match signature.output with Returns type_ | Lends (_, type_) -> type_) ]
  | Some (Constant_interface _) ->
      [ Interface.Definition.read_constant_type lookups.interface path ]
  | Some (Type_interface _) -> list_field_types lookups.interface path
  | Some (Trait_interface _ | Impl_interface _ | Law_proof_interface _ | Error_interface _) | None
    ->
      []

module Type_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.ty
end))

type type_use = { type_ : Types.ty; origin : Core.origin option }

let iter_type_parts visit type_ =
  ignore
    (Types.exists
       (fun part ->
         visit part;
         false)
       type_)

let list_type_uses (lookups : lookups) path =
  let instance = find_instance lookups path in
  let uses = Type_table.create 16 in
  let ordered = ref [] in
  let note origin type_ =
    iter_type_parts
      (fun part ->
        match part with
        | Types.Named _ when not (Type_table.mem uses part) ->
            Type_table.replace uses part ();
            ordered := { type_ = part; origin } :: !ordered
        | _ -> ())
      (substitute_type lookups.interface instance type_)
  in
  let note_local (info : Tree.local_info) = note (Some info.origin) info.type_ in
  let contract = find_contract lookups path in
  Option.iter (Walk.iter_locals note_local) (find_code lookups path);
  List.iter
    (fun (formula : Tree.formula) ->
      Walk.iter_formula_locals note_local formula;
      note None formula.type_)
    (Option.fold ~none:[] ~some:list_contract_formulas contract);
  Option.iter
    (fun (contract : Tree.contract) ->
      List.iter (fun (parameter : Tree.parameter) -> note None parameter.type_) contract.parameters)
    contract;
  List.iter (note None) (list_signature_types lookups path);
  List.rev !ordered

let list_instance_dependencies (lookups : lookups) (instance : Types.ty) =
  let entered = Type_table.create 8 in
  let rec list_from ~enclosing (type_ : Types.ty) =
    match type_ with
    | Named { path; arguments = _ :: _ as arguments } when not (Type_table.mem entered type_) -> (
        Type_table.replace entered type_ ();
        match Interface.Definition.find_type_interface lookups.interface path with
        | Some { type_generics; _ } ->
            let substitution = bind_generics Types.no_substitution type_generics arguments in
            if List.exists (Path.equal path) enclosing then
              list_code_supplied_to_generics lookups.interface type_generics substitution
            else
              list_paths
                (List.concat_map
                   (list_formula_dependencies lookups substitution)
                   (list_invariant_clauses lookups path @ list_potential_clauses lookups path))
              @ List.concat_map
                  (fun field_type ->
                    let dependencies = ref [] in
                    iter_type_parts
                      (fun part ->
                        dependencies :=
                          list_from ~enclosing:(path :: enclosing) part @ !dependencies)
                      (substitute_type lookups.interface substitution field_type);
                    !dependencies)
                  (list_field_types lookups.interface path)
        | None -> [])
    | _ -> []
  in
  list_from ~enclosing:[] instance

type instance_use = { used : type_use; dependencies : Path.t list }

let list_instance_uses (lookups : lookups) path =
  List.filter_map
    (fun (used : type_use) ->
      match list_instance_dependencies lookups used.type_ with
      | [] -> None
      | dependencies -> Some { used; dependencies })
    (list_type_uses lookups path)

let has_fields (interface : Interface.Lookups.t) path =
  match Interface.Definition.find_type_interface interface path with
  | Some { shape = Record _ | Sum _; _ } -> true
  | Some _ | None -> false

let list_law_proofs (lookups : lookups) package (trait : Types.trait_reference)
    (for_type : Types.ty) =
  let is_same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
  in
  let named_laws =
    match (Interface.Impls.find_head for_type, lookups.interface.find_trait_header trait.trait) with
    | Some type_head, Some header ->
        List.concat_map
          (fun law ->
            lookups.interface.names.list_law_proofs package { trait = trait.trait; law; type_head })
          header.laws
    | _ -> []
  in
  List.filter_map
    (fun (key : Resolve.Names.key) ->
      match Interface.Definition.find_interface lookups.interface key.path with
      | Some (Interface.Environment.Law_proof_interface proven) -> (
          let variables =
            List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
          in
          match
            Interface.Impls.match_type ~variables Types.no_substitution proven.for_type for_type
          with
          | Some renaming
            when List.equal is_same_argument
                   (List.map
                      (Types.substitute_argument_erased renaming)
                      proven.trait.trait_arguments)
                   trait.trait_arguments ->
              Some (proven.law, key, renaming)
          | _ -> None)
      | _ -> Compiler_bug.raise_bug ~stage:"MIR" "%s is not a law proof" (Path.show key.path))
    named_laws

let find_implementing (interface : Interface.Lookups.t) (trait : Types.trait_reference) self_type =
  match
    Interface.Impls.resolve_evidence interface Types.no_substitution ~self_type ~trait Bound
  with
  | Impl { impl; _ } | Derived_for_view { viewed = impl; _ } -> Some impl
  | Bound -> None

let find_proven_impl (lookups : lookups) path =
  match Interface.Definition.find_interface lookups.interface path with
  | Some (Interface.Environment.Law_proof_interface proven) ->
      find_implementing lookups.interface proven.trait proven.for_type
  | Some _ | None ->
      Option.map
        (fun (_ : Types.impl_interface) -> path)
        (Interface.Definition.find_impl_interface lookups.interface path)

let list_trait_laws (lookups : lookups) trait =
  match lookups.interface.names.find_key trait with
  | Some key -> (lookups.mir.read_contract_part key).laws
  | None -> []

let list_assumed_laws (lookups : lookups) path =
  let instance = find_instance lookups path in
  let list_laws substitution formulas =
    snd (collect lookups substitution (fun ~code:_ ~formula -> List.iter formula formulas))
  in
  let list_laws_of_another_source substitution formulas =
    List.map
      (fun (laws : assumed_laws) -> { laws with origin = None })
      (list_laws substitution formulas)
  in
  let of_code =
    snd
      (collect lookups instance (fun ~code ~formula:_ -> Option.iter code (find_code lookups path)))
  in
  let of_contract =
    list_laws instance
      (Option.fold ~none:[] ~some:list_contract_formulas (find_contract lookups path))
  in
  let of_inherited_contract =
    match Interface.Impls.find_implemented_method lookups.interface path with
    | Some implemented ->
        list_laws_of_another_source implemented.implementation.substitution
          (Option.fold ~none:[] ~some:list_contract_formulas
             (find_contract lookups implemented.declaration))
    | None -> []
  in
  let of_type_clauses =
    list_laws Types.no_substitution
      (list_invariant_clauses lookups path @ list_potential_clauses lookups path)
  in
  let of_proven_laws =
    match Interface.Definition.find_impl_interface lookups.interface path with
    | Some impl ->
        list_laws_of_another_source
          (Types.make_trait_substitution
             (Interface.Definition.read_trait_interface lookups.interface impl.implements.trait)
               .trait_generics
             ~self:impl.for_type impl.implements)
          (List.concat_map
             (fun (law : Tree.law) -> law.requires @ [ law.states ])
             (list_trait_laws lookups impl.implements.trait))
    | None -> []
  in
  let proven = find_proven_impl lookups path in
  List.filter
    (fun (laws : assumed_laws) ->
      laws.is_assumed_by_the_callee || not (Option.equal Path.equal proven (Some laws.impl)))
    (of_code @ of_contract @ of_inherited_contract @ of_type_clauses @ of_proven_laws)

let list_own_law_proofs (lookups : lookups) path =
  match Interface.Definition.find_impl_interface lookups.interface path with
  | Some impl ->
      List.map
        (fun (_, (key : Resolve.Names.key), _) -> key.path)
        (list_law_proofs lookups (Path.locate_package path) impl.implements impl.for_type)
  | None -> []

let list_assumed_paths (lookups : lookups) path =
  let package = Path.locate_package path in
  let is_type_of_package (used : type_use) =
    match used.type_ with
    | Named { path = head; _ }
      when Path.compare_package (Path.locate_package head) package = 0
           && has_fields lookups.interface head ->
        Some head
    | _ -> None
  in
  List.sort_uniq Path.compare
    (list_paths (list_contract_dependencies lookups path)
    @ list_paths (list_inherited_contract_dependencies lookups path)
    @ list_paths (list_invariant_dependencies lookups path)
    @ list_paths (list_potential_dependencies lookups path)
    @ List.filter_map is_type_of_package (list_type_uses lookups path)
    @ List.concat_map
        (fun (instance : instance_use) -> instance.dependencies)
        (list_instance_uses lookups path)
    @ List.map (fun (laws : assumed_laws) -> laws.impl) (list_assumed_laws lookups path)
    @ list_own_law_proofs lookups path)
