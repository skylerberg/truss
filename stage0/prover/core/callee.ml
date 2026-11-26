type trait_method = {
  trait : Types.trait_reference;
  name : string;
  receiver : Path.receiver;
  self_type : Types.ty;
  evidence : Types.evidence;
}

type definition = {
  path : Path.t;
  contract : State.contract option;
  substitution_of : State.clauses -> Types.substitution;
  type_arguments : Types.argument list;
  declaration : Path.t;
  declaration_substitution : Types.substitution;
  trait_method : trait_method option;
  capability_method : (Path.t * string) option;
}

type target =
  | Definition of definition
  | Function_value
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }

type t = {
  target : target;
  group_member : Path.t option;
  lends : Language.Mode.t option;
  uses : Types.capability_set;
}

let substitute_arguments context (frame : State.frame) arguments =
  List.map
    (fun argument ->
      match Types.substitute_argument_erased frame.substitution argument with
      | Types.Type ty -> Types.Type (Encoding.substitute_type context frame ty)
      | other -> other)
    arguments

let bind_generics context path (instantiation : Types.instantiation) ~fixed =
  let generics, capability_parameters =
    match Contracts.read_signature context path with
    | Some (signature : Types.signature) ->
        ( List.map (fun (generic : Types.generic) -> generic.generic) signature.generics,
          signature.capability_parameters )
    | None -> ([], [])
  in
  let rec bind_remaining substitution parameters arguments =
    match (parameters, arguments) with
    | parameter :: parameters, argument :: arguments ->
        bind_remaining (Types.bind_argument parameter argument substitution) parameters arguments
    | _ -> substitution
  in
  Types.combine_substitutions
    (bind_remaining fixed
       (List.filter
          (fun parameter -> Option.is_none (Types.find_argument parameter fixed))
          generics)
       instantiation.type_arguments)
    (Types.make_capability_substitution capability_parameters instantiation.capability_arguments)

let add_restated_clauses (context : State.context) (method_ : trait_method) instantiation
    (contract : State.contract) =
  {
    contract with
    restated_clauses =
      List.map
        (fun ((subtrait : Types.trait_reference), (clauses : State.clauses)) ->
          {
            clauses with
            bindings =
              bind_generics context
                (Path.Method
                   { owner = subtrait.trait; name = method_.name; receiver = method_.receiver })
                instantiation
                ~fixed:
                  (Contracts.make_trait_substitution context.lookups subtrait method_.self_type);
          })
        (Contracts.list_restated_clauses context
           ~packages:(Operations.list_impl_packages context method_.self_type)
           ~self_type:method_.self_type method_.trait.trait method_.name method_.receiver);
  }

let bind_clauses substitution_of (clauses : State.clauses) =
  Types.combine_substitutions (substitution_of clauses) clauses.bindings

let resolve_target (context : State.context) (frame : State.frame) (written : _ Core.target) =
  let substitute_instantiation (instantiation : Types.instantiation) : Types.instantiation =
    {
      type_arguments = substitute_arguments context frame instantiation.type_arguments;
      capability_arguments =
        List.map
          (fun (name, argument) ->
            (name, Types.substitute_capabilities frame.substitution argument))
          instantiation.capability_arguments;
    }
  in
  match written with
  | Function { path; instantiation } ->
      let instantiation = substitute_instantiation instantiation in
      let substitution = bind_generics context path instantiation ~fixed:Types.no_substitution in
      Definition
        {
          path;
          contract = Contracts.find_function_contract context path;
          substitution_of = bind_clauses (fun _ -> substitution);
          type_arguments = instantiation.type_arguments;
          declaration = path;
          declaration_substitution = substitution;
          trait_method = None;
          capability_method = None;
        }
  | Trait_method { trait; name; receiver; evidence; self_type; instantiation } ->
      let instantiation = substitute_instantiation instantiation in
      let evidence =
        Interface.Impls.resolve_evidence context.lookups.interface frame.substitution ~self_type
          ~trait evidence
      in
      let method_ =
        {
          trait =
            {
              trait with
              trait_arguments = substitute_arguments context frame trait.trait_arguments;
            };
          name;
          receiver;
          self_type = Encoding.substitute_type context frame self_type;
          evidence;
        }
      in
      let declaration = Path.Method { owner = trait.trait; name; receiver } in
      let declaration_substitution =
        bind_generics context declaration instantiation
          ~fixed:(Contracts.make_trait_substitution context.lookups method_.trait method_.self_type)
      in
      let path, substitution =
        match evidence with
        | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
            let path = Path.Method { owner = impl; name; receiver } in
            (path, bind_generics context path instantiation ~fixed:substitution)
        | Bound -> (declaration, declaration_substitution)
      in
      Definition
        {
          path;
          contract =
            Option.map
              (add_restated_clauses context method_ instantiation)
              (Contracts.find_method_contract context method_.trait name receiver evidence);
          substitution_of =
            bind_clauses (fun clauses ->
                if clauses.inherited then declaration_substitution else substitution);
          type_arguments =
            Facts.list_method_type_arguments method_.trait ~self_type:method_.self_type
              instantiation.type_arguments;
          declaration;
          declaration_substitution;
          trait_method = Some method_;
          capability_method = None;
        }
  | Capability_method { capability; name } ->
      let path = Path.make_capability_method capability name in
      Definition
        {
          path;
          contract = Contracts.find_capability_contract context capability name;
          substitution_of = bind_clauses (fun _ -> Types.no_substitution);
          type_arguments = [];
          declaration = path;
          declaration_substitution = Types.no_substitution;
          trait_method = None;
          capability_method = Some (capability, name);
        }
  | Indirect _ -> Function_value
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }

let resolve context frame written ~lends ~uses =
  {
    target = resolve_target context frame written;
    group_member = Cycles.find_group_member context frame written;
    lends;
    uses;
  }

let is_update_step context (callee : t) =
  match callee.target with
  | Definition { path; trait_method = None; capability_method = None; _ } -> (
      match Contracts.read_signature context path with
      | Some signature -> signature.is_update_step
      | None -> false)
  | Definition _ | Function_value | Intrinsic _ -> false

let find_parameter_type context (callee : t) index =
  match callee.target with
  | Definition { declaration; declaration_substitution; _ } ->
      Option.bind (Contracts.read_signature context declaration)
        (fun (signature : Types.signature) ->
          let types =
            (match signature.receiver with Some (_, ty) -> [ ty ] | None -> [])
            @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
          in
          Option.map (Types.substitute_erased declaration_substitution) (List.nth_opt types index))
  | Function_value | Intrinsic _ -> None

let find_callback context (frame : State.frame) (callee : t) position ~known =
  match callee.target with
  | Definition { declaration; declaration_substitution; _ } ->
      Option.bind (Contracts.find_callee_clauses context declaration)
        (fun (clauses : State.clauses) ->
          Option.map
            (fun callback ->
              ( clauses.callee,
                Contracts.make_entry_frame frame clauses ~arguments:known
                  ~substitution:declaration_substitution,
                callback ))
            (List.assoc_opt position clauses.callbacks))
  | Function_value | Intrinsic _ -> None
