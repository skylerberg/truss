include Tree
module Graph = Graph
module Call_edges = Call_edges
include Walk
include Parts

let expand_formula = Expansion.expand_formula

let list_callee_modified_fields (lookups : Interface.Lookups.t) substitution (callee : Tree.callee)
    position =
  let path : Path.t option =
    match callee.target with
    | Function { path; _ } -> Some path
    | Trait_method { trait; name; receiver; evidence; self_type; _ } -> (
        match Interface.Impls.resolve_evidence lookups substitution ~self_type ~trait evidence with
        | Impl { impl; _ } -> Some (Method { owner = impl; name; receiver })
        | Bound -> Some (Method { owner = trait.trait; name; receiver }))
    | Capability_method { capability; name } -> Some (Path.make_capability_method capability name)
    | Intrinsic _ | Indirect _ -> None
  in
  Option.bind path (fun path ->
      Option.bind (Interface.Impls.read_signature lookups path) (fun signature ->
          Types.list_modified_fields signature position))

let make_code tree : Parts.code = { tree; graph = Expansion.expand tree }

let make_body_part ?interface (form : Core.t) : body_part =
  match form.definition with
  | Constant (Some value) -> Initializer (make_code (Builder.of_expression value))
  | definition -> (
      match
        Builder.of_definition
          ~is_specification:
            (Option.fold ~none:false ~some:Interface.Definition.is_specification interface)
          ~origin:form.origin definition
      with
      | Some tree -> Body (make_code tree)
      | None -> No_code)

let find_defaults (definition : Core.definition) =
  match definition with
  | Function { parameters; _ } ->
      Some
        (Parameter_defaults
           (List.concat
              (List.mapi
                 (fun position (parameter : Core.parameter) ->
                   match parameter.default with
                   | Some default -> [ (position, Builder.of_default default) ]
                   | None -> [])
                 parameters)))
  | Type { defaults; _ } ->
      Some
        (Field_defaults
           (List.map
              (fun (variant, field, (default : Core.expression)) ->
                { variant; field; type_ = default.type_; value = Builder.of_expression default })
              defaults))
  | Test _ | Law_proof _ -> Some (Parameter_defaults [])
  | Trait _ | Constant _ | Empty -> None

let find_local_name = Core_walk.find_local_name
let make_parameter ({ local; mode; type_; _ } : Core.parameter) : parameter = { local; mode; type_ }

let of_conditional_clause ~parameters ({ holds_when; clause } : Core.expression Core.conditional) =
  { (Builder.of_clause ~parameters clause) with holds_when }

let find_contract (definition : Core.definition) =
  match definition with
  | Function { parameters; contract; _ } ->
      Some
        {
          parameters = List.map make_parameter parameters;
          panics_unless =
            List.map
              (fun value ->
                {
                  clause = Builder.of_clause ~parameters value;
                  is_executable = false;
                  names = Builder.list_names value;
                })
              contract.panics_unless;
          requires =
            List.map
              (fun ({ holds_when; clause = written } : Core.condition Core.conditional) ->
                {
                  clause =
                    {
                      (Builder.of_clause ~is_executable:written.executable ~parameters written.value)
                      with
                      holds_when;
                    };
                  is_executable = written.executable;
                  names = Builder.list_names written.value;
                })
              contract.requires;
          ensures = List.map (of_conditional_clause ~parameters) contract.ensures;
          decreases = List.map (of_conditional_clause ~parameters) contract.decreases;
          costs =
            List.map
              (fun ({ holds_when; clause = { origin; amortized; resource; bound } } :
                     Core.cost Core.conditional) ->
                let bound : bound =
                  match bound with
                  | Order_of amount -> Order_of (Builder.of_clause ~parameters amount)
                  | At_most amount -> At_most (Builder.of_clause ~parameters amount)
                  | Exactly amount -> Exactly (Builder.of_clause ~parameters amount)
                in
                { origin; amortized; resource; bound; holds_when })
              contract.costs;
          callbacks =
            (let entry_locals =
               List.map (fun (parameter : Core.parameter) -> parameter.local) parameters
             in
             List.concat
               (List.mapi
                  (fun position (parameter : Core.parameter) ->
                    match parameter.callback_contract with
                    | Some { inputs; requires; ensures } ->
                        [
                          ( position,
                            {
                              inputs;
                              requires = List.map (Builder.of_specification ~entry_locals) requires;
                              ensures =
                                List.map
                                  (Builder.of_specification ~entry_locals:(entry_locals @ inputs))
                                  ensures;
                            } );
                        ]
                    | None -> [])
                  parameters));
        }
  | Test _ ->
      Some
        {
          parameters = [];
          panics_unless = [];
          requires = [];
          ensures = [];
          decreases = [];
          costs = [];
          callbacks = [];
        }
  | Type _ | Trait _ | Constant _ | Law_proof _ | Empty -> None

let list_laws (definition : Core.definition) =
  match definition with
  | Trait laws ->
      List.map
        (fun (law : Core.law) ->
          let entry_locals =
            List.map (fun (parameter : Core.parameter) -> parameter.local) law.parameters
          in
          {
            name = law.name;
            parameters =
              List.map
                (fun (parameter : Core.parameter) -> (parameter.local, parameter.type_))
                law.parameters;
            requires = List.map (Builder.of_specification ~entry_locals) law.requires;
            states = Builder.of_law_statement ~entry_locals ~origin:law.origin law.body;
          })
        laws
  | Function _ | Type _ | Constant _ | Test _ | Law_proof _ | Empty -> []

let find_type_clauses ~find_type_interface path (definition : Core.definition) =
  match definition with
  | Type { invariants; potential; _ } ->
      Option.map
        (fun (interface : Types.type_interface) ->
          let self : Core.parameter =
            {
              local = Self;
              mode = Read;
              type_ =
                Types.Named
                  { path; arguments = Types.list_generic_arguments interface.type_generics };
              default = None;
              callback_contract = None;
            }
          in
          {
            invariants =
              List.map
                (fun (invariant : Core.condition) ->
                  {
                    clause =
                      Builder.of_clause ~is_executable:invariant.executable ~parameters:[ self ]
                        invariant.value;
                    is_executable = invariant.executable;
                    names = Builder.list_names invariant.value;
                  })
                invariants;
            potential = Option.map (Builder.of_specification ~entry_locals:[]) potential;
          })
        (find_type_interface path)
  | Function _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> None

let expand_defaults = function
  | Parameter_defaults defaults ->
      Parameter_defaults
        (List.map (fun (position, default) -> (position, Expansion.expand default)) defaults)
  | Field_defaults defaults ->
      Field_defaults
        (List.map
           (fun (default : t field_default) ->
             { default with value = Expansion.expand default.value })
           defaults)

let make_contract_part ~find_type_interface path (form : Core.t) : contract_part =
  let defaults = find_defaults form.definition in
  {
    contract = find_contract form.definition;
    defaults;
    default_graphs = Option.map expand_defaults defaults;
    laws = list_laws form.definition;
    type_clauses = find_type_clauses ~find_type_interface path form.definition;
  }

let expand = Expansion.expand
