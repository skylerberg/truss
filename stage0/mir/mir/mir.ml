include Tree
module Graph = Graph
module Call_edges = Call_edges
include Walk
include Parts

let expand_formula = Expansion.expand_formula
let make_code tree : Parts.code = { tree; graph = Expansion.expand tree }

let make_body_part ?interface (form : Core.t) : body_part =
  match form.definition with
  | Constant (Some value) -> Initializer (make_code (Builder.of_expression value))
  | definition -> (
      match
        Builder.of_definition
          ~is_specification:
            (Option.fold ~none:false ~some:Interface.Definition.is_specification interface)
          definition
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
                   | Some default -> [ (position, Builder.of_expression default) ]
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

let make_parameter ({ local; name; mode; type_; default; _ } : Core.parameter) : parameter =
  { local; name; mode; type_; has_default = default <> None }

let find_contract (definition : Core.definition) =
  match definition with
  | Function { parameters; contract; _ } ->
      Some
        {
          parameters = List.map make_parameter parameters;
          requires =
            List.map
              (fun (written : Core.condition) ->
                {
                  clause =
                    Builder.of_clause ~is_executable:written.executable ~parameters written.value;
                  is_executable = written.executable;
                  names = Builder.list_names written.value;
                })
              contract.requires;
          ensures = List.map (Builder.of_clause ~parameters) contract.ensures;
          decreases = List.map (Builder.of_clause ~parameters) contract.decreases;
          costs =
            List.map
              (fun ({ origin; amortized; resource; bound } : Core.cost) ->
                let bound : bound =
                  match bound with
                  | Finite -> Finite
                  | Order_of amount -> Order_of (Builder.of_clause ~parameters amount)
                  | At_most amount -> At_most (Builder.of_clause ~parameters amount)
                  | Exactly amount -> Exactly (Builder.of_clause ~parameters amount)
                in
                { origin; amortized; resource; bound })
              contract.costs;
          callbacks =
            (let entry_locals =
               List.map (fun (parameter : Core.parameter) -> parameter.local) parameters
             in
             List.concat
               (List.mapi
                  (fun position (parameter : Core.parameter) ->
                    match parameter.callback_contract with
                    | Some { inputs; requires } ->
                        [
                          ( position,
                            {
                              inputs;
                              requires = List.map (Builder.of_specification ~entry_locals) requires;
                            } );
                        ]
                    | None -> [])
                  parameters));
        }
  | Type _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> None

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
            states = Builder.of_law_statement ~entry_locals law.body;
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
              name = "self";
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

module For_testing = struct
  let expand = Expansion.expand
end
