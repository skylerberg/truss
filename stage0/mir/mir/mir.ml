include Tree
module Graph = Graph
module Call_edges = Call_edges
include Walk
include Parts
open Builder
open Expansion

let code_of_formula = code_of_formula
let code_of tree : Parts.code = { tree; graph = expanded tree }

let body_part ?interface (form : Core.t) : body_part =
  match form.definition with
  | Constant (Some value) -> Initializer (code_of (of_expression value))
  | definition -> (
      match
        of_definition
          ~is_specification:
            (Option.fold ~none:false ~some:Interface.Environment.is_specification interface)
          definition
      with
      | Some tree -> Body (code_of tree)
      | None -> No_code)

let defaults_of (definition : Core.definition) =
  match definition with
  | Function { parameters; _ } ->
      Some
        (Parameter_defaults
           (List.concat
              (List.mapi
                 (fun position (parameter : Core.parameter) ->
                   match parameter.default with
                   | Some default -> [ (position, of_expression default) ]
                   | None -> [])
                 parameters)))
  | Type { defaults; _ } ->
      Some
        (Field_defaults
           (List.map
              (fun (variant, field, (default : Core.expression)) ->
                { variant; field; type_ = default.type_; value = of_expression default })
              defaults))
  | Test _ | Law_proof _ -> Some (Parameter_defaults [])
  | Trait _ | Constant _ | Empty -> None

let parameter ({ local; name; mode; type_; default; _ } : Core.parameter) : parameter =
  { local; name; mode; type_; has_default = default <> None }

let contract_of (definition : Core.definition) =
  match definition with
  | Function { parameters; contract; _ } ->
      Some
        {
          parameters = List.map parameter parameters;
          requires =
            List.map
              (fun (written : Core.condition) ->
                {
                  clause = of_clause ~is_executable:written.executable ~parameters written.value;
                  is_executable = written.executable;
                  names = names_of written.value;
                })
              contract.requires;
          ensures = List.map (of_clause ~parameters) contract.ensures;
          decreases = List.map (of_clause ~parameters) contract.decreases;
          costs =
            List.map
              (fun ({ origin; amortized; resource; bound } : Core.cost) ->
                let bound : bound =
                  match bound with
                  | Finite -> Finite
                  | Order_of amount -> Order_of (of_clause ~parameters amount)
                  | At_most amount -> At_most (of_clause ~parameters amount)
                  | Exactly amount -> Exactly (of_clause ~parameters amount)
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
                              requires = List.map (of_specification ~entry_locals) requires;
                            } );
                        ]
                    | None -> [])
                  parameters));
        }
  | Type _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> None

let laws_of (definition : Core.definition) =
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
            requires = List.map (of_specification ~entry_locals) law.requires;
            states = of_law_statement ~entry_locals law.body;
          })
        laws
  | Function _ | Type _ | Constant _ | Test _ | Law_proof _ | Empty -> []

let type_clauses_of ~type_interface path (definition : Core.definition) =
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
                Types.Named { path; arguments = Types.generic_arguments interface.type_generics };
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
                      of_clause ~is_executable:invariant.executable ~parameters:[ self ]
                        invariant.value;
                    is_executable = invariant.executable;
                    names = names_of invariant.value;
                  })
                invariants;
            potential = Option.map (of_specification ~entry_locals:[]) potential;
          })
        (type_interface path)
  | Function _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> None

let expanded_defaults = function
  | Parameter_defaults defaults ->
      Parameter_defaults
        (List.map (fun (position, default) -> (position, expanded default)) defaults)
  | Field_defaults defaults ->
      Field_defaults
        (List.map
           (fun (default : t field_default) -> { default with value = expanded default.value })
           defaults)

let contract_part ~type_interface path (form : Core.t) : contract_part =
  let defaults = defaults_of form.definition in
  {
    contract = contract_of form.definition;
    defaults;
    default_graphs = Option.map expanded_defaults defaults;
    laws = laws_of form.definition;
    type_clauses = type_clauses_of ~type_interface path form.definition;
  }

module For_testing = struct
  let expanded = expanded
end
