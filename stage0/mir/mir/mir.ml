include Tree
module Graph = Graph
include Walk
open Builder
open Expansion

let code_of_formula = code_of_formula

let mir =
  Query.query ~name:"mir" ~phase:Phases.bodies ~show:Resolve.Names.show_key (fun database key ->
      match
        ( Query.demand database Infer.core key,
          Query.demand database Interface.Environment.lowered_interface key )
      with
      | Some form, Some lowered ->
          of_definition
            ~is_specification:(Interface.Environment.is_specification lowered.interface)
            form.definition
      | _ -> None)

let is_lowered database key = Option.is_some (Query.demand database Infer.core key)

let by_form_origin database path ~of_written ~of_generated =
  Option.bind (Query.demand database Infer.form_origin path) (fun (origin, _) ->
      match origin with
      | Infer.Written key | Inherited key -> Query.demand database of_written key
      | Generated ->
          Option.bind (Query.demand database Infer.derived path) (fun (form : Core.t) ->
              of_generated form.definition))

let of_path =
  Query.query ~name:"mir_of_path" ~phase:Phases.bodies ~show:Path.show (fun database path ->
      by_form_origin database path ~of_written:mir ~of_generated:of_definition)

let graph =
  Query.query ~name:"mir_graph" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key -> Option.map expanded (Query.demand database mir key))

let graph_of_path =
  Query.query ~name:"mir_graph_of_path" ~phase:Phases.bodies ~show:Path.show (fun database path ->
      by_form_origin database path ~of_written:graph ~of_generated:(fun definition ->
          Option.map expanded (of_definition definition)))

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

let defaults =
  Query.query ~name:"mir_defaults" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.bind (Query.demand database Infer.core key) (fun (form : Core.t) ->
          defaults_of form.definition))

let defaults_of_path =
  Query.query ~name:"mir_defaults_of_path" ~phase:Phases.bodies ~show:Path.show
    (fun database path ->
      by_form_origin database path ~of_written:defaults ~of_generated:defaults_of)

let default_graphs_of_path =
  Query.query ~name:"mir_default_graphs_of_path" ~phase:Phases.bodies ~show:Path.show
    (fun database path ->
      Option.map
        (function
          | Parameter_defaults defaults ->
              Parameter_defaults
                (List.map (fun (position, default) -> (position, expanded default)) defaults)
          | Field_defaults defaults ->
              Field_defaults
                (List.map
                   (fun (default : t field_default) ->
                     { default with value = expanded default.value })
                   defaults))
        (Query.demand database defaults_of_path path))

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

let contract =
  Query.query ~name:"mir_contract" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.bind (Query.demand database Infer.core key) (fun (form : Core.t) ->
          contract_of form.definition))

let contract_of_path =
  Query.query ~name:"mir_contract_of_path" ~phase:Phases.bodies ~show:Path.show
    (fun database path ->
      by_form_origin database path ~of_written:contract ~of_generated:contract_of)

let laws =
  Query.query ~name:"mir_laws" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      match Query.demand database Infer.core key with
      | Some { definition = Trait laws } ->
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
      | Some _ | None -> [])

let type_clauses_of_path =
  Query.query ~name:"mir_type_clauses_of_path" ~phase:Phases.bodies ~show:Path.show
    (fun database path ->
      match
        ( Query.demand database Infer.core_of_path path,
          Query.demand database Interface.Environment.type_interface path )
      with
      | Some ({ definition = Type { invariants; potential; _ }; _ }, _), Some interface ->
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
          Some
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
            }
      | _ -> None)

let is_generated database path =
  match Query.demand database Infer.form_origin path with
  | Some (Generated, _) -> true
  | Some ((Written _ | Inherited _), _) | None -> false

let of_constant =
  Query.query ~name:"mir_of_constant" ~phase:Phases.bodies ~show:Path.show (fun database path ->
      match Query.demand database Infer.core_of_path path with
      | Some ({ definition = Constant value; _ }, _) -> Some (of_expression value)
      | _ -> None)

let graph_of_constant =
  Query.query ~name:"mir_graph_of_constant" ~phase:Phases.bodies ~show:Path.show
    (fun database path -> Option.map expanded (Query.demand database of_constant path))

module For_testing = struct
  let expanded = expanded
end
