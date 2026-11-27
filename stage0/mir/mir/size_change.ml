type arc = { source : int; target : int; is_strict : bool }
type graph = arc list

type site = {
  origin : Core.origin;
  target : Path.t;
  graphs : graph list;
  passage : Catalog.Prover.passage;
}

type source = Parameter of int | Lambda_parameter of { code : int; lambda : int; position : int }
type bound = { limit : source; is_strict : bool }
type raw_arc = { from : source; into : int; is_strict_arc : bool }

module Locals = Map.Make (Int)

module Site_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.origin * Path.t
end))

module Lambda_table = Hashtbl.Make (Structural_key.Make (struct
  type t = int * int * int
end))

type recorded = { mutable raw_graphs : raw_arc list list; passage : Catalog.Prover.passage }

type walk = {
  lookups : Call_edges.lookups;
  instance : Types.substitution;
  recorded : recorded Site_table.t;
  lambda_alternatives : bound list list Lambda_table.t;
  code_number : int;
  lambdas : Tree.body array;
  scope : Tree.local_info array;
  count_codes : int ref;
}

let normalize (arcs : graph) =
  List.fold_left
    (fun merged (arc : arc) ->
      match merged with
      | (last : arc) :: rest when last.source = arc.source && last.target = arc.target ->
          { last with is_strict = last.is_strict || arc.is_strict } :: rest
      | _ -> arc :: merged)
    []
    (List.sort
       (fun (left : arc) (right : arc) ->
         compare (left.source, left.target) (right.source, right.target))
       arcs)
  |> List.rev

let strengthen bounds = List.map (fun (bound : bound) -> { bound with is_strict = true }) bounds

let relate_place state (place : Tree.place) =
  match place.root with
  | Local local ->
      let bounds = Option.value (Locals.find_opt local state) ~default:[] in
      if
        List.exists
          (function Tree.Field _ | Variant_field _ | Element _ -> true | Range _ -> false)
          place.projections
      then strengthen bounds
      else bounds
  | Constant _ | Literal _ -> []

let relate_operand state : Tree.operand -> bound list = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> relate_place state place
  | Immediate _ -> []

let relate_rvalue state : Tree.rvalue -> bound list = function
  | Operand value | Copy value | Convert { conversion = To_view; value; _ } ->
      relate_operand state value
  | Convert { conversion = Widen | To_integer | From_integer; _ }
  | Operation _ | Compare _ | Not _ | Construct _ | Array _ | Is_variant _ | Function_value _
  | Lambda _ | Value_parameter _ | Specification _ ->
      []

let assign state local bounds = Locals.add local bounds state
let forget state local = Locals.add local [] state

let find_root (place : Tree.place) =
  match place.root with Local local -> Some local | Constant _ | Literal _ -> None

let join_bounds left right =
  List.filter_map
    (fun (bound : bound) ->
      Option.map
        (fun (other : bound) -> { bound with is_strict = bound.is_strict && other.is_strict })
        (List.find_opt (fun (other : bound) -> other.limit = bound.limit) right))
    left

let join left right =
  match (left, right) with
  | None, state | state, None -> state
  | Some left, Some right ->
      Some
        (Locals.merge
           (fun _ left right ->
             match (left, right) with
             | Some left, Some right -> Some (join_bounds left right)
             | Some assigned, None | None, Some assigned -> Some assigned
             | None, None -> None)
           left right)

let list_mut_argument_places (call : Tree.call) =
  List.filter_map
    (fun (argument : Tree.argument) ->
      match (argument.mode, argument.value) with
      | _, Borrow { place; mode = Mut; _ } | Mut, (Use { place; _ } | Take { place; _ }) ->
          Some place
      | _ -> None)
    call.arguments

let list_written_places (statement : Tree.statement) : Tree.place list =
  let mut_borrow : Tree.operand -> Tree.place list = function
    | Borrow { place; mode = Mut; _ } -> [ place ]
    | Use _ | Borrow _ | Take _ | Immediate _ -> []
  in
  match statement.kind with
  | Basic (Assign { target; value = Operand value | Copy value | Convert { value; _ } }) ->
      target :: mut_borrow value
  | Basic (Assign { target; _ }) | Choose { target; _ } | Provide { target; _ } -> [ target ]
  | Basic (Call { destination; call }) -> Option.to_list destination @ list_mut_argument_places call
  | Basic (Lend { part; call }) ->
      { root = Local part; projections = [] } :: list_mut_argument_places call
  | Basic (Loan_start { borrowed; mode = Mut; _ }) -> (
      match borrowed with
      | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> [ place ]
      | Immediate _ -> [])
  | For { iteration = Pull { cursor; _ }; _ } -> [ cursor ]
  | Basic
      ( Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Proof _
      | Evaluated_assert _ )
  | For _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ | Jump _ ->
      []

let rec list_written_locals (block : Tree.block) =
  List.concat_map
    (fun statement ->
      List.filter_map find_root (list_written_places statement)
      @ List.concat_map list_written_locals (Walk.list_nested_blocks statement))
    block.statements

let forget_locals state locals = List.fold_left forget state locals

let record walk ~origin ~target ~passage raw_graphs =
  let key = (origin, target) in
  match Site_table.find_opt walk.recorded key with
  | Some recorded -> recorded.raw_graphs <- recorded.raw_graphs @ raw_graphs
  | None -> Site_table.replace walk.recorded key { raw_graphs; passage }

let find_owner (method_ : Path.t) = match method_ with Method { owner; _ } -> owner | _ -> method_

let make_arcs (bounds : bound list) into =
  List.map
    (fun (bound : bound) -> { from = bound.limit; into; is_strict_arc = bound.is_strict })
    bounds

let make_graphs (choices : (int * bound list list) list) =
  List.fold_left
    (fun graphs (position, alternatives) ->
      let alternatives = if alternatives = [] then [ [] ] else alternatives in
      List.concat_map
        (fun graph ->
          List.map (fun alternative -> graph @ make_arcs alternative position) alternatives)
        graphs)
    [ [] ] choices

let rec mentions parameter (ty : Types.ty) =
  match ty with
  | Parameter other -> other = parameter
  | Named { arguments; _ } -> List.exists (mentions_argument parameter) arguments
  | Projection { base; trait; _ } -> mentions parameter base || mentions_trait parameter trait
  | Function { inputs; output; _ } ->
      mentions parameter output || List.exists (fun (_, input) -> mentions parameter input) inputs
  | Never | Integer | Variable _ | Hole | Error _ -> false

and mentions_argument parameter : Types.argument -> bool = function
  | Type ty -> mentions parameter ty
  | Value _ -> false

and mentions_trait parameter (trait : Types.trait_reference) =
  List.exists (mentions_argument parameter) trait.trait_arguments
  || List.exists (fun (_, ty) -> mentions parameter ty) trait.associated

type occurrence = Absent | Whole | Within | Consumed | Out_of_reach of Types.ty

let combine left right =
  match (left, right) with
  | Out_of_reach ty, _ | _, Out_of_reach ty -> Out_of_reach ty
  | (Whole | Within), _ | _, (Whole | Within) -> Within
  | Consumed, _ | _, Consumed -> Consumed
  | Absent, Absent -> Absent

let enclose = function Whole -> Within | occurrence -> occurrence

let list_instance_fields (type_interface : Types.type_interface) arguments =
  List.map
    (fun (field : Types.field) -> field.field_type)
    (Option.value ~default:[] (Types.instantiate_fields type_interface arguments)
    @ List.concat_map
        (fun (variant : Types.variant) -> Option.value ~default:[] variant.fields)
        (Option.value ~default:[] (Types.instantiate_variants type_interface arguments)))

let rec classify interface ~parameter ~visiting (ty : Types.ty) =
  let ty = Types.strip_view ty in
  if not (mentions parameter ty) then Absent
  else
    match ty with
    | Parameter _ -> Whole
    | Named { path; arguments } -> (
        if Well_known.is_built_from_elements path then
          List.fold_left
            (fun occurrence (argument : Types.argument) ->
              match argument with
              | Type element ->
                  combine occurrence (enclose (classify interface ~parameter ~visiting element))
              | Value _ -> occurrence)
            Absent arguments
        else if List.exists (Path.equal path) visiting then Within
        else
          match Interface.Definition.find_type_interface interface path with
          | Some type_interface when not type_interface.opaque ->
              List.fold_left
                (fun occurrence field ->
                  combine occurrence
                    (enclose (classify interface ~parameter ~visiting:(path :: visiting) field)))
                Absent
                (list_instance_fields type_interface arguments)
          | Some _ | None -> Out_of_reach ty)
    | Function { output; _ } -> if mentions parameter output then Out_of_reach ty else Consumed
    | Projection _ | Never | Integer | Variable _ | Hole | Error _ -> Out_of_reach ty

let rec classify_holding interface ~heads ~visiting (ty : Types.ty) =
  let classify_each ~visiting types =
    List.fold_left
      (fun occurrence ty ->
        combine occurrence (enclose (classify_holding interface ~heads ~visiting ty)))
      Absent types
  in
  match Types.strip_view ty with
  | Named { path; _ } when List.exists (Path.equal path) heads -> Whole
  | Named { path; arguments } -> (
      let elements () =
        classify_each ~visiting
          (List.filter_map
             (function Types.Type element -> Some element | Value _ -> None)
             arguments)
      in
      if Well_known.is_built_from_elements path then elements ()
      else if List.exists (Path.equal path) visiting then Absent
      else
        match Interface.Definition.find_type_interface interface path with
        | Some type_interface ->
            classify_each ~visiting:(path :: visiting)
              (list_instance_fields type_interface arguments)
        | None -> ( match elements () with Absent -> Absent | _ -> Out_of_reach ty))
  | Function { inputs; output; _ } -> (
      match classify_holding interface ~heads ~visiting output with
      | Absent ->
          if
            List.exists
              (fun (_, input) -> classify_holding interface ~heads ~visiting input <> Absent)
              inputs
          then Consumed
          else Absent
      | Whole | Within | Consumed | Out_of_reach _ -> Out_of_reach ty)
  | Projection _ -> Out_of_reach ty
  | Parameter _ | Never | Integer | Variable _ | Hole | Error _ -> Absent

let classify_holding interface ~heads ty = classify_holding interface ~heads ~visiting:[] ty

let holds_itself interface (ty : Types.ty) =
  match Types.strip_view ty with
  | Named { path; arguments } -> (
      match Interface.Definition.find_type_interface interface path with
      | Some type_interface ->
          List.exists
            (fun field -> classify_holding interface ~heads:[ path ] field <> Absent)
            (list_instance_fields type_interface arguments)
      | None -> false)
  | _ -> false

let list_declared_types (signature : Types.signature) =
  (match signature.receiver with Some (_, ty) -> [ ty ] | None -> [])
  @ List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters

let find_trait_declaration (interface : Interface.Lookups.t) (method_ : Path.t) =
  match method_ with
  | Method { owner = Impl { trait = { path = trait; _ }; _ } | Derived { trait; _ }; name; _ }
  | Method { owner = Top _ as trait; name; _ } -> (
      match Interface.Definition.find_trait_interface interface trait with
      | Some trait_interface ->
          Option.map
            (fun (declared : Types.trait_method) ->
              (trait, Path.Method { owner = trait; name; receiver = declared.method_receiver }))
            (List.find_opt
               (fun (declared : Types.trait_method) -> declared.method_name = name)
               trait_interface.methods)
      | None -> None)
  | _ -> None

let list_self_positions interface method_ =
  match find_trait_declaration interface method_ with
  | Some (trait, declaration) -> (
      let self = Types.make_self_parameter trait in
      match Interface.Impls.read_signature interface declaration with
      | Some signature ->
          List.concat
            (List.mapi
               (fun position ty ->
                 match Types.strip_view ty with
                 | Parameter parameter when parameter = self -> [ position ]
                 | _ -> [])
               (list_declared_types signature))
      | None -> [])
  | None -> []

type resolved_operand = Result_value | Formula_parameter of int | Other

let rec find_assignment local (statements : Tree.statement list) =
  List.find_map
    (fun (statement : Tree.statement) ->
      match statement.kind with
      | Basic (Assign { target = { root = Local target; projections = [] }; value })
        when target = local ->
          Some (`Value value)
      | Choose { target = { root = Local target; projections = [] }; choice } when target = local ->
          Some (`Choice choice)
      | _ -> find_assignment_in_nested local statement)
    statements

and find_assignment_in_nested local statement =
  List.find_map
    (fun (block : Tree.block) -> find_assignment local block.statements)
    (Walk.list_nested_blocks statement)

let rec resolve_formula_local (formula : Tree.formula) statements local =
  match List.find_index (Int.equal local) formula.parameters with
  | Some position -> Formula_parameter position
  | None -> (
      match find_assignment local statements with
      | Some (`Value (Specification Result)) -> Result_value
      | Some (`Value (Specification (Entry entry))) ->
          resolve_formula_local formula statements entry
      | Some (`Value (Operand value | Copy value)) ->
          resolve_formula_operand formula statements value
      | Some _ | None -> Other)

and resolve_formula_operand formula statements (operand : Tree.operand) =
  match operand with
  | Use { place = { root = Local local; projections = [] }; _ }
  | Borrow { place = { root = Local local; projections = [] }; _ }
  | Take { place = { root = Local local; projections = [] }; _ } ->
      resolve_formula_local formula statements local
  | Use _ | Borrow _ | Take _ | Immediate _ -> Other

let rec list_identical_parameters (formula : Tree.formula) statements (operand : Tree.operand) =
  match operand with
  | Use { place = { root = Local local; projections = [] }; _ } -> (
      match find_assignment local statements with
      | Some (`Value (Specification (Identical (left, right)))) -> (
          match
            ( resolve_formula_operand formula statements left,
              resolve_formula_operand formula statements right )
          with
          | Result_value, Formula_parameter position | Formula_parameter position, Result_value ->
              Some [ position ]
          | _ -> None)
      | Some (`Value (Operand value | Copy value)) ->
          list_identical_parameters formula statements value
      | Some (`Choice (Connective { connective = Or; left; right })) -> (
          let read (block : Tree.block) =
            Option.bind block.value
              (list_identical_parameters formula (block.statements @ statements))
          in
          match (read left, read right) with
          | Some left, Some right -> Some (left @ right)
          | _ -> None)
      | Some _ | None -> None)
  | Use _ | Borrow _ | Take _ | Immediate _ -> None

let returns_one_of_its_arguments (lookups : Call_edges.lookups) declaration ~self_positions =
  match Parts.read_contract lookups.mir declaration with
  | Some { form = contract; _ } ->
      List.exists
        (fun (formula : Tree.formula) ->
          formula.holds_when = []
          &&
          match
            Option.bind formula.value.value
              (list_identical_parameters formula formula.value.statements)
          with
          | Some positions ->
              List.for_all (fun position -> List.mem position self_positions) positions
          | None -> false)
        contract.ensures
  | None -> false

let find_value_maker (lookups : Call_edges.lookups) (generics : Types.generic list) parameter =
  let interface = lookups.interface in
  let makes_values trait (declared : Types.trait_method) =
    let declaration =
      Path.Method
        { owner = trait; name = declared.method_name; receiver = declared.method_receiver }
    in
    let self = Types.make_self_parameter trait in
    match Interface.Impls.read_signature interface declaration with
    | None -> Some declaration
    | Some signature ->
        let result = match signature.output with Returns ty | Lends (_, ty) -> ty in
        let writes_self =
          List.exists
            (fun (parameter : Types.parameter_info) ->
              parameter.mode = Mut && mentions self parameter.type_)
            signature.parameters
          ||
          match signature.receiver with
          | Some (Mut, ty) -> mentions self ty
          | Some _ | None -> false
        in
        let self_positions = list_self_positions interface declaration in
        if writes_self then Some declaration
        else if
          mentions self result
          && not
               (Types.strip_view result = Parameter self
               && returns_one_of_its_arguments lookups declaration ~self_positions)
        then Some declaration
        else None
  in
  List.find_map
    (fun (generic : Types.generic) ->
      match generic.kind with
      | Type_generic bounds when generic.generic = parameter ->
          List.find_map
            (fun bound ->
              List.find_map
                (fun (reference : Types.trait_reference) ->
                  match Interface.Definition.find_trait_interface interface reference.trait with
                  | Some trait_interface ->
                      List.find_map (makes_values reference.trait) trait_interface.methods
                  | None -> Some reference.trait)
                (Interface.Properties.list_bound_closure interface ~self:(Parameter parameter) bound))
            bounds
      | Type_generic bounds ->
          List.find_map
            (fun (bound : Types.trait_reference) ->
              if mentions_trait parameter bound then Some bound.trait else None)
            bounds
      | Value_generic -> None)
    generics

let find_incomparable lookups (signature : Types.signature) (parameter : Types.parameter) :
    Catalog.Prover.incomparable option =
  match find_value_maker lookups signature.generics parameter with
  | Some maker -> Some (Makes_values { parameter = parameter.name; maker })
  | None ->
      List.find_map
        (fun ty : Catalog.Prover.incomparable option ->
          match classify lookups.interface ~parameter ~visiting:[] ty with
          | Out_of_reach type_ -> Some (Holds_out_of_reach { parameter = parameter.name; type_ })
          | Absent | Whole | Within | Consumed -> None)
        (list_declared_types signature)

let list_alternatives interface (signature : Types.signature) parameter
    (arguments : bound list list) =
  List.concat
    (List.mapi
       (fun position ty ->
         match (classify interface ~parameter ~visiting:[] ty, List.nth_opt arguments position) with
         | Whole, Some bounds -> [ bounds ]
         | Within, Some bounds -> [ strengthen bounds ]
         | (Whole | Within), None | (Absent | Consumed | Out_of_reach _), _ -> [])
       (list_declared_types signature))

let find_assumption_out_of_reach (lookups : Call_edges.lookups) (dictionary : Call_edges.dictionary)
    =
  let interface = lookups.interface in
  List.find_map
    (fun (assumption : Call_edges.assumption) ->
      let out_of_reach : Catalog.Prover.incomparable option =
        Some (Assumed_by_impl assumption.assumer)
      in
      match
        (assumption.parameter, Interface.Definition.find_impl_interface interface assumption.assumer)
      with
      | Some parameter, Some impl -> (
          if mentions_trait parameter impl.implements then out_of_reach
          else if find_value_maker lookups impl.impl_generics parameter <> None then out_of_reach
          else
            match classify interface ~parameter ~visiting:[] impl.for_type with
            | Within -> None
            | Absent | Whole | Consumed | Out_of_reach _ -> out_of_reach)
      | None, _ | _, None -> out_of_reach)
    dictionary.assumptions

let record_dictionary walk ~origin signature arguments (dictionary : Call_edges.dictionary) =
  let interface = walk.lookups.interface in
  let record_methods incomparable methods alternatives =
    List.iter
      (fun method_ ->
        record walk ~origin ~target:method_
          ~passage:(Dictionary { owner = find_owner method_; incomparable })
          (match incomparable with
          | Some _ -> [ [] ]
          | None ->
              make_graphs
                (List.map
                   (fun position -> (position, alternatives))
                   (list_self_positions interface method_))))
      methods
  in
  match find_incomparable walk.lookups signature dictionary.parameter with
  | Some _ as incomparable ->
      record_methods incomparable (Call_edges.list_dictionary_methods dictionary) []
  | None ->
      let alternatives = list_alternatives interface signature dictionary.parameter arguments in
      record_methods None dictionary.methods alternatives;
      record_methods
        (find_assumption_out_of_reach walk.lookups dictionary)
        dictionary.assumed_methods
        (List.map strengthen alternatives)

let find_function_inputs (ty : Types.ty) =
  match Types.strip_view ty with
  | Function { inputs; _ } -> List.map (fun (_, input) -> Types.strip_view input) inputs
  | _ -> []

let list_function_argument_alternatives walk (signature : Types.signature) arguments ty =
  List.map
    (fun (input : Types.ty) ->
      match input with
      | Parameter parameter
        when List.exists
               (fun (generic : Types.generic) -> generic.generic = parameter)
               signature.generics
             && Option.is_none (find_incomparable walk.lookups signature parameter) ->
          Some (list_alternatives walk.lookups.interface signature parameter arguments)
      | _ -> None)
    (find_function_inputs ty)

let record_function_arguments walk signature arguments (call : Tree.call) =
  let declared = list_declared_types signature in
  List.iteri
    (fun position (argument : Tree.argument) ->
      match (argument.function_, List.nth_opt declared position) with
      | Some (Lambda_expression { body; _ }), Some ty ->
          List.iteri
            (fun input alternatives ->
              Option.iter
                (fun alternatives ->
                  let key = (walk.code_number, body, input) in
                  Lambda_table.replace walk.lambda_alternatives key
                    (Option.value ~default:[] (Lambda_table.find_opt walk.lambda_alternatives key)
                    @ alternatives))
                alternatives)
            (list_function_argument_alternatives walk signature arguments ty)
      | Some (Function_reference { path; origin }), Some ty ->
          record walk ~origin ~target:path ~passage:(Function_value path)
            (make_graphs
               (List.filter_map
                  (fun (input, alternatives) ->
                    Option.map (fun alternatives -> (input, alternatives)) alternatives)
                  (List.mapi
                     (fun input alternatives -> (input, alternatives))
                     (list_function_argument_alternatives walk signature arguments ty))))
      | _ -> ())
    call.arguments

let record_call walk ~origin (callee : Tree.callee) arguments (call : Tree.call option) =
  let resolution = Call_edges.resolve_callee walk.lookups.interface walk.instance callee.target in
  Option.iter
    (fun target ->
      record walk ~origin ~target ~passage:Direct_call
        [ List.concat (List.mapi (fun position bounds -> make_arcs bounds position) arguments) ])
    resolution.target;
  let dictionaries = Lazy.force resolution.dictionaries in
  match Option.bind resolution.callee (Interface.Impls.read_signature walk.lookups.interface) with
  | Some signature ->
      List.iter (record_dictionary walk ~origin signature arguments) dictionaries;
      Option.iter (record_function_arguments walk signature arguments) call
  | None ->
      List.iter
        (fun dictionary ->
          List.iter
            (fun method_ ->
              record walk ~origin ~target:method_
                ~passage:(Dictionary { owner = find_owner method_; incomparable = None })
                [ [] ])
            (Call_edges.list_dictionary_methods dictionary))
        dictionaries

let rec walk_block walk state (block : Tree.block) =
  let state =
    List.fold_left
      (fun state statement ->
        match state with
        | Some state -> walk_statement walk state statement
        | None ->
            ignore (walk_statement walk Locals.empty statement);
            None)
      (Some state) block.statements
  in
  ( state,
    match (state, block.value) with Some state, Some value -> relate_operand state value | _ -> []
  )

and walk_choice walk state (choice : Tree.choice) =
  let ends =
    match choice with
    | Cases cases ->
        List.map
          (fun (case : Tree.case) ->
            let tested, _ = walk_block walk state case.tests in
            let guarded =
              match (tested, case.guard) with
              | Some tested, Some guard -> fst (walk_block walk tested guard)
              | _ -> tested
            in
            match guarded with
            | Some guarded -> walk_block walk guarded case.value
            | None -> (None, []))
          cases
    | Conditional { condition; then_; else_ } -> (
        match fst (walk_block walk state condition) with
        | Some tested -> [ walk_block walk tested then_; walk_block walk tested else_ ]
        | None -> [])
    | Connective { left; right; _ } -> (
        match walk_block walk state left with
        | (Some after_left, _) as left_end ->
            [ (fst left_end, []); (fst (walk_block walk after_left right), []) ]
        | (None, _) as left_end -> [ left_end ])
  in
  let joined_state = List.fold_left (fun joined (state, _) -> join joined state) None ends in
  let reached = List.filter (fun (state, _) -> Option.is_some state) ends in
  let value =
    match reached with
    | (_, first) :: rest ->
        List.fold_left (fun value (_, other) -> join_bounds value other) first rest
    | [] -> []
  in
  (joined_state, value)

and walk_lambda walk state body (captures : Tree.capture list) =
  let lambda = walk.lambdas.(body) in
  let walk = { walk with scope = lambda.locals } in
  let start =
    List.fold_left2
      (fun start local (capture : Tree.capture) ->
        assign start local (relate_place state capture.place))
      Locals.empty lambda.captures captures
  in
  let start =
    List.fold_left
      (fun start (position, local) ->
        assign start local
          [
            {
              limit = Lambda_parameter { code = walk.code_number; lambda = body; position };
              is_strict = false;
            };
          ])
      start
      (List.mapi (fun position local -> (position, local)) lambda.parameters)
  in
  ignore (walk_block walk start lambda.code)

and walk_nested_code walk state (code : Tree.t) =
  let nested =
    {
      walk with
      code_number = !(walk.count_codes);
      lambdas = code.lambdas;
      scope = code.body.locals;
    }
  in
  incr walk.count_codes;
  let relate_source source =
    match
      List.filter_map
        (fun local -> Locals.find_opt local state)
        (List.filter
           (fun local ->
             match walk.scope.(local).kind with
             | Source { local = candidate; _ } -> candidate = source
             | Temporary | Lent _ -> false)
           (List.init (Array.length walk.scope) Fun.id))
    with
    | first :: rest -> List.fold_left join_bounds first rest
    | [] -> []
  in
  let start =
    List.fold_left
      (fun start local ->
        match code.body.locals.(local).kind with
        | Source { local = source; _ } -> assign start local (relate_source source)
        | Temporary | Lent _ -> start)
      Locals.empty code.body.parameters
  in
  ignore (walk_block nested start code.body.code)

and walk_statement walk state (statement : Tree.statement) =
  let origin = Call_edges.locate_call statement in
  let forget_written state =
    List.fold_left
      (fun state place ->
        match find_root place with Some local -> forget state local | None -> state)
      state (list_written_places statement)
  in
  let relate_arguments (call : Tree.call) =
    List.map (fun (argument : Tree.argument) -> relate_operand state argument.value) call.arguments
  in
  match statement.kind with
  | Basic (Assign { target; value }) ->
      (match value with
      | Lambda { body; captures; _ } -> walk_lambda walk state body captures
      | Specification (Quantified { matches; body; _ }) ->
          let matched = Option.value (fst (walk_block walk state matches)) ~default:state in
          ignore (walk_block walk matched body)
      | _ -> ());
      let bounds = relate_rvalue state value in
      let state = forget_written state in
      Some
        (match (target.root, target.projections) with
        | Local local, [] -> assign state local bounds
        | _ -> state)
  | Basic (Call { call; _ } | Lend { call; _ }) ->
      record_call walk ~origin call.callee (relate_arguments call) (Some call);
      Some (forget_written state)
  | For { iteration; bindings; body; elements; _ } ->
      (match iteration with
      | Pull { cursor; next; _ } -> record_call walk ~origin next [ relate_place state cursor ] None
      | Range _ -> ());
      let looping =
        forget_locals (forget_written state)
          (list_written_locals bindings @ list_written_locals body
          @ Option.fold ~none:[]
              ~some:(fun (elements : Tree.elements) -> list_written_locals elements.count)
              elements)
      in
      Option.iter
        (fun (elements : Tree.elements) -> ignore (walk_block walk looping elements.count))
        elements;
      (match fst (walk_block walk looping bindings) with
      | Some bound -> ignore (walk_block walk bound body)
      | None -> ());
      Some looping
  | While { condition; body; failed; _ } ->
      let looping =
        forget_locals state
          (list_written_locals condition @ list_written_locals body
          @ list_written_locals { statements = failed; value = None })
      in
      (match fst (walk_block walk looping condition) with
      | Some tested -> ignore (walk_block walk tested body)
      | None -> ());
      ignore (walk_block walk looping { statements = failed; value = None });
      Some looping
  | Choose { target; choice } -> (
      let joined, value = walk_choice walk state choice in
      match joined with
      | Some joined ->
          Some
            (match (target.root, target.projections) with
            | Local local, [] -> assign joined local value
            | _ -> forget_written joined)
      | None -> None)
  | Fork { branches; _ } ->
      List.fold_left
        (fun joined branch -> join joined (fst (walk_block walk state branch)))
        None branches
  | Provide { body; _ } -> Option.map forget_written (fst (walk_block walk state body))
  | Resume { exits; _ } ->
      List.fold_left
        (fun joined (exit : Tree.early_exit) ->
          join joined (fst (walk_block walk state exit.resumed)))
        None exits
  | Assert_by_bit_vector { code; _ } -> fst (walk_block walk state code)
  | Basic (Proof code | Evaluated_assert code) ->
      walk_nested_code walk state code;
      Some state
  | Basic (Ghost_assert _) -> Some state
  | Basic (Live _ | Dead _ | Assert _ | Echo _ | Loan_end _ | Loan_start _) ->
      Some (forget_written state)
  | Yield _ -> Some state
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo) -> None

let rec expand_graph walk ~depth (raw : raw_arc list) : graph list =
  let lambda_sources =
    List.sort_uniq compare
      (List.filter_map
         (fun arc ->
           match arc.from with
           | Lambda_parameter { code; lambda; position } -> Some (code, lambda, position)
           | Parameter _ -> None)
         raw)
  in
  match lambda_sources with
  | [] ->
      [
        normalize
          (List.filter_map
             (fun arc ->
               match arc.from with
               | Parameter source ->
                   Some { source; target = arc.into; is_strict = arc.is_strict_arc }
               | Lambda_parameter _ -> None)
             raw);
      ]
  | key :: _ ->
      let alternatives =
        if depth > 4 then []
        else Option.value ~default:[] (Lambda_table.find_opt walk.lambda_alternatives key)
      in
      let substitute (alternative : bound list option) =
        List.concat_map
          (fun arc ->
            match arc.from with
            | Lambda_parameter { code; lambda; position } when (code, lambda, position) = key -> (
                match alternative with
                | Some bounds ->
                    List.map
                      (fun (bound : bound) ->
                        {
                          from = bound.limit;
                          into = arc.into;
                          is_strict_arc = arc.is_strict_arc || bound.is_strict;
                        })
                      bounds
                | None -> [])
            | _ -> [ arc ])
          raw
      in
      List.concat_map
        (fun alternative -> expand_graph walk ~depth:(depth + 1) (substitute alternative))
        (match alternatives with [] -> [ None ] | _ -> List.map Option.some alternatives)

let rec iter_called_statements visit (code : Tree.t) =
  Walk.iter_run_code
    (fun (statement : Tree.statement) ->
      visit statement;
      match statement.kind with
      | Basic (Proof nested | Evaluated_assert nested) -> iter_called_statements visit nested
      | _ -> ())
    code

let states_decreases (lookups : Call_edges.lookups) path =
  match Parts.read_contract lookups.mir path with
  | Some { form; _ } -> form.decreases <> []
  | None -> false

let list_sites (lookups : Call_edges.lookups) ~instance (code : Tree.t) =
  let walk =
    {
      lookups;
      instance;
      recorded = Site_table.create 16;
      lambda_alternatives = Lambda_table.create 4;
      code_number = 0;
      lambdas = code.lambdas;
      scope = code.body.locals;
      count_codes = ref 1;
    }
  in
  let start =
    List.fold_left
      (fun start (position, local) ->
        assign start local [ { limit = Parameter position; is_strict = false } ])
      Locals.empty
      (List.mapi (fun position local -> (position, local)) code.body.parameters)
  in
  ignore (walk_block walk start code.body.code);
  iter_called_statements
    (fun statement ->
      let origin = Call_edges.locate_call statement in
      let record_unrelated target passage =
        if not (Site_table.mem walk.recorded (origin, target)) then
          record walk ~origin ~target ~passage [ [] ]
      in
      List.iter
        (fun (edge : Call_edges.edge) ->
          match edge with
          | Calls target -> record_unrelated target Direct_call
          | Passes { argument = Dictionary; code } ->
              List.iter
                (fun target ->
                  record_unrelated target
                    (Dictionary { owner = find_owner target; incomparable = None }))
                code
          | Passes { argument = Function_value path; code } ->
              List.iter (fun target -> record_unrelated target (Function_value path)) code
          | Passes { argument = Handler; _ } -> ())
        (Call_edges.list_statement_edges lookups.interface walk.instance statement))
    code;
  Site_table.fold
    (fun (origin, target) (recorded : recorded) sites ->
      {
        origin;
        target;
        graphs =
          List.sort_uniq compare (List.concat_map (expand_graph walk ~depth:0) recorded.raw_graphs);
        passage = recorded.passage;
      }
      :: sites)
    walk.recorded []
  |> List.sort compare

let compose (first : graph) (second : graph) =
  normalize
    (List.concat_map
       (fun (left : arc) ->
         List.filter_map
           (fun (right : arc) ->
             if left.target = right.source then
               Some
                 {
                   source = left.source;
                   target = right.target;
                   is_strict = left.is_strict || right.is_strict;
                 }
             else None)
           second)
       first)

type call = {
  caller : Path.t;
  origin : Core.origin;
  callee : Path.t;
  passage : Catalog.Prover.passage;
}

module Closure_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * Path.t * graph
end))

module Path_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t
end))

let list_calls_without_decrease (nodes : (Path.t * site list) list) =
  let is_node path = List.exists (fun (node, _) -> Path.equal node path) nodes in
  let closure = Closure_table.create 64 in
  let leaving = Path_table.create 16 and entering = Path_table.create 16 in
  let pending = Queue.create () in
  let add source destination graph witness =
    let key = (source, destination, graph) in
    if not (Closure_table.mem closure key) then begin
      Closure_table.replace closure key witness;
      Path_table.add leaving source (destination, graph, witness);
      Path_table.add entering destination (source, graph, witness);
      Queue.add key pending
    end
  in
  List.iter
    (fun (caller, sites) ->
      List.iter
        (fun (site : site) ->
          if is_node site.target then
            List.iter
              (fun graph ->
                add caller site.target graph
                  [ { caller; origin = site.origin; callee = site.target; passage = site.passage } ])
              site.graphs)
        sites)
    nodes;
  while not (Queue.is_empty pending) do
    let ((source, destination, graph) as key) = Queue.pop pending in
    let witness = Closure_table.find closure key in
    List.iter
      (fun (next, second, more) -> add source next (compose graph second) (witness @ more))
      (Path_table.find_all leaving destination);
    List.iter
      (fun (previous, first, earlier) ->
        add previous destination (compose first graph) (earlier @ witness))
      (Path_table.find_all entering source)
  done;
  Closure_table.fold
    (fun (source, destination, graph) witness failing ->
      if
        Path.equal source destination
        && compose graph graph = graph
        && not (List.exists (fun arc -> arc.source = arc.target && arc.is_strict) graph)
      then witness @ failing
      else failing)
    closure []
  |> List.sort_uniq compare

type summary = { sites : site list; ranked_parameters : int list }

let is_ranked (ty : Types.ty) =
  match Types.strip_view ty with
  | Named _ as ty -> Option.is_none (Types.find_builtin ty)
  | _ -> false

let summarize (lookups : Call_edges.lookups) path =
  match Call_edges.find_code lookups path with
  | Some code when not (states_decreases lookups path) ->
      let instance = Call_edges.find_instance lookups path in
      {
        sites = list_sites lookups ~instance code;
        ranked_parameters =
          List.concat
            (List.mapi
               (fun position local ->
                 if is_ranked (Types.substitute instance code.body.locals.(local).type_) then
                   [ position ]
                 else [])
               code.body.parameters);
      }
  | Some _ | None -> { sites = []; ranked_parameters = [] }

type component = Level of int | Largest_rank of int list

type verdict = {
  calls_without_decrease : call list;
  ranking : (Path.t * component list) list option;
}

type constraint_ = { caller : Path.t; callee : Path.t; graph : graph }

let find_entry entries path =
  Option.map snd (List.find_opt (fun (key, _) -> Path.equal key path) entries)

let find_positions sets path = Option.value (find_entry sets path) ~default:[]

let has_arc ~is_strict (graph : graph) source target =
  List.exists
    (fun (arc : arc) ->
      arc.source = source && arc.target = target && (arc.is_strict || not is_strict))
    graph

let is_reached ~is_strict sets (decrease : constraint_) target =
  List.exists
    (fun source -> has_arc ~is_strict decrease.graph source target)
    (find_positions sets decrease.caller)

let rec keep_weakly_decreasing constraints sets =
  let kept =
    List.map
      (fun (path, positions) ->
        ( path,
          List.filter
            (fun target ->
              List.for_all
                (fun (decrease : constraint_) ->
                  (not (Path.equal decrease.callee path))
                  || is_reached ~is_strict:false sets decrease target)
                constraints)
            positions ))
      sets
  in
  if kept = sets then sets else keep_weakly_decreasing constraints kept

let decreases_strictly sets (decrease : constraint_) =
  match find_positions sets decrease.callee with
  | [] -> find_positions sets decrease.caller <> []
  | targets -> List.for_all (is_reached ~is_strict:true sets decrease) targets

let find_largest_ranks constraints ranked =
  let weak = keep_weakly_decreasing constraints ranked in
  let is_progress sets = List.exists (decreases_strictly sets) constraints in
  if is_progress weak then Some weak
  else
    List.find_map
      (fun (decrease : constraint_) ->
        let blocking =
          List.filter
            (fun target -> not (is_reached ~is_strict:true weak decrease target))
            (find_positions weak decrease.callee)
        in
        let sets =
          keep_weakly_decreasing constraints
            (List.map
               (fun (path, positions) ->
                 ( path,
                   if Path.equal path decrease.callee then
                     List.filter (fun position -> not (List.mem position blocking)) positions
                   else positions ))
               weak)
        in
        if is_progress sets then Some sets else None)
      constraints

let find_levels functions constraints =
  let levels = Path_table.create 16 in
  let rec find_level visiting path =
    match Path_table.find_opt levels path with
    | Some level -> Some level
    | None when List.exists (Path.equal path) visiting -> None
    | None ->
        let level =
          List.fold_left
            (fun level (decrease : constraint_) ->
              if Path.equal decrease.caller path then
                Option.bind level (fun level ->
                    Option.map
                      (fun below -> max level (below + 1))
                      (find_level (path :: visiting) decrease.callee))
              else level)
            (Some 0) constraints
        in
        Option.iter (Path_table.replace levels path) level;
        level
  in
  List.fold_right
    (fun path found ->
      Option.bind found (fun found ->
          Option.map (fun level -> (path, level) :: found) (find_level [] path)))
    functions (Some [])

let find_ranking (summaries : (Path.t * summary) list) =
  let functions = List.map fst summaries in
  let ranked = List.map (fun (path, summary) -> (path, summary.ranked_parameters)) summaries in
  let rec build constraints components =
    match find_levels functions constraints with
    | Some levels -> Some (List.rev (`Levels levels :: components))
    | None -> (
        match find_largest_ranks constraints ranked with
        | Some sets ->
            build
              (List.filter (fun decrease -> not (decreases_strictly sets decrease)) constraints)
              (`Largest sets :: components)
        | None -> None)
  in
  Option.map
    (fun components ->
      List.map
        (fun path ->
          ( path,
            List.map
              (function
                | `Levels levels -> Level (Option.value (find_entry levels path) ~default:0)
                | `Largest sets -> Largest_rank (find_positions sets path))
              components ))
        functions)
    (build
       (List.concat_map
          (fun (caller, summary) ->
            List.concat_map
              (fun (site : site) ->
                if List.exists (Path.equal site.target) functions then
                  List.map (fun graph -> { caller; callee = site.target; graph }) site.graphs
                else [])
              summary.sites)
          summaries)
       [])

let decide (summaries : (Path.t * summary) list) =
  let calls =
    list_calls_without_decrease (List.map (fun (path, summary) -> (path, summary.sites)) summaries)
  in
  let ranking = if calls = [] then find_ranking summaries else None in
  List.map
    (fun (path, _) ->
      ( path,
        {
          calls_without_decrease =
            List.filter (fun (call : call) -> Path.equal call.caller path) calls;
          ranking;
        } ))
    summaries
