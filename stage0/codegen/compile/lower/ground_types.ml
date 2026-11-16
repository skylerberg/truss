open Definitions

module Set = Set.Make (struct
  type t = Ground.ty

  let compare = Ground.compare
end)

let lowering_types =
  [
    Ground.builtin UInt8;
    Ground.builtin Int32;
    uint64;
    Ground.builtin Bool;
    Ground.builtin Unit;
    Ground.builtin Character;
    Ground.builtin Handle;
    Ground.Never;
    string_slice;
    Writing.output_ty;
    Storage.view_of_elements (Ground.builtin UInt8);
  ]

let is_runtime (ty : Types.ty) =
  (not (Types.contains_unsolved ty))
  && not
       (Types.exists
          (function Types.Integer | Error _ | Hole | Variable _ | Literal _ -> true | _ -> false)
          ty)

type walk = {
  context : context;
  mutable named : Ground.ty list;
  mutable constants : Path.t list;
  mutable walked : (Path.t * Ground.argument list) list;
}

let add walk ty = walk.named <- ty :: walk.named

let add_type walk substitution ty =
  if is_runtime ty then add walk (Monomorphic.ground walk.context.monomorphic substitution ty)

let ground_arguments walk substitution arguments =
  List.filter_map
    (function
      | Types.Type ty when not (is_runtime ty) -> None
      | argument ->
          Some (Monomorphic.ground_argument walk.context.monomorphic substitution argument))
    arguments

let add_arguments walk arguments =
  List.iter
    (function
      | Ground.Type ty ->
          add walk ty;
          add walk (Storage.of_elements ty);
          add walk (Storage.view_of_elements ty)
      | Value _ | Capabilities _ -> ())
    arguments

let signature_types ?(receiver = true) walk substitution (signature : Types.signature) =
  List.iter
    (fun (_, ty) -> add_type walk substitution ty)
    (interface_parameters (if receiver then signature else { signature with receiver = None }));
  match signature.output with Returns ty | Lends (_, ty) -> add_type walk substitution ty

let type_substitution walk (ty : Ground.ty) =
  match ty with
  | Named { path; arguments } -> (
      match Interface.Definition.type_interface walk.context.lookups.interface path with
      | Some interface -> Some (path, Monomorphic.substitution interface.type_generics arguments)
      | None -> None)
  | Function _ | Any _ | Never -> None

let member_type walk (ty : Ground.ty) (projection : Mir.projection) =
  let typed fields name =
    List.find_map
      (fun (field, (member : Memory_layout.member)) ->
        match member with Typed ty when field = name -> Some ty | Typed _ | Raw _ -> None)
      fields
  in
  match (Monomorphic.shape walk.context.monomorphic ty, projection) with
  | Record fields, Field name -> typed fields name
  | Sum variants, Variant_field { variant; field } ->
      List.find_map
        (fun (shape : Memory_layout.variant_shape) ->
          if shape.name = variant then typed shape.fields field else None)
        variants
  | _ -> None

let walk_capability_methods walk capability =
  match Interface.Definition.trait_interface walk.context.lookups.interface capability with
  | Some interface ->
      List.iter
        (fun (trait_method : Types.trait_method) ->
          signature_types ~receiver:false walk []
            (Interface.Definition.method_signature walk.context.lookups.interface ~owner:capability
               trait_method))
        interface.methods
  | None -> ()

let rec walk_graph walk substitution (graph : Mir.Graph.t) =
  walk_body walk substitution graph.body;
  Array.iter (walk_body walk substitution) graph.lambdas

and walk_body walk substitution (body : Mir.Graph.body) =
  Array.iter (fun (info : Mir.local_info) -> add_type walk substitution info.type_) body.locals;
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          walk_statement walk substitution body statement.kind)
        basic.statements;
      walk_terminator walk substitution basic.terminator)
    body.blocks

and walk_statement walk substitution body (basic : Mir.basic) =
  match basic with
  | Assign { target; value; _ } -> walk_rvalue walk substitution body target value
  | Call { call; _ } | Slice { call; _ } | Template { call; _ } -> walk_call walk substitution call
  | Lend { call; _ } ->
      walk_call walk substitution call;
      walk_forwarded walk substitution call
  | Assert { condition; _ } | Echo condition -> walk_operand walk substitution condition
  | Provide { provided; _ } ->
      List.iter
        (fun (provided : Mir.provided) ->
          add_type walk substitution provided.type_;
          walk_operand walk substitution provided.value)
        provided
  | Live _ | Dead _ | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _
    ->
      ()

and walk_terminator walk substitution (terminator : Mir.Graph.terminator) =
  (match terminator with
  | For _ | Fork _ -> walk_capability_methods walk (Well_known.path Tasks)
  | _ -> ());
  match terminator with
  | Branch { condition; _ } -> walk_operand walk substitution condition
  | For { iteration; _ } -> walk_iteration walk substitution iteration
  | Yield { part; _ } -> walk_yielded walk substitution part
  | Return operand -> Option.iter (walk_operand walk substitution) operand
  | Cancel { returned; _ } ->
      Option.iter (fun (operand, _) -> walk_operand walk substitution operand) returned
  | Goto _ | Fork _ | Join _ | Iteration_end _ | Resume _ | Unreachable | Written_unreachable | Todo
    ->
      ()

and walk_iteration walk substitution (iteration : Mir.iteration) =
  match iteration with
  | Range { start; stop; _ } ->
      walk_operand walk substitution start;
      walk_operand walk substitution stop
  | Pull { next; _ } -> walk_callee walk substitution next

and walk_yielded walk substitution (yielded : Mir.yielded) =
  match yielded with
  | Part operand -> walk_operand walk substitution operand
  | Built { fields; type_; _ } ->
      add_type walk substitution type_;
      List.iter (fun (_, field) -> Option.iter (walk_yielded walk substitution) field) fields

and walk_operand walk substitution (operand : Mir.operand) =
  add_type walk substitution (Mir.operand_type operand);
  match operand with
  | Use { place = { root = Constant path; _ }; _ }
  | Borrow { place = { root = Constant path; _ }; _ }
  | Take { place = { root = Constant path; _ }; _ } ->
      walk.constants <- path :: walk.constants;
      Option.iter (add_type walk [])
        (Interface.Definition.constant_type walk.context.lookups.interface path)
  | Use _ | Borrow _ | Take _ | Constant _ -> ()

and walk_rvalue walk substitution body (target : Mir.place) (value : Mir.rvalue) =
  match value with
  | Operand operand | Not operand | Copy operand -> walk_operand walk substitution operand
  | Operation { operation; type_arguments; operands } ->
      List.iter (walk_operand walk substitution) operands;
      walk_operation walk substitution operation type_arguments
  | Compare { left; right; _ } ->
      walk_operand walk substitution left;
      walk_operand walk substitution right
  | Construct { fields; variant } ->
      List.iter (fun (_, field) -> Option.iter (walk_operand walk substitution) field) fields;
      if List.exists (fun (_, field) -> Option.is_none field) fields then
        Option.iter
          (fun ty -> walk_field_defaults walk ty ~variant)
          (place_type walk substitution body target)
  | Array operands -> List.iter (walk_operand walk substitution) operands
  | Is_variant _ | Value_parameter _ | Specification _ -> ()
  | Convert { value; _ } | To_any { value; _ } -> walk_operand walk substitution value
  | Function_value { path; type_arguments; _ } ->
      walk_callee walk substitution (Function { path; type_arguments })
  | Lambda { captures; _ } ->
      List.iter (fun (capture : Mir.capture) -> add_type walk substitution capture.type_) captures

and place_type walk substitution (body : Mir.Graph.body) (place : Mir.place) =
  let root =
    match place.root with
    | Local local ->
        let ty = body.locals.(local).type_ in
        if is_runtime ty then Some (Monomorphic.ground walk.context.monomorphic substitution ty)
        else None
    | Constant path ->
        Option.map
          (Monomorphic.ground walk.context.monomorphic [])
          (Interface.Definition.constant_type walk.context.lookups.interface path)
  in
  List.fold_left
    (fun ty projection -> Option.bind ty (fun ty -> member_type walk ty projection))
    root place.projections

and walk_field_defaults walk ty ~variant =
  match type_substitution walk ty with
  | Some (path, substitution) -> (
      match Mir.default_graphs_of_path walk.context.lookups.mir path with
      | Some (Field_defaults defaults) ->
          List.iter
            (fun (default : Mir.Graph.t Mir.field_default) ->
              if default.variant = variant then begin
                add_type walk substitution default.type_;
                walk_graph walk substitution default.value
              end)
            defaults
      | Some (Parameter_defaults _) | None -> ())
  | None -> ()

and walk_operation walk substitution (operation : Intrinsic.operation) type_arguments =
  let arguments = ground_arguments walk substitution type_arguments in
  add_arguments walk arguments;
  match (operation, arguments) with
  | Holds_invariant, [ Type ty ] -> (
      match type_substitution walk ty with
      | Some (path, type_substitution) ->
          Option.iter
            (fun (clauses : Mir.type_clauses) ->
              List.iter
                (fun (requirement : Mir.requirement) ->
                  if requirement.is_executable then
                    walk_graph walk type_substitution (Mir.code_of_formula requirement.clause))
                clauses.invariants)
            (Mir.type_clauses_of_path walk.context.lookups.mir path)
      | None -> ())
  | Libc function_, _ ->
      let ground scalar : Ground.ty =
        Named { path = Intrinsic.builtin_path (Intrinsic.libc_builtin scalar); arguments = [] }
      in
      let { Libc.parameters; result; _ } = Libc.signature function_ in
      List.iter
        (fun (_, (passes : Libc.passes)) ->
          match passes with
          | Value scalar | Elements (scalar, _) | Room (scalar, _) | Elements_to_change (scalar, _)
            ->
              add_arguments walk [ Type (ground scalar) ]
          | Written (scalar, names) ->
              add walk
                (Named
                   {
                     path = Intrinsic.builtin_path Array;
                     arguments = [ Type (ground scalar); Value (Z.of_int (List.length names)) ];
                   })
          | Always _ | Fixed _ -> ())
        parameters;
      begin match result with
      | Returns scalar | Points_at scalar -> add_arguments walk [ Type (ground scalar) ]
      | Text | Never -> ()
      end
  | Shared_new, [ Type ty ] ->
      add walk (Named { path = Intrinsic.builtin_path Shared; arguments = [ Type ty ] })
  | _ -> ()

and walk_call walk substitution (call : Mir.call) =
  walk_callee walk substitution call.callee;
  List.iter
    (function
      | Mir.Passed { value; function_; _ } -> (
          walk_operand walk substitution value;
          match function_ with
          | Some (Lambda_expression { type_; _ }) -> add_type walk substitution type_
          | Some (Function_reference _) | None -> ())
      | Default -> ())
    call.arguments

and walk_callee walk substitution (callee : Mir.callee) =
  match callee with
  | Function _ | Trait_method _ -> (
      (match callee with
      | Trait_method { self_type; type_arguments; trait; _ } ->
          add_type walk substitution self_type;
          add_arguments walk (ground_arguments walk substitution type_arguments);
          add_arguments walk (ground_arguments walk substitution trait.trait_arguments)
      | _ -> ());
      match resolved_callee walk substitution callee with
      | Some (path, arguments) ->
          add_arguments walk arguments;
          walk_signature walk path arguments
      | None -> ())
  | Capability_method { capability; name } ->
      let _, signature = Targets.capability_method walk.context capability name in
      signature_types walk [] signature
  | Intrinsic { operation; type_arguments } ->
      walk_operation walk substitution operation type_arguments
  | Indirect operand -> walk_operand walk substitution operand

and resolved_callee walk substitution (callee : Mir.callee) =
  match callee with
  | Function { path; type_arguments } ->
      Some (path, ground_arguments walk substitution type_arguments)
  | Trait_method { evidence = Dynamic; _ } -> None
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match
        Targets.trait_method_key walk.context substitution ~trait ~name ~receiver ~self_type
          ~type_arguments ~evidence
      with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> None)
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

and walk_signature walk path arguments =
  match Interface.Impls.signature walk.context.lookups.interface path with
  | Some signature when List.length signature.generics = List.length arguments ->
      signature_types walk (bind signature.generics arguments) signature
  | Some _ | None -> ()

and walk_forwarded walk substitution (call : Mir.call) =
  match resolved_callee walk substitution call.callee with
  | Some (path, arguments) when Path.package path = Path.standard_package ->
      walk_code walk path arguments
  | Some _ | None -> ()

and walk_code walk path arguments =
  if not (List.mem (path, arguments) walk.walked) then begin
    walk.walked <- (path, arguments) :: walk.walked;
    match Mir.graph_of_path walk.context.lookups.mir path with
    | Some graph ->
        let code = code_of walk.context path arguments in
        walk_graph walk code.substitution graph;
        walk_defaults walk path code.substitution;
        add_result walk code.substitution code.result
    | None -> ()
  end

and walk_defaults walk path substitution =
  match Mir.default_graphs_of_path walk.context.lookups.mir path with
  | Some (Parameter_defaults defaults) ->
      List.iter (fun (_, graph) -> walk_graph walk substitution graph) defaults
  | Some (Field_defaults _) | None -> ()

and add_result walk substitution (result : Types.result) =
  match result with Returns ty | Lends (_, ty) -> add_type walk substitution ty

let rec folded_callees walk ~depth substitution (graph : Mir.Graph.t) =
  if depth > 0 then
    Array.iter
      (fun (basic : Mir.Graph.basic_block) ->
        List.iter
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Call { call = { callee = Function { path; type_arguments }; _ }; _ } -> (
                let arguments = ground_arguments walk substitution type_arguments in
                match Mir.graph_of_path walk.context.lookups.mir path with
                | Some callee when not (List.mem (path, arguments) walk.walked) ->
                    walk_code walk path arguments;
                    folded_callees walk ~depth:(depth - 1)
                      (code_of walk.context path arguments).substitution callee
                | Some _ | None -> ())
            | _ -> ())
          basic.statements)
      graph.body.blocks

let walk_constant walk path =
  Option.iter (add_type walk [])
    (Interface.Definition.constant_type walk.context.lookups.interface path);
  match Mir.initializer_graph_of_path walk.context.lookups.mir path with
  | Some graph ->
      walk_graph walk [] graph;
      folded_callees walk ~depth:Constants.call_depth [] graph
  | None -> ()

let walk_real walk capabilities =
  List.iter
    (fun capability ->
      match Generated.find_real_implementation walk.context.lookups.interface capability with
      | Some (_, impl_interface) -> (
          add_type walk [] impl_interface.for_type;
          match Monomorphic.ground walk.context.monomorphic [] impl_interface.for_type with
          | Named { path; _ } ->
              walk_signature walk (Method { owner = path; name = "new"; receiver = Static }) []
          | Function _ | Any _ | Never -> ())
      | None -> ())
    capabilities

let rec walk_key walk (key : Instance.key) =
  match key with
  | Code { path; type_arguments } ->
      add_arguments walk type_arguments;
      walk_signature walk path type_arguments;
      walk_code walk path type_arguments;
      walk_real walk (code_of walk.context path type_arguments).real
  | Constant path -> walk_constant walk path
  | Evaluator path ->
      walk_constant walk path;
      walk_signature walk Constants.write_fully []
  | Drop ty | Copy ty | Any_drop ty | Any_copy ty -> add walk ty
  | Debug ty ->
      add walk ty;
      List.iter (add walk) Debug_output.ground_types
  | Encode ty ->
      add walk ty;
      List.iter (add walk) Encoding.ground_types
  | Template_check { from_template; clauses; _ } ->
      walk_signature walk Constants.write_fully [];
      walk_signature walk from_template [];
      List.iter (walk_graph walk []) (template_clauses walk.context from_template clauses)
  | Call_evaluation { function_; _ } ->
      walk_signature walk Constants.write_fully [];
      walk_signature walk function_ []
  | Generated (Adapter { function_; type_arguments; ty }) ->
      add walk (Function ty);
      walk_key walk (Code { path = function_; type_arguments })
  | Generated (Entry ({ impl; name; type_arguments; _ } as impl_method)) ->
      walk_key walk (Instance.make_method_code impl_method);
      let interface = impl_interface walk.context impl in
      let substitution =
        bind (signature_of walk.context (Instance.make_method_path impl_method)).generics
          type_arguments
      in
      add_type walk substitution interface.for_type;
      let _, capability_signature =
        Targets.capability_method walk.context interface.implements.trait name
      in
      signature_types ~receiver:false walk [] capability_signature
  | Generated (Any_entry ({ impl; name; type_arguments; _ } as impl_method)) ->
      walk_key walk (Instance.make_method_code impl_method);
      walk_any_methods walk impl type_arguments ~only:(Some name)
  | Generated (Program_main path) ->
      walk_signature walk path [];
      walk_real walk
        (evidence_for walk.context []
           (Option.fold ~none:Types.no_capabilities
              ~some:(fun (signature : Types.signature) -> signature.uses)
              (Interface.Impls.signature walk.context.lookups.interface path)))
  | Generated (Locked_entry { capability; name }) ->
      let _, signature = Targets.capability_method walk.context capability name in
      signature_types ~receiver:false walk [] signature
  | Table (Impl_table { impl; _ }) ->
      walk_capability_methods walk (impl_interface walk.context impl).implements.trait
  | Table (Locked_table capability) -> walk_capability_methods walk capability
  | Table (Any_table { impl; type_arguments }) ->
      walk_any_methods walk impl type_arguments ~only:None

and walk_any_methods walk impl type_arguments ~only =
  let interface = impl_interface walk.context impl in
  let trait = interface.implements.trait in
  let substitution = bind interface.impl_generics type_arguments in
  add_type walk substitution interface.for_type;
  let any = Types.substitute_trait substitution interface.implements in
  let any_substitution = Targets.any_substitution walk.context ~any trait in
  List.iter
    (fun (trait_method : Types.trait_method) ->
      if Option.fold ~none:true ~some:(String.equal trait_method.method_name) only then
        signature_types ~receiver:false walk any_substitution
          (Interface.Definition.method_signature walk.context.lookups.interface ~owner:trait
             trait_method))
    (Targets.any_methods walk.context trait)

let rec reached context (ty : Ground.ty) =
  (match ty with
    | Function { parameters; result; _ } -> result :: List.map snd parameters
    | Any { arguments; associated; _ } ->
        List.filter_map (function Ground.Type ty -> Some ty | _ -> None) arguments
        @ List.map snd associated
    | Named { path; arguments = [ Type value ] } when Intrinsic.builtin_of_path path = Some Shared
      ->
        [ value ]
    | Named _ | Never -> [])
  @
  match Monomorphic.shape context.monomorphic ty with
  | shape -> Memory_layout.reaches shape
  | exception Monomorphic.Todo_type _ -> []

and closed context types =
  let rec visit seen = function
    | [] -> seen
    | ty :: rest ->
        if Set.mem ty seen then visit seen rest
        else visit (Set.add ty seen) (reached context ty @ rest)
  in
  Set.elements (visit Set.empty types)

type t = { types : Ground.ty list; folded_constants : Path.t list }

let of_instance context (key : Instance.key) =
  let walk = { context; named = []; constants = []; walked = [] } in
  walk_key walk key;
  {
    types = closed context (lowering_types @ walk.named);
    folded_constants =
      (match key with Constant _ -> List.sort_uniq Path.compare walk.constants | _ -> []);
  }
