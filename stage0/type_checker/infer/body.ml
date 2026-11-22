type checked = {
  form : Core.t;
  tables : Tables.published;
  used_packages : Path.package list;
  places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
  requires_run_forever : bool;
}

let no_output : State.env =
  {
    output = None;
    specification = false;
    self = None;
    self_mode = Language.Mode.Read;
    loop_element = None;
    compile_time = false;
    in_quantifier = false;
  }

let constant_expression : State.env = { no_output with compile_time = true }

let check_body state (env : State.env) (written : Syntax.block) =
  let rec check_statements = function
    | [] -> (
        match env.output with
        | Some (Returns output) ->
            if not (State.unify state output Types.unit) then
              State.report state Mismatch
                (Source.Definition_span.make (State.read_span state written.id).stop
                   (State.read_span state written.id).stop)
                (Printf.sprintf "This body must end with a value of type `%s`."
                   (State.show state output))
        | _ -> ())
    | [ (last : Syntax.statement) ] ->
        Solver.run_in_statement state env (State.read_span state last.id) (fun () ->
            match (last.kind, env.output) with
            | Expression _, Some (Returns output) when State.resolve state output = Types.unit ->
                Statements.check_statement state env last ~last:false
            | Expression value, Some (Returns output) -> Expressions.check state env value output
            | Expression value, Some (Lends (_, part)) ->
                State.mark_lent_tails state value;
                Expressions.check state env value part
            | _, Some (Returns output) ->
                Statements.check_statement state env last ~last:true;
                if
                  not
                    (Statements.statement_diverges state last || State.unify state output Types.unit)
                then
                  State.report state Mismatch (State.read_span state last.id)
                    (Printf.sprintf "This body must end with a value of type `%s`."
                       (State.show state output))
            | _ -> Statements.check_statement state env last ~last:false)
    | (first : Syntax.statement) :: rest ->
        Solver.run_in_statement state env (State.read_span state first.id) (fun () ->
            Statements.check_statement state env first ~last:false);
        check_statements rest
  in
  Solver.run_in_statement state env (State.read_span state written.id) (fun () ->
      check_statements written.statements)

let declare_parameters state (written : Syntax.parameter list) (signature : Types.signature) =
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; _ } -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some info -> State.declare state name info.type_ ~binding:Parameter ~mode:info.mode
          | None -> ())
      | Self_parameter _ | Parameter_error -> ())
    written

let classify_self_mode (signature : Types.signature) =
  match signature.receiver with Some (mode, _) -> mode | None -> Language.Mode.Read

let check_clauses state env ~uses (clauses : Syntax.clause list) =
  List.iter
    (fun (clause : Syntax.clause) ->
      Clauses.check_under_condition state ~id:clause.id clause.condition (fun () ->
          match clause.kind with
          | Requires value | Ensures value -> Clauses.check_condition state env value
          | Decreases measures -> Clauses.check_measures state env measures
          | Cost cost ->
              Clauses.check_cost state env cost;
              if cost.resource = Metric Time then Clauses.check_time_terminates state clause ~uses
          | Uses uses ->
              List.iter
                (fun (use : Syntax.capability_use) ->
                  List.iter (Clauses.check_condition state env) use.unless_values)
                uses
          | Clause_error -> ()))
    clauses

let check_callback_contracts state env (written : Syntax.parameter list)
    (signature : Types.signature) =
  let env = { env with State.specification = true } in
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { inputs; clauses; _ }; _ }; _ }
        when List.for_all (fun (input : Syntax.function_input) -> Option.is_some input.name) inputs
             && List.exists
                  (fun (clause : Syntax.clause) ->
                    match clause.kind with Requires _ | Ensures _ -> true | _ -> false)
                  clauses -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some { type_ = Types.Function elaborated; _ } ->
              List.iter2
                (fun (input : Syntax.function_input) (mode, type_) ->
                  Option.iter
                    (fun input_name -> State.declare state input_name type_ ~binding:Let ~mode)
                    input.name)
                inputs elaborated.inputs;
              let check_clause env (value : Syntax.expression) =
                Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
                    Expressions.check state env value Types.bool)
              in
              List.iter
                (fun (clause : Syntax.clause) ->
                  match clause.kind with
                  | Requires value -> check_clause env value
                  | Ensures value ->
                      check_clause { env with output = Some (Returns elaborated.output) } value
                  | _ -> ())
                clauses
          | _ -> ())
      | _ -> ())
    written

let check_defaults state env (written : Syntax.parameter list) (signature : Types.signature) =
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; default; _ } -> (
          match
            ( List.find_opt
                (fun (info : Types.parameter_info) -> info.name = name.text)
                signature.parameters,
              default )
          with
          | Some info, Some value ->
              Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
                  let actual = Expressions.check_expression state env ~expected:info.type_ value in
                  Conversions.coerce state env ~argument:info.mode value ~actual
                    ~expected:info.type_);
              Constant.check state ~default:true value
          | Some { has_default = true; _ }, None ->
              State.raise_bug "`%s` has no default, and its signature has one" name.text
          | (Some _ | None), _ -> ())
      | Self_parameter _ | Parameter_error -> ())
    written

let check_function state ~broken_body (written : Syntax.signature)
    (body_block : Syntax.block option) (signature : Types.signature) =
  let env : State.env =
    {
      output = Some signature.output;
      specification = signature.specification_only;
      self = Option.map snd signature.receiver;
      self_mode = classify_self_mode signature;
      loop_element = None;
      compile_time = false;
      in_quantifier = false;
    }
  in
  declare_parameters state written.parameters signature;
  check_defaults state
    { constant_expression with specification = signature.specification_only }
    written.parameters signature;
  check_callback_contracts state env written.parameters signature;
  check_clauses state env ~uses:signature.uses written.clauses;
  match body_block with Some block when not broken_body -> check_body state env block | _ -> ()

let check_bit_vector_names state (form : Core.t) =
  let check_names (value : Core.expression) =
    Core_walk.walk_expression
      (Core_walk.make_deep_visitor
         {
           Core_walk.ignore_all with
           place =
             (function
             | Local { type_; origin; _ }
               when not (Types.is_builtin Bool type_ || Types.find_integer_range type_ <> None) ->
                 State.report state Not_bit_vector
                   (State.read_span state (Core_walk.locate_origin origin))
                   (Printf.sprintf
                      "An assertion `by bit_vector` can name only integers and booleans, and this \
                       is a `%s`."
                      (Types.show type_))
             | _ -> ());
         })
      value
  in
  Core_walk.walk_definition
    (Core_walk.make_deep_visitor
       {
         Core_walk.ignore_all with
         statement =
           (function
           | { kind = Assert { condition; by_bit_vector = true }; _ } -> check_names condition.value
           | _ -> ());
       })
    form.definition

let check_deserialized_invariants state (elaborated : Interface.Environment.elaborated_interface)
    (form : Core.t) =
  match (form.definition, elaborated.interface) with
  | Type { invariants; _ }, Type_interface interface
    when List.exists (Well_known.is Deserialize) interface.derives ->
      List.iter
        (fun (invariant : Core.condition) ->
          if not invariant.executable then
            State.report state Cannot_derive
              (State.read_span state (Core_walk.locate_origin invariant.value.origin))
              "This invariant cannot be checked at run time, so `serialization.Deserialize` cannot \
               be derived: a value read from data might break it. Write the `impl`, which checks \
               the value another way.")
        invariants
  | _ -> ()

let check_definition (state : State.state) (elaborated : Interface.Environment.elaborated_interface)
    ~checks_body =
  let definition = state.definition in
  let is_broken (part : Resolve.Parts.part) =
    Resolve.Names.is_broken state.lookups.interface.names state.key part
    || (part = Body && not checks_body)
  in
  let read_effective_signature () =
    match Interface.Impls.read_signature state.lookups.interface state.key.path with
    | Some signature -> signature
    | None -> State.raise_bug "a function with an interface has no signature"
  in
  if not (is_broken Header) then
    match (definition.kind, elaborated.interface) with
    | Function { signature; body = written }, Function_interface _ ->
        check_function state ~broken_body:(is_broken Body) signature (Some written)
          (read_effective_signature ())
    | Method_declaration signature, Function_interface _ ->
        check_function state ~broken_body:true signature None (read_effective_signature ())
    | Type_definition { body = type_body; clauses; _ }, Type_interface interface -> (
        let self =
          Types.Named
            {
              path = state.key.path;
              arguments = Types.list_generic_arguments interface.type_generics;
            }
        in
        let env : State.env = { no_output with specification = true; self = Some self } in
        List.iter
          (fun (clause : Syntax.type_clause) ->
            match clause.kind with
            | Type_invariant value ->
                Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
                    Expressions.check state env value Types.bool)
            | Potential value -> Clauses.check_integer state env value ~described:"A `potential`"
            | Derives _ -> ())
          clauses;
        let check_defaults (fields : Syntax.field list) (lowered_fields : Types.field list) =
          List.iter
            (fun (field : Syntax.field) ->
              match field.kind with
              | Field_declaration { name; default = Some value; _ } -> (
                  match
                    List.find_opt
                      (fun (elaborated : Types.field) -> elaborated.field_name = name.text)
                      lowered_fields
                  with
                  | Some elaborated ->
                      Solver.run_in_statement state constant_expression
                        (State.read_span state value.id) (fun () ->
                          Expressions.check state constant_expression value elaborated.field_type);
                      Constant.check state ~default:true value
                  | None -> ())
              | _ -> ())
            fields
        in
        match (type_body, interface.shape) with
        | Fields fields, Record lowered_fields -> check_defaults fields lowered_fields
        | Variants variants, Sum lowered_variants ->
            List.iter
              (fun (variant : Syntax.variant) ->
                match
                  ( variant.fields,
                    List.find_opt
                      (fun (elaborated : Types.variant) ->
                        elaborated.variant_name = variant.name.text)
                      lowered_variants )
                with
                | Some fields, Some { fields = Some lowered_fields; _ } ->
                    check_defaults fields lowered_fields
                | _ -> ())
              variants
        | _ -> ())
    | Trait { members; _ }, Trait_interface _ ->
        let self = Types.Parameter (Types.make_self_parameter state.key.path) in
        List.iteri
          (fun index (line : Syntax.trait_member Syntax.node) ->
            match line.kind with
            | Law law ->
                let env : State.env = { no_output with specification = true; self = Some self } in
                List.iter
                  (fun (parameter : Syntax.parameter) ->
                    match parameter.kind with
                    | Named_parameter { name; type_; _ } ->
                        State.declare state name
                          (Interface.Elaborator.elaborate_type (State.read_context state) type_)
                          ~binding:Let ~mode:Language.Mode.Read
                    | _ -> ())
                  law.parameters;
                List.iter
                  (fun (requirement : Syntax.expression) ->
                    Solver.run_in_statement state env (State.read_span state requirement.id)
                      (fun () -> Expressions.check state env requirement Types.bool))
                  law.requires;
                if not (is_broken (Member_body index)) then
                  check_body state { env with output = Some (Returns Types.bool) } law.body
            | Associated_type _ | Associated_capability _ | Trait_member_error -> ())
          members
    | Constant { type_; value; _ }, Constant_interface constant ->
        Constant.check_type state type_ constant.constant_type;
        if not (is_broken Body) then begin
          let env =
            {
              constant_expression with
              specification =
                Option.is_some (Types.find_specification_only_type constant.constant_type);
            }
          in
          Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
              Expressions.check state env value constant.constant_type);
          Constant.check state ~default:false value
        end
    | Test { body = written; _ }, _ ->
        if not (is_broken Body) then
          check_body state { no_output with output = Some (Returns Types.unit) } written
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        declare_parameters state parameters signature;
        let env : State.env =
          { no_output with specification = true; output = Some (Returns Types.unit) }
        in
        check_clauses state env ~uses:Types.no_capabilities clauses;
        if not (is_broken Body) then check_body state env written
    | Law_proof { body = written; _ }, _ ->
        if not (is_broken Body) then
          check_body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | _ -> ()

let list_used_packages (resolved : Resolve.resolved) ~evidence_packages (form : Core.t) =
  let named =
    List.filter_map
      (function
        | Some (Resolve.Definition (_, path) | Variant (path, _)) -> Some (Path.locate_package path)
        | Some (Module { module_; _ }) -> Some module_.package
        | _ -> None)
      (Array.to_list resolved.names)
  in
  let called = ref evidence_packages in
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      callee =
        (fun callee ->
          match callee.target with
          | Trait_method { trait; evidence; _ } ->
              called :=
                Path.locate_package trait.trait
                ::
                (match evidence with
                | Impl { impl; _ } -> [ Path.locate_package impl ]
                | _ -> [])
                @ !called
          | _ -> ());
    }
    form.definition;
  List.sort_uniq compare (named @ !called)

let list_law_parameters (lookups : Lookups.t) (interface : Interface.Environment.interface) =
  match interface with
  | Law_proof_interface { trait; law; for_type; _ } -> (
      match Interface.Definition.find_trait_interface lookups.interface trait.trait with
      | Some trait_interface ->
          let substitution =
            Types.make_trait_substitution trait_interface.trait_generics ~self:for_type trait
          in
          List.map
            (fun (name, type_) -> (name, Types.substitute substitution type_))
            (Option.value ~default:[] (List.assoc_opt law trait_interface.laws))
      | None -> [])
  | _ -> []

let check (lookups : Lookups.t) (key : Resolve.Names.key) ~checks_body =
  let resolved =
    Resolve.merge
      (List.map
         (fun section -> lookups.interface.read_resolved section key)
         (if checks_body then Resolve.sections else [ Interface; Contract ]))
  in
  let elaborated = lookups.interface.read_elaborated_interface key in
  let module_ = key.module_ in
  let definition = lookups.interface.names.read_definition key in
  let spans = lookups.interface.names.read_spans key in
  let context =
    Interface.Elaborator.create lookups.interface resolved ~spans
      (Interface.Impls.read_scope lookups.interface key)
  in
  let text = lazy (lookups.interface.names.read_text key) in
  let state : State.state =
    {
      lookups;
      key;
      package = module_.package;
      definition;
      resolved;
      text;
      tables = Tables.create (definition.id + 1);
      diagnostics = [];
      unifier =
        Unify.create ~context ~list_rigid_members:(fun context rigid ->
            Interface.Properties.list_rigid_members lookups.interface
              ~list_bounds:(Interface.Elaborator.list_bounds context)
              rigid);
      locals = Hashtbl.create 32;
      law_parameters = list_law_parameters lookups elaborated.interface;
      frames = [];
      locals_read = [];
      keyword_modes = [];
      places_without_keyword = [];
      mode_keywords = [];
      yielded = Hashtbl.create 4;
      lent_tails = Hashtbl.create 4;
      lambdas = [];
      unsolved = None;
      capability_constraints = [];
      capability_solution = None;
      evidence_packages = [];
      final_type_checks = [];
      log = [];
      annotatable = Hashtbl.create 8;
      goals = [];
    }
  in
  Solver.run_in_statement state no_output (State.read_span state definition.id) (fun () ->
      check_definition state elaborated ~checks_body);
  List.iter (fun check -> check ()) (List.rev state.final_type_checks);
  state.diagnostics <- Interface.Elaborator.list_diagnostics context @ state.diagnostics;
  state.diagnostics <-
    Interface.Check.list_bound_diagnostics lookups.interface ~package:state.package
      ~list_bounds:(State.lookup_bounds state) ~spans
      (Interface.Elaborator.list_named_types context)
    @ state.diagnostics;
  let finalize () =
    Tables.map ~map_type:(State.finalize_type state) ~map_argument:(State.finalize_argument state)
      ~map_capabilities:(State.finalize_capabilities state)
      state.tables
  in
  let tables = finalize () in
  Exported_parts.check state;
  let is_clean tables =
    state.diagnostics = []
    && (not (Resolve.Names.is_broken lookups.interface.names key Header))
    && (not (checks_body && Resolve.Names.is_broken lookups.interface.names key Body))
    && not (Tables.exists_type Types.is_error tables)
  in
  let build tables =
    Form.build lookups ~resolved ~tables ~context ~package:state.package ~text ~key ~definition
      ~elaborated ~law_parameters:state.law_parameters ~checks_body
  in
  let checked = if is_clean tables then Some (build tables) else None in
  let requires_run_forever =
    match checked with
    | Some form ->
        check_bit_vector_names state form;
        let requires_run_forever = Capabilities.check state elaborated form in
        check_deserialized_invariants state elaborated form;
        Some requires_run_forever
    | None ->
        state.capability_solution <- Some (Hashtbl.create 1);
        None
  in
  let has_capability_variables = state.unifier.capability_variable_count > 0 in
  let tables = if has_capability_variables then finalize () else tables in
  match (checked, requires_run_forever) with
  | Some form, Some requires_run_forever when is_clean tables ->
      let form = if has_capability_variables then build tables else form in
      Ok
        {
          form;
          tables = Tables.publish tables;
          used_packages =
            list_used_packages resolved ~evidence_packages:state.evidence_packages form;
          places_without_keyword = state.places_without_keyword;
          mode_keywords = state.mode_keywords;
          requires_run_forever;
        }
  | _ ->
      Error
        (List.sort_uniq
           (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
             compare (left.span, left.code, left.message) (right.span, right.code, right.message))
           state.diagnostics)
