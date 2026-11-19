type checked = {
  form : Core.t;
  tables : Tables.published;
  used_packages : Path.package list;
  places_without_keyword : (Core.origin * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
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

let list_clause_expressions (clauses : Syntax.clause list) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Requires value | Ensures value -> [ (value, `Bool) ]
      | Decreases measures -> List.map (fun measure -> (measure, `Cost_function)) measures
      | Cost { bound = Big_o value | At_most value | Exactly value; _ } ->
          [ (value, `Cost_function) ]
      | Uses _ | Clause_error -> [])
    clauses

let check_clauses state env (clauses : Syntax.clause list) =
  let env = { env with State.specification = true } in
  List.iter
    (fun (clause : Syntax.clause) ->
      match clause.kind with Cost cost -> State.check_cost state cost | _ -> ())
    clauses;
  List.iter
    (fun ((value : Syntax.expression), kind) ->
      Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
          match kind with
          | `Bool -> Expressions.check state env value Types.bool
          | `Cost_function -> ignore (Expressions.check_expression state env value)))
    (list_clause_expressions clauses)

let check_function_type_requires state env (written : Syntax.parameter list)
    (signature : Types.signature) =
  let env = { env with State.specification = true } in
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { inputs; clauses; _ }; _ }; _ }
        when List.exists (fun (input : Syntax.function_input) -> Option.is_some input.name) inputs
        -> (
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
              List.iter
                (fun (clause : Syntax.clause) ->
                  match clause.kind with
                  | Requires value ->
                      Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
                          Expressions.check state env value Types.bool)
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

let build_core_contract state (clauses : Syntax.clause list) : Core.contract =
  let collect_each choose =
    List.concat_map (fun (clause : Syntax.clause) -> choose clause.kind) clauses
  in
  let requires =
    collect_each (function
      | Requires value ->
          let value = State.build_expression state value in
          [ { Core.value; executable = Form.is_executable state value } ]
      | _ -> [])
  in
  let ensures =
    collect_each (function Ensures value -> [ State.build_expression state value ] | _ -> [])
  in
  let decreases =
    collect_each (function
      | Decreases measures -> List.map (State.build_expression state) measures
      | _ -> [])
  in
  {
    requires;
    ensures;
    decreases;
    costs =
      List.filter_map
        (fun (clause : Syntax.clause) ->
          match clause.kind with
          | Cost cost -> Some (Form.build_cost state ~origin:clause.id cost)
          | _ -> None)
        clauses;
  }

let build_core_parameters state (written : Syntax.parameter list) (signature : Types.signature) :
    Core.parameter list =
  List.filter_map
    (fun (parameter : Syntax.parameter) : Core.parameter option ->
      match parameter.kind with
      | Self_parameter _ ->
          Option.map
            (fun (mode, type_) : Core.parameter ->
              { local = Self; mode; type_; default = None; callback_contract = None })
            signature.receiver
      | Named_parameter { name; default; type_; _ } ->
          Option.map
            (fun (info : Types.parameter_info) : Core.parameter ->
              let default = Option.map (State.build_expression state) default in
              {
                local = Declared { origin = name.id; name = name.text };
                mode = info.mode;
                type_ = info.type_;
                default;
                callback_contract =
                  (match type_.kind with
                  | Function_type { inputs = _ :: _ as inputs; clauses; _ }
                    when List.for_all
                           (fun (input : Syntax.function_input) -> Option.is_some input.name)
                           inputs ->
                      Some
                        {
                          inputs =
                            List.filter_map
                              (fun (input : Syntax.function_input) ->
                                Option.map
                                  (fun (input_name : Syntax.name) : Core.local ->
                                    Declared { origin = input_name.id; name = input_name.text })
                                  input.name)
                              inputs;
                          requires =
                            List.filter_map
                              (fun (clause : Syntax.clause) ->
                                match clause.kind with
                                | Requires value -> Some (State.build_expression state value)
                                | _ -> None)
                              clauses;
                        }
                  | _ -> None);
              })
            (List.find_opt
               (fun (info : Types.parameter_info) -> info.name = name.text)
               signature.parameters)
      | Parameter_error -> None)
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
  check_function_type_requires state env written.parameters signature;
  check_clauses state env written.clauses;
  state.form.definition_builder <-
    Some
      (fun ~holds_body ->
        let parameters = build_core_parameters state written.parameters signature in
        let contract = build_core_contract state written.clauses in
        let body = if holds_body then Option.map (State.build_block state) body_block else None in
        let body =
          match signature.output with
          | Lends (mode, _) -> Option.map (Form.lend_block state mode) body
          | Returns _ -> body
        in
        Function { parameters; contract; body });
  match body_block with Some block when not broken_body -> check_body state env block | _ -> ()

let check_deserialized_invariants state (elaborated : Interface.Environment.elaborated_interface)
    (form : Core.t) =
  match (form.definition, elaborated.interface) with
  | Type { invariants; _ }, Type_interface interface
    when List.exists (Well_known.is Deserialize) interface.derives ->
      List.iter
        (fun (invariant : Core.condition) ->
          if not invariant.executable then
            State.report state Cannot_derive
              (State.read_span state invariant.value.origin)
              "This invariant cannot be checked at run time, so `serialization::Deserialize` \
               cannot be derived: a value read from data might break it. Write the `impl`, which \
               checks the value another way.")
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
            | Potential value ->
                Solver.run_in_statement state env (State.read_span state value.id) (fun () ->
                    ignore (Expressions.check_expression state env value))
            | Derives _ -> ())
          clauses;
        let list_defaulted variant (fields : Syntax.field list) =
          List.filter_map
            (fun (field : Syntax.field) ->
              match field.kind with
              | Field_declaration { name; default = Some value; _ } ->
                  Some (variant, name.text, value)
              | _ -> None)
            fields
        in
        state.form.definition_builder <-
          Some
            (fun ~holds_body:_ ->
              let defaults =
                List.map
                  (fun (variant, name, value) ->
                    (variant, name, State.build_expression state value))
                  (match type_body with
                  | Fields fields -> list_defaulted None fields
                  | Variants variants ->
                      List.concat_map
                        (fun (variant : Syntax.variant) ->
                          list_defaulted (Some variant.name.text)
                            (Option.value ~default:[] variant.fields))
                        variants
                  | Type_todo -> [])
              in
              let collect_clause choose =
                List.filter_map (fun (clause : Syntax.type_clause) -> choose clause.kind) clauses
              in
              Type
                {
                  defaults;
                  invariants =
                    collect_clause (function
                      | Type_invariant value ->
                          let value = State.build_expression state value in
                          Some { Core.value; executable = Form.is_executable state value }
                      | _ -> None);
                  potential =
                    (match
                       collect_clause (function
                         | Potential value -> Some (State.build_expression state value)
                         | _ -> None)
                     with
                    | first :: _ -> Some first
                    | [] -> None);
                });
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
        state.form.definition_builder <-
          Some
            (fun ~holds_body:_ ->
              Trait
                (List.concat
                   (List.mapi
                      (fun index (line : Syntax.trait_member Syntax.node) ->
                        match line.kind with
                        | Law law
                          when not (is_broken (Member_header index) || is_broken (Member_body index))
                          ->
                            let parameters =
                              List.filter_map
                                (fun (parameter : Syntax.parameter) : Core.parameter option ->
                                  match parameter.kind with
                                  | Named_parameter { name; _ } ->
                                      Some
                                        {
                                          local = Declared { origin = name.id; name = name.text };
                                          mode = Read;
                                          type_ = Form.read_local_type state name.id;
                                          default = None;
                                          callback_contract = None;
                                        }
                                  | _ -> None)
                                law.parameters
                            in
                            let requires = List.map (State.build_expression state) law.requires in
                            [
                              {
                                Core.name = law.name.text;
                                parameters;
                                requires;
                                body = State.build_block state law.body;
                              };
                            ]
                        | _ -> [])
                      members)));
        List.iteri
          (fun index (line : Syntax.trait_member Syntax.node) ->
            if not (is_broken (Member_header index)) then
              match line.kind with
              | Law law ->
                  let env : State.env = { no_output with specification = true; self = Some self } in
                  List.iter
                    (fun (parameter : Syntax.parameter) ->
                      match parameter.kind with
                      | Named_parameter { name; type_; _ } ->
                          State.declare state name
                            (Interface.Elaborator.elaborate_type state.context type_)
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
    | Constant { value; _ }, Constant_interface constant ->
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Constant (if holds_body then Some (State.build_expression state value) else None));
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
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Test (if holds_body then Some (State.build_block state written) else None));
        if not (is_broken Body) then
          check_body state { no_output with output = Some (Returns Types.unit) } written
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        declare_parameters state parameters signature;
        let env : State.env =
          { no_output with specification = true; output = Some (Returns Types.unit) }
        in
        check_clauses state env clauses;
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              let parameters = build_core_parameters state parameters signature in
              let contract = build_core_contract state clauses in
              Function
                {
                  parameters;
                  contract;
                  body = (if holds_body then Some (State.build_block state written) else None);
                });
        if not (is_broken Body) then check_body state env written
    | Law_proof { body = written; _ }, Law_proof_interface { trait; law; for_type; _ } ->
        (match Interface.Definition.find_trait_interface state.lookups.interface trait.trait with
        | Some interface ->
            let substitution =
              Types.make_trait_substitution interface.trait_generics ~self:for_type trait
            in
            state.law_parameters <-
              List.map
                (fun (name, type_) -> (name, Types.substitute substitution type_))
                (Option.value ~default:[] (List.assoc_opt law interface.laws))
        | None -> ());
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              let parameters =
                List.mapi
                  (fun index (name, type_) : Core.parameter ->
                    {
                      local = Trait_parameter { index; name };
                      mode = Read;
                      type_ = State.finalize_type state type_;
                      default = None;
                      callback_contract = None;
                    })
                  state.law_parameters
              in
              Law_proof
                {
                  parameters;
                  body = (if holds_body then Some (State.build_block state written) else None);
                });
        if not (is_broken Body) then
          check_body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | Law_proof { body = written; _ }, _ ->
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Law_proof
                {
                  parameters = [];
                  body = (if holds_body then Some (State.build_block state written) else None);
                });
        if not (is_broken Body) then
          check_body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | _ -> ()

let finalize (state : State.state) =
  let finalize_type = State.finalize_type state
  and finalize_argument = State.finalize_argument state
  and finalize_instantiation = State.finalize_instantiation state in
  let finalize_trait (reference : Types.trait_reference) =
    {
      reference with
      trait_arguments = List.map finalize_argument reference.trait_arguments;
      associated = List.map (fun (name, type_) -> (name, finalize_type type_)) reference.associated;
    }
  in
  let finalize_call (written : Tables.call) : Tables.call =
    {
      written with
      callee =
        (match written.callee with
        | Function { path; instantiation } ->
            Function { path; instantiation = finalize_instantiation instantiation }
        | Trait_method method_ ->
            Trait_method
              {
                method_ with
                trait = finalize_trait method_.trait;
                self_type = finalize_type method_.self_type;
                instantiation = finalize_instantiation method_.instantiation;
              }
        | Constructor constructor ->
            Constructor
              {
                constructor with
                type_arguments = List.map finalize_argument constructor.type_arguments;
              }
        | Intrinsic intrinsic ->
            Intrinsic
              {
                intrinsic with
                type_arguments = List.map finalize_argument intrinsic.type_arguments;
              }
        | other -> other);
      callee_result = finalize_type written.callee_result;
    }
  in
  let tables = state.tables in
  let update table transform =
    Array.iteri (fun index entry -> table.(index) <- Option.map transform entry) table
  in
  update tables.types finalize_type;
  update tables.local_types finalize_type;
  update tables.scrutinee_types finalize_type;
  update tables.calls finalize_call;
  update tables.resolutions (function
    | Tables.Global { path; instantiation } ->
        Tables.Global { path; instantiation = finalize_instantiation instantiation }
    | Field_access { type_; field } -> Field_access { type_ = finalize_type type_; field }
    | Variant_value { type_; variant } -> Variant_value { type_ = finalize_type type_; variant }
    | Type_name type_ -> Type_name (finalize_type type_)
    | other -> other);
  update tables.loops (function
    | Tables.Integer_range { element; inclusive } ->
        Tables.Integer_range { element = finalize_type element; inclusive }
    | Elements { count; element; lends } ->
        Elements { count = finalize_call count; element = finalize_call element; lends }
    | Pulled { cursor; cursor_call; remaining } ->
        Pulled
          {
            cursor = finalize_type cursor;
            cursor_call = Option.map finalize_call cursor_call;
            remaining = Option.map finalize_call remaining;
          });
  update tables.patterns (function
    | Tables.Variant_pattern { type_; variant } ->
        Tables.Variant_pattern { type_ = finalize_type type_; variant }
    | Record_pattern { type_ } -> Record_pattern { type_ = finalize_type type_ }
    | other -> other);
  update tables.templates (fun (template : Tables.template) ->
      {
        template with
        from_template = Option.map finalize_call template.from_template;
        part_conversions = List.map (Option.map finalize_call) template.part_conversions;
      })

let list_used_packages (resolved : Resolve.resolved) ~evidence_packages (form : Core.t) =
  let named =
    List.filter_map
      (function
        | Some (Resolve.Definition (_, path) | Variant (path, _)) -> Some (Path.locate_package path)
        | Some (Module module_) -> Some module_.package
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
      context;
      text;
      tables = Tables.create (definition.id + 1);
      form =
        {
          expression_builders = Array.make (definition.id + 1) None;
          statement_builders = Array.make (definition.id + 1) None;
          pattern_builders = Array.make (definition.id + 1) None;
          definition_builder = None;
          next_node_id = 0;
          next_synthetic_local = 0;
          tables_with_holes = None;
        };
      diagnostics = [];
      unifier =
        Unify.create ~list_rigid_members:(fun rigid ->
            Option.value ~default:[]
              (Types.find_bound_integer_implementors
                 (Interface.Properties.list_known_bounds lookups.interface
                    ~list_bounds:(Interface.Elaborator.list_bounds context)
                    rigid)));
      locals = Hashtbl.create 32;
      law_parameters = [];
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
      undecided = [];
      decisions = Hashtbl.create 4;
      annotatable = Hashtbl.create 8;
      narrowings = [];
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
  finalize state;
  Exported_parts.check state;
  let has_any_type is_unwanted =
    let contains table =
      Seq.exists
        (function
          | Some type_ ->
              let has_unwanted = ref false in
              ignore
                (Types.map
                   (fun part ->
                     if is_unwanted part then has_unwanted := true;
                     None)
                   type_);
              !has_unwanted
          | None -> false)
        (Array.to_seq table)
    in
    contains state.tables.types || contains state.tables.local_types
    || contains state.tables.scrutinee_types
  in
  let is_clean () =
    state.diagnostics = []
    && (not (Resolve.Names.is_broken lookups.interface.names key Header))
    && (not (checks_body && Resolve.Names.is_broken lookups.interface.names key Body))
    && not (has_any_type Types.is_error)
  in
  let build () : Core.t =
    state.form.next_node_id <- 0;
    state.form.next_synthetic_local <- 0;
    let checked = state.tables in
    if has_any_type (fun part -> part = Types.Hole) then begin
      state.form.tables_with_holes <- Some checked;
      state.tables <- Tables.copy checked;
      finalize state
    end;
    let definition =
      match state.form.definition_builder with
      | Some build -> build ~holds_body:checks_body
      | None -> Core.Empty
    in
    state.tables <- checked;
    state.form.tables_with_holes <- None;
    { definition }
  in
  let checked = if is_clean () then Some (build ()) else None in
  (match checked with
  | Some form ->
      Capabilities.check state elaborated form;
      check_deserialized_invariants state elaborated form
  | None -> state.capability_solution <- Some (Hashtbl.create 1));
  let has_capability_variables = state.unifier.capability_variable_count > 0 in
  if has_capability_variables then finalize state;
  match checked with
  | Some form when is_clean () ->
      let form = if has_capability_variables then build () else form in
      Ok
        {
          form;
          tables = Tables.publish state.tables;
          used_packages =
            list_used_packages resolved ~evidence_packages:state.evidence_packages form;
          places_without_keyword = state.places_without_keyword;
          mode_keywords = state.mode_keywords;
        }
  | _ ->
      Error
        (List.sort_uniq
           (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
             compare (left.span, left.code, left.message) (right.span, right.code, right.message))
           state.diagnostics)
