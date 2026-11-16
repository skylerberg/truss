open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower
open State
open Statements
open Expressions

type checked = { form : Core.t; tables : Tables.published; evidence_packages : Path.package list }

let no_output : env =
  {
    output = None;
    specification = false;
    self = None;
    self_mode = Types.Read;
    loop_element = None;
    compile_time = false;
    in_quantifier = false;
  }

let constant_expression : env = { no_output with compile_time = true }

let body state env (written : block) =
  let rec check_statements = function
    | [] -> (
        match env.output with
        | Some (Returns output) ->
            if not (unify state output Types.unit) then
              report state Mismatch
                (Source.Definition_span.make (read_span state written.id).stop
                   (read_span state written.id).stop)
                (Printf.sprintf "This body must end with a value of type `%s`." (show state output))
        | _ -> ())
    | [ (last : statement) ] ->
        in_statement state env (read_span state last.id) (fun () ->
            match (last.kind, env.output) with
            | Expression _, Some (Returns output) when resolve state output = Types.unit ->
                statement state env last ~last:false
            | Expression value, Some (Returns output) -> check state env value output
            | Expression value, Some (Lends (_, part)) ->
                mark_lent_tails state value;
                check state env value part
            | _, Some (Returns output) ->
                statement state env last ~last:true;
                if not (statement_diverges state last || unify state output Types.unit) then
                  report state Mismatch (read_span state last.id)
                    (Printf.sprintf "This body must end with a value of type `%s`."
                       (show state output))
            | _ -> statement state env last ~last:false)
    | (first : statement) :: rest ->
        in_statement state env (read_span state first.id) (fun () ->
            statement state env first ~last:false);
        check_statements rest
  in
  in_statement state env (read_span state written.id) (fun () ->
      check_statements written.statements)

let declare_parameters state (written : parameter list) (signature : Types.signature) =
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; _ } -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some info -> declare state name info.type_ ~is_var:false ~mode:info.mode
          | None -> ())
      | Self_parameter _ | Parameter_error -> ())
    written

let self_mode (signature : Types.signature) =
  match signature.receiver with
  | Some (Mut, _) -> Types.Mut
  | Some (Own, _) -> Types.Own
  | _ -> Types.Read

let clause_expressions (clauses : clause list) =
  List.concat_map
    (fun (clause : clause) ->
      match clause.kind with
      | Requires value | Ensures value -> [ (value, `Bool) ]
      | Decreases measures -> List.map (fun measure -> (measure, `Cost_function)) measures
      | Cost { bound = Big_o value | At_most value | Exactly value; _ } ->
          [ (value, `Cost_function) ]
      | Cost { bound = Finite; _ } | Uses _ | Clause_error -> [])
    clauses

let check_clauses state env (clauses : clause list) =
  let env = { env with specification = true } in
  List.iter
    (fun (clause : clause) ->
      match clause.kind with Cost { resource; _ } -> check_resource state resource | _ -> ())
    clauses;
  List.iter
    (fun ((value : expression), kind) ->
      in_statement state env (read_span state value.id) (fun () ->
          match kind with
          | `Bool -> check state env value Types.bool
          | `Cost_function -> ignore (expression state env value)))
    (clause_expressions clauses)

let check_function_type_requires state env (written : parameter list) (signature : Types.signature)
    =
  let env = { env with specification = true } in
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { inputs; clauses; _ }; _ }; _ }
        when List.exists (fun (input : function_input) -> Option.is_some input.name) inputs -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some { type_ = Types.Function lowered; _ } ->
              List.iter2
                (fun (input : function_input) (mode, type_) ->
                  Option.iter
                    (fun input_name -> declare state input_name type_ ~is_var:false ~mode)
                    input.name)
                inputs lowered.inputs;
              List.iter
                (fun (clause : clause) ->
                  match clause.kind with
                  | Requires value ->
                      in_statement state env (read_span state value.id) (fun () ->
                          check state env value Types.bool)
                  | _ -> ())
                clauses
          | _ -> ())
      | _ -> ())
    written

let check_defaults state env (written : parameter list) (signature : Types.signature) =
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; default = Some value; _ } -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some info ->
              in_statement state env (read_span state value.id) (fun () ->
                  let actual = expression state env ~expected:info.type_ value in
                  Name_lookup.coerce state env ~argument:info.mode value ~actual
                    ~expected:info.type_);
              Constant.check state ~default:true value
          | None -> ())
      | _ -> ())
    written

let core_contract state (clauses : clause list) : Core.contract =
  let each choose = List.concat_map (fun (clause : clause) -> choose clause.kind) clauses in
  let requires =
    each (function
      | Requires value ->
          let value = build_expression state value in
          [ { Core.value; executable = Form.is_executable state value } ]
      | _ -> [])
  in
  let ensures = each (function Ensures value -> [ build_expression state value ] | _ -> []) in
  let decreases =
    each (function Decreases measures -> List.map (build_expression state) measures | _ -> [])
  in
  {
    requires;
    ensures;
    decreases;
    costs =
      List.filter_map
        (fun (clause : clause) ->
          match clause.kind with
          | Cost cost -> Some (Form.build_cost state ~origin:clause.id cost)
          | _ -> None)
        clauses;
  }

let core_parameters state (written : parameter list) (signature : Types.signature) :
    Core.parameter list =
  List.filter_map
    (fun (parameter : parameter) : Core.parameter option ->
      match parameter.kind with
      | Self_parameter _ ->
          Option.map
            (fun ((receiver : Path.receiver), type_) : Core.parameter ->
              {
                local = Self;
                name = "self";
                mode = (match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read);
                type_;
                default = None;
                callback_contract = None;
              })
            signature.receiver
      | Named_parameter { name; default; type_; _ } ->
          Option.map
            (fun (info : Types.parameter_info) : Core.parameter ->
              let default = Option.map (build_expression state) default in
              {
                local = Named name.id;
                name = name.text;
                mode = info.mode;
                type_ = info.type_;
                default;
                callback_contract =
                  (match type_.kind with
                  | Function_type { inputs = _ :: _ as inputs; clauses; _ }
                    when List.for_all
                           (fun (input : function_input) -> Option.is_some input.name)
                           inputs ->
                      Some
                        {
                          inputs =
                            List.filter_map
                              (fun (input : function_input) ->
                                Option.map
                                  (fun (input_name : name) : (Core.local * string) ->
                                    (Named input_name.id, input_name.text))
                                  input.name)
                              inputs;
                          requires =
                            List.filter_map
                              (fun (clause : clause) ->
                                match clause.kind with
                                | Requires value -> Some (build_expression state value)
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

let check_function state ~broken_body (written : signature) (body_block : block option)
    (signature : Types.signature) =
  let env : env =
    {
      output = Some signature.output;
      specification = signature.specification_only;
      self = Option.map snd signature.receiver;
      self_mode = self_mode signature;
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
        let parameters = core_parameters state written.parameters signature in
        let contract = core_contract state written.clauses in
        let body = if holds_body then Option.map (build_block state) body_block else None in
        let body =
          match signature.output with
          | Lends (mode, _) -> Option.map (Form.lend_block state mode) body
          | Returns _ -> body
        in
        Function { parameters; contract; body });
  match body_block with Some block when not broken_body -> body state env block | _ -> ()

let check_deserialized_invariants state (lowered : Environment.lowered_interface) (form : Core.t) =
  match (form.definition, lowered.interface) with
  | Type { invariants; _ }, Type_interface interface
    when List.exists (Well_known.is Deserialize) interface.derives ->
      List.iter
        (fun (invariant : Core.condition) ->
          if not invariant.executable then
            report state Cannot_derive
              (read_span state invariant.value.origin)
              "This invariant cannot be checked at run time, so `serialization::Deserialize` \
               cannot be derived: a value read from data might break it. Write the `impl`, which \
               checks the value another way.")
        invariants
  | _ -> ()

let check_definition state (lowered : Environment.lowered_interface) ~checks_body =
  let definition = state.definition in
  let broken (part : Resolve.Parts.part) =
    Names.is_broken state.lookups.interface.names state.key part || (part = Body && not checks_body)
  in
  if not (broken Header) then
    match (definition.kind, lowered.interface) with
    | Function { signature; body = written }, Function_interface lowered_signature ->
        check_function state ~broken_body:(broken Body) signature (Some written) lowered_signature
    | Method_declaration signature, Function_interface lowered_signature ->
        check_function state ~broken_body:true signature None lowered_signature
    | Type_definition { body = type_body; clauses; _ }, Type_interface interface -> (
        let self =
          Types.Named
            { path = state.key.path; arguments = Types.generic_arguments interface.type_generics }
        in
        let env : env = { no_output with specification = true; self = Some self } in
        List.iter
          (fun (clause : type_clause) ->
            match clause.kind with
            | Type_invariant value ->
                in_statement state env (read_span state value.id) (fun () ->
                    check state env value Types.bool)
            | Potential value ->
                in_statement state env (read_span state value.id) (fun () ->
                    ignore (expression state env value))
            | Derives _ -> ())
          clauses;
        let defaulted variant (fields : field list) =
          List.filter_map
            (fun (field : field) ->
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
                  (fun (variant, name, value) -> (variant, name, build_expression state value))
                  (match type_body with
                  | Fields fields -> defaulted None fields
                  | Variants variants ->
                      List.concat_map
                        (fun (variant : variant) ->
                          defaulted (Some variant.name.text)
                            (Option.value ~default:[] variant.fields))
                        variants
                  | Type_todo -> [])
              in
              let clause choose =
                List.filter_map (fun (clause : type_clause) -> choose clause.kind) clauses
              in
              Type
                {
                  defaults;
                  invariants =
                    clause (function
                      | Type_invariant value ->
                          let value = build_expression state value in
                          Some { Core.value; executable = Form.is_executable state value }
                      | _ -> None);
                  potential =
                    (match
                       clause (function
                         | Potential value -> Some (build_expression state value)
                         | _ -> None)
                     with
                    | first :: _ -> Some first
                    | [] -> None);
                });
        let defaults (fields : field list) (lowered_fields : Types.field list) =
          List.iter
            (fun (field : field) ->
              match field.kind with
              | Field_declaration { name; default = Some value; _ } -> (
                  match
                    List.find_opt
                      (fun (lowered : Types.field) -> lowered.field_name = name.text)
                      lowered_fields
                  with
                  | Some lowered ->
                      in_statement state constant_expression (read_span state value.id) (fun () ->
                          check state constant_expression value lowered.field_type);
                      Constant.check state ~default:true value
                  | None -> ())
              | _ -> ())
            fields
        in
        match (type_body, interface.shape) with
        | Fields fields, Record lowered_fields -> defaults fields lowered_fields
        | Variants variants, Sum lowered_variants ->
            List.iter
              (fun (variant : variant) ->
                match
                  ( variant.fields,
                    List.find_opt
                      (fun (lowered : Types.variant) -> lowered.variant_name = variant.name.text)
                      lowered_variants )
                with
                | Some fields, Some { fields = Some lowered_fields; _ } ->
                    defaults fields lowered_fields
                | _ -> ())
              variants
        | _ -> ())
    | Trait { members; _ }, Trait_interface _ ->
        let self = Types.Parameter { owner = state.key.path; name = "Self" } in
        state.form.definition_builder <-
          Some
            (fun ~holds_body:_ ->
              Trait
                (List.concat
                   (List.mapi
                      (fun index (line : trait_member node) ->
                        match line.kind with
                        | Law law
                          when not (broken (Member_header index) || broken (Member_body index)) ->
                            let parameters =
                              List.filter_map
                                (fun (parameter : parameter) : Core.parameter option ->
                                  match parameter.kind with
                                  | Named_parameter { name; _ } ->
                                      Some
                                        {
                                          local = Named name.id;
                                          name = name.text;
                                          mode = Read;
                                          type_ = Form.read_local_type state name.id;
                                          default = None;
                                          callback_contract = None;
                                        }
                                  | _ -> None)
                                law.parameters
                            in
                            let requires = List.map (build_expression state) law.requires in
                            [
                              {
                                Core.name = law.name.text;
                                parameters;
                                requires;
                                body = build_block state law.body;
                              };
                            ]
                        | _ -> [])
                      members)));
        List.iteri
          (fun index (line : trait_member node) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Law law ->
                  let env : env = { no_output with specification = true; self = Some self } in
                  List.iter
                    (fun (parameter : parameter) ->
                      match parameter.kind with
                      | Named_parameter { name; type_; _ } ->
                          declare state name (Lower.type_ state.context type_) ~is_var:false
                            ~mode:Types.Read
                      | _ -> ())
                    law.parameters;
                  List.iter
                    (fun (requirement : expression) ->
                      in_statement state env (read_span state requirement.id) (fun () ->
                          check state env requirement Types.bool))
                    law.requires;
                  if not (broken (Member_body index)) then
                    body state { env with output = Some (Returns Types.bool) } law.body
              | Associated_type _ | Associated_capability _ | Trait_member_error -> ())
          members
    | Constant { value; _ }, Constant_interface constant ->
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Constant (if holds_body then Some (build_expression state value) else None));
        if not (broken Body) then begin
          let env =
            {
              constant_expression with
              specification =
                Option.is_some (Types.find_specification_only_type constant.constant_type);
            }
          in
          in_statement state env (read_span state value.id) (fun () ->
              check state env value constant.constant_type);
          Constant.check state ~default:false value
        end
    | Test { body = written; _ }, _ ->
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Test (if holds_body then Some (build_block state written) else None));
        if not (broken Body) then
          body state { no_output with output = Some (Returns Types.unit) } written
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        declare_parameters state parameters signature;
        let env : env =
          { no_output with specification = true; output = Some (Returns Types.unit) }
        in
        check_clauses state env clauses;
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              let parameters = core_parameters state parameters signature in
              let contract = core_contract state clauses in
              Function
                {
                  parameters;
                  contract;
                  body = (if holds_body then Some (build_block state written) else None);
                });
        if not (broken Body) then body state env written
    | Law_proof { body = written; _ }, Law_proof_interface { trait; law; for_type; _ } ->
        (match Interface.Definition.trait_interface state.lookups.interface trait.trait with
        | Some interface ->
            let substitution =
              Interface.Properties.trait_substitution interface ~self:for_type trait
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
                      local = Synthetic index;
                      name;
                      mode = Read;
                      type_ = final_type state type_;
                      default = None;
                      callback_contract = None;
                    })
                  state.law_parameters
              in
              state.form.next_synthetic_local <- List.length parameters;
              Law_proof
                {
                  parameters;
                  body = (if holds_body then Some (build_block state written) else None);
                });
        if not (broken Body) then
          body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | Law_proof { body = written; _ }, _ ->
        state.form.definition_builder <-
          Some
            (fun ~holds_body ->
              Law_proof
                {
                  parameters = [];
                  body = (if holds_body then Some (build_block state written) else None);
                });
        if not (broken Body) then
          body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | _ -> ()

let finalize (state : state) =
  let final_type = final_type state and argument = final_argument state in
  let trait (reference : Types.trait_reference) =
    {
      reference with
      trait_arguments = List.map argument reference.trait_arguments;
      associated = List.map (fun (name, type_) -> (name, final_type type_)) reference.associated;
    }
  in
  let evidence : Tables.evidence -> Tables.evidence = function
    | Impl { impl; arguments } ->
        Impl
          {
            impl;
            arguments = List.map (fun (parameter, value) -> (parameter, argument value)) arguments;
          }
    | other -> other
  in
  let call (written : Tables.call) : Tables.call =
    {
      written with
      callee =
        (match written.callee with
        | Function { path; type_arguments } ->
            Function { path; type_arguments = List.map argument type_arguments }
        | Trait_method method_ ->
            Trait_method
              {
                method_ with
                trait = trait method_.trait;
                self_type = final_type method_.self_type;
                type_arguments = List.map argument method_.type_arguments;
                evidence = evidence method_.evidence;
              }
        | Constructor constructor ->
            Constructor
              { constructor with type_arguments = List.map argument constructor.type_arguments }
        | Intrinsic intrinsic ->
            Intrinsic { intrinsic with type_arguments = List.map argument intrinsic.type_arguments }
        | other -> other);
      uses = final_capabilities state written.uses;
      callee_result = final_type written.callee_result;
    }
  in
  let tables = state.tables in
  let update table transform =
    Array.iteri (fun index entry -> table.(index) <- Option.map transform entry) table
  in
  update tables.types final_type;
  update tables.local_types final_type;
  update tables.scrutinee_types final_type;
  update tables.calls call;
  update tables.resolutions (function
    | Tables.Global { path; type_arguments } ->
        Tables.Global { path; type_arguments = List.map argument type_arguments }
    | Field_access { type_; field } -> Field_access { type_ = final_type type_; field }
    | Variant_value { type_; variant } -> Variant_value { type_ = final_type type_; variant }
    | Type_name type_ -> Type_name (final_type type_)
    | other -> other);
  update tables.loops (function
    | Tables.Integer_range { element; inclusive } ->
        Tables.Integer_range { element = final_type element; inclusive }
    | Elements { count; element; lends } ->
        Elements { count = call count; element = call element; lends }
    | Pulled { cursor; cursor_call; remaining } ->
        Pulled
          {
            cursor = final_type cursor;
            cursor_call = Option.map call cursor_call;
            remaining = Option.map call remaining;
          });
  update tables.patterns (function
    | Tables.Variant_pattern { type_; variant } ->
        Tables.Variant_pattern { type_ = final_type type_; variant }
    | Record_pattern { type_ } -> Record_pattern { type_ = final_type type_ }
    | other -> other);
  update tables.templates (fun (template : Tables.template) ->
      {
        template with
        from_template = Option.map call template.from_template;
        part_conversions = List.map (Option.map call) template.part_conversions;
      })

let integer_literal_range (bounds : Types.trait_reference list) =
  let signed = Intrinsic.[ Int8; Int16; Int32; Int64 ]
  and unsigned = Intrinsic.[ UInt8; UInt16; UInt32; UInt64 ] in
  let implementors =
    List.fold_left
      (fun found (bound : Types.trait_reference) ->
        let these =
          if Well_known.is Signed_integer bound.trait then Some signed
          else if Well_known.is Unsigned_integer bound.trait then Some unsigned
          else if Well_known.is Fixed_width_integer bound.trait then Some (signed @ unsigned)
          else None
        in
        match (found, these) with
        | Some found, Some these -> Some (List.filter (fun builtin -> List.mem builtin these) found)
        | None, these | these, None -> these)
      None bounds
  in
  Option.bind implementors (fun builtins ->
      List.fold_left
        (fun range builtin ->
          match (range, Types.integer_range (Types.builtin builtin)) with
          | Some (low, high), Some (other_low, other_high) ->
              Some (Z.max low other_low, Z.min high other_high)
          | None, found | found, None -> found)
        None builtins)

let check (lookups : Lookups.t) (key : Names.key) ~checks_body =
  match
    ( Resolve.whole
        ~sections:(if checks_body then Resolve.sections else [ Interface; Contract ])
        lookups.interface.resolved key,
      lookups.interface.lowered_interface key )
  with
  | Some resolved, Some lowered ->
      let module_ = key.module_ in
      let definition = lookups.interface.names.definition key in
      let spans = lookups.interface.names.spans key in
      let context = Interface.Lower.create lookups.interface resolved ~spans lowered.scope in
      let text = lazy (lookups.interface.names.text key) in
      let state : state =
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
          unifier = Unify.create ();
          locals = Hashtbl.create 32;
          law_parameters = [];
          frames = [];
          locals_read = [];
          receiver_modes = [];
          yielded = Hashtbl.create 4;
          lent_tails = Hashtbl.create 4;
          lambdas = [];
          unsolved = None;
          capability_constraints = [];
          capability_solution = None;
          evidence_packages = [];
          undecided = [];
          decisions = Hashtbl.create 4;
          annotatable = Hashtbl.create 8;
        }
      in
      state.unifier.integer_range <-
        (fun type_ ->
          integer_literal_range
            (Interface.Properties.known_bounds lookups.interface ~bounds:(bounds state) type_));
      check_definition state lowered ~checks_body;
      state.diagnostics <- !(context.diagnostics) @ state.diagnostics;
      state.diagnostics <-
        Interface.Check.bound_diagnostics lookups.interface ~package:state.package
          ~bounds:(bounds state) ~spans !(context.named)
        @ state.diagnostics;
      finalize state;
      Exported_parts.check state;
      let any_type unwanted =
        let contains table =
          Seq.exists
            (function
              | Some type_ ->
                  let has_unwanted = ref false in
                  ignore
                    (Types.map
                       (fun part ->
                         if unwanted part then has_unwanted := true;
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
        && (not (Names.is_broken lookups.interface.names key Header))
        && (not (checks_body && Names.is_broken lookups.interface.names key Body))
        && not (any_type Types.is_error)
      in
      let build () : Core.t =
        state.form.next_node_id <- 0;
        state.form.next_synthetic_local <- 0;
        let checked = state.tables in
        if any_type (fun part -> part = Types.Hole) then begin
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
          Capabilities.check state lowered form;
          check_deserialized_invariants state lowered form
      | None -> state.capability_solution <- Some (Hashtbl.create 1));
      let has_capability_variables = state.unifier.capability_variable_count > 0 in
      if has_capability_variables then finalize state;
      Some
        (match checked with
        | Some form when is_clean () ->
            Ok
              {
                form = (if has_capability_variables then build () else form);
                tables = Tables.publish state.tables;
                evidence_packages = List.sort_uniq compare state.evidence_packages;
              }
        | _ ->
            Error
              (List.sort_uniq
                 (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                   compare
                     (left.span, left.code, left.message)
                     (right.span, right.code, right.message))
                 state.diagnostics))
  | _ -> None
