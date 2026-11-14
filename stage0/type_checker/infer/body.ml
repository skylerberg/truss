(* Checks the bodies of a definition: a function's body, defaults, and
   clauses; a type's invariants, potential, and field defaults; a trait's
   default methods and laws; an [impl]'s methods; a constant's value; and
   the bodies of tests, theorems, and proofs. A part that did not parse is
   not checked. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower
open State
open Statements
open Expressions

type type_check_result = {
  tables : Tables.published;
  core : Core.t option;
      (** The definition's core form, when it parsed whole and nothing in it is an error. *)
  diagnostics : Syntax.diagnostic list;
  evidence : Path.package list;  (** The packages whose [impl]s met a bound in the definition *)
}

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

(* The environment of a constant expression: the value of a constant, or a
   default. *)
let constant_expression : env = { no_output with compile_time = true }

(* Checks a body. Types are inferred one statement at a time, and the last
   expression is checked against the result type. The body is a statement
   too, which gives each literal type that its statements leave undecided
   its default type. *)
let body state env (written : block) =
  let rec check_statements = function
    | [] -> (
        match env.output with
        | Some (Returns output) ->
            if not (unify state output Types.unit) then
              report state Mismatch
                (Span.make written.span.stop written.span.stop)
                (Printf.sprintf "This body must end with a value of type `%s`." (show state output))
        | _ -> ())
    | [ (last : statement) ] ->
        in_statement state env last.span (fun () ->
            match (last.kind, env.output) with
            | Expression _, Some (Returns output) when resolve state output = Types.unit ->
                (* The body of a function with no result ends with a
                   statement. Its value must be used or discarded, like the
                   value of any statement. *)
                statement state env last ~last:false
            | Expression value, Some (Returns output) -> check state env value output
            | Expression value, Some (Lends (_, part)) ->
                (* The value of a lending method's body is the part it lends. *)
                mark_lent_tails state value;
                check state env value part
            | _, Some (Returns output) ->
                statement state env last ~last:true;
                if not (statement_diverges state last || unify state output Types.unit) then
                  report state Mismatch last.span
                    (Printf.sprintf "This body must end with a value of type `%s`."
                       (show state output))
            | _ -> statement state env last ~last:false)
    | (first : statement) :: rest ->
        in_statement state env first.span (fun () -> statement state env first ~last:false);
        check_statements rest
  in
  in_statement state env written.span (fun () -> check_statements written.statements)

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
      in_statement state env value.span (fun () ->
          match kind with
          | `Bool -> check state env value Types.bool
          | `Cost_function -> ignore (expression state env value)))
    (clause_expressions clauses)

(* Checks the [requires] clauses of a function-typed parameter. They are
   specifications over the named inputs of the function type and the
   parameters declared before it. *)
let check_function_type_requires state env (written : parameter list) (signature : Types.signature)
    =
  let env = { env with specification = true } in
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { input_names; clauses; _ }; _ }; _ }
        when input_names <> [] -> (
          match
            List.find_opt
              (fun (info : Types.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some { type_ = Types.Function lowered; _ }
            when List.length lowered.inputs = List.length input_names ->
              List.iter2
                (fun (input : name) (mode, type_) -> declare state input type_ ~is_var:false ~mode)
                input_names lowered.inputs;
              List.iter
                (fun (clause : clause) ->
                  match clause.kind with
                  | Requires value ->
                      in_statement state env value.span (fun () -> check state env value Types.bool)
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
              (* A default is the argument of a call that leaves the
                 parameter out, so it converts as an argument does: an owned
                 collection becomes its view. *)
              in_statement state env value.span (fun () ->
                  let actual = expression state env ~expected:info.type_ value in
                  Lookups.coerce state env ~argument:info.mode value ~actual ~expected:info.type_);
              Constant.check state ~default:true value
          | None -> ())
      | _ -> ())
    written

(* The core form of a definition's parts *)

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
          | Cost cost -> Some (Form.cost state ~origin:clause.id cost)
          | _ -> None)
        clauses;
  }

(* The core parameters of a function: [self] first if there is one, each
   with the mode and the type from the signature. *)
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
                  | Function_type { input_names = _ :: _ as inputs; clauses; _ } ->
                      Some
                        {
                          inputs =
                            List.map
                              (fun (input : name) : (Core.local * string) ->
                                (Named input.id, input.text))
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
      (* The body of a function for specifications only is a specification:
         it has exact arithmetic, [==>], and quantifiers over types. *)
      specification = signature.specification_only;
      self = Option.map snd signature.receiver;
      self_mode = self_mode signature;
      loop_element = None;
      compile_time = false;
      in_quantifier = false;
    }
  in
  declare_parameters state written.parameters signature;
  check_defaults state constant_expression written.parameters signature;
  check_function_type_requires state env written.parameters signature;
  check_clauses state env written.clauses;
  state.form.definition_builder <-
    Some
      (fun () ->
        let parameters = core_parameters state written.parameters signature in
        let contract = core_contract state written.clauses in
        let body = Option.map (build_block state) body_block in
        let body =
          match signature.output with
          | Lends (mode, _) -> Option.map (Form.lend_block state mode) body
          | Returns _ -> body
        in
        Function { parameters; contract; body });
  match body_block with Some block when not broken_body -> body state env block | _ -> ()

let check_definition state (lowered : Environment.lowered_interface) =
  let definition = state.definition in
  let broken part = Resolve.Parts.broken definition part in
  if not (broken Header) then
    match (definition.kind, lowered.interface) with
    | Function { signature; body = written }, Function_interface lowered_signature ->
        check_function state ~broken_body:(broken Body) signature (Some written) lowered_signature
    (* A method without a body still has clauses, which are checked. *)
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
                in_statement state env value.span (fun () -> check state env value Types.bool)
            | Potential value ->
                in_statement state env value.span (fun () -> ignore (expression state env value))
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
            (fun () ->
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
                      | Type_invariant value -> Some (build_expression state value)
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
                      in_statement state constant_expression value.span (fun () ->
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
            (fun () ->
              Trait
                (List.concat
                   (List.mapi
                      (fun index (line : trait_member line) ->
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
                                          type_ = Form.local_type state name.id;
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
          (fun index (line : trait_member line) ->
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
                      in_statement state env requirement.span (fun () ->
                          check state env requirement Types.bool))
                    law.requires;
                  if not (broken (Member_body index)) then
                    body state { env with output = Some (Returns Types.bool) } law.body
              | Associated_type _ | Associated_capability _ | Trait_member_error -> ())
          members
    | Constant { value; _ }, Constant_interface constant ->
        if not (broken Body) then begin
          in_statement state constant_expression value.span (fun () ->
              check state constant_expression value constant.constant_type);
          state.form.definition_builder <- Some (fun () -> Constant (build_expression state value));
          Constant.check state ~default:false value
        end
    | Test { body = written; _ }, _ ->
        state.form.definition_builder <- Some (fun () -> Test (build_block state written));
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
            (fun () ->
              let parameters = core_parameters state parameters signature in
              let contract = core_contract state clauses in
              Function { parameters; contract; body = Some (build_block state written) });
        if not (broken Body) then body state env written
    | Law_proof { body = written; _ }, Law_proof_interface { trait; law; for_type; _ } ->
        (* The body names the law's parameters, as the law's own body does. *)
        (match Query.demand state.database Environment.trait_interface trait.trait with
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
            (fun () ->
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
              Law_proof { parameters; body = build_block state written });
        if not (broken Body) then
          body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | Law_proof { body = written; _ }, _ ->
        state.form.definition_builder <-
          Some (fun () -> Law_proof { parameters = []; body = build_block state written });
        if not (broken Body) then
          body state
            { no_output with specification = true; output = Some (Returns Types.unit) }
            written
    | _ -> ()

(* Replaces every type in the tables by its final form, so that they hold
   no inference variable. A variable that is still unsolved was reported,
   and becomes the error type. An entry recorded while a statement was
   checked, such as a call's type arguments, is final only after the
   statement's inference finished. *)
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
    | Pulled { cursor; made_by; remaining } ->
        Pulled
          {
            cursor = final_type cursor;
            made_by = Option.map call made_by;
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

(* The values an integer literal may have in a type that integer traits
   bound: those of every built-in type that implements each of them, the
   narrowest such type's. *)
let integer_literal_range (bounds : Types.trait_reference list) =
  let signed = Intrinsic.[ Int8; Int16; Int32; Int64; ISize ]
  and unsigned = Intrinsic.[ UInt8; UInt16; UInt32; UInt64; USize ] in
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

let check database (key : Names.key) =
  match
    (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
  with
  | Some definition, Some resolved ->
      (* The module comes from the definition's key. The definition's
         position in its file is not read, so a definition that only moved
         is not checked again. *)
      let module_ = key.module_ in
      let lowered, context = Environment.lower database key definition resolved in
      let text = Option.value ~default:"" (Query.demand database Names.text key) in
      let binding_spans = Hashtbl.create 64 in
      List.iter
        (fun (name : name) -> Hashtbl.replace binding_spans name.id name.span)
        (Syntax_walk.names definition);
      let state : state =
        {
          database;
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
          references = [];
          receiver_modes = [];
          yielded = Hashtbl.create 4;
          lent_tails = Hashtbl.create 4;
          binding_spans;
          lambdas = [];
          unsolved = None;
          capability_constraints = [];
          capability_solution = None;
          evidence = [];
          undecided = [];
          decisions = Hashtbl.create 4;
          annotatable = Hashtbl.create 8;
        }
      in
      (* Diagnostics about the types in the signature belong to the
         interface check. Only diagnostics about the types written in the
         body, and their bounds, are reported here. *)
      let interface_diagnostics = List.length !(context.diagnostics) in
      let interface_named = List.length !(context.named) in
      state.unifier.integer_range <-
        (fun type_ ->
          integer_literal_range
            (Interface.Properties.known_bounds database ~bounds:(bounds state) type_));
      check_definition state lowered;
      let since count list = List.filteri (fun index _ -> index < List.length list - count) list in
      state.diagnostics <- since interface_diagnostics !(context.diagnostics) @ state.diagnostics;
      state.diagnostics <-
        Interface.Check.bound_diagnostics database ~package:state.package ~bounds:(bounds state)
          (since interface_named !(context.named))
        @ state.diagnostics;
      finalize state;
      Exported_parts.check state;
      (* Whether a recorded type contains a type that [unwanted] accepts. *)
      let any_type unwanted =
        let contains table =
          Array.exists
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
            table
        in
        contains state.tables.types || contains state.tables.local_types
        || contains state.tables.scrutinee_types
      in
      (* Whether a type is an error, or names a type whose declaration has
         an error. The error is reported at the declaration, and a use of
         the type is checked without a second report. *)
      let broken =
        let shapes = Hashtbl.create 8 in
        fun (part : Types.ty) ->
          Types.is_error part
          ||
          match part with
          | Types.Named { path; _ } -> (
              match Hashtbl.find_opt shapes path with
              | Some broken -> broken
              | None ->
                  let broken =
                    match Members.shape state.database path with
                    | Some (Error_shape _) -> true
                    | _ -> false
                  in
                  Hashtbl.replace shapes path broken;
                  broken)
          | _ -> false
      in
      (* A definition has a core form if it parsed completely, has no
         diagnostic, and no recorded type contains an error. A type contains
         an error when it depends on a definition that has one. *)
      let whole =
        state.diagnostics = [] && resolved.diagnostics = []
        && (not (Resolve.Parts.broken definition Header || Resolve.Parts.broken definition Body))
        && (match lowered.interface with Error_interface _ -> false | _ -> true)
        && not (any_type broken)
      in
      let build () : Core.t =
        state.form.next_node_id <- 0;
        state.form.next_synthetic_local <- 0;
        (* The core form has no hole type. If the definition has one, the
           builders read a copy of the tables in which every hole is
           [Never]. The tables themselves keep their holes for the stages
           that still read them. *)
        let checked = state.tables in
        if any_type (fun part -> part = Types.Hole) then begin
          state.form.tables_with_holes <- Some checked;
          state.tables <- Tables.copy checked;
          finalize state
        end;
        let definition =
          match state.form.definition_builder with Some build -> build () | None -> Core.Empty
        in
        state.tables <- checked;
        state.form.tables_with_holes <- None;
        { definition }
      in
      (* The capability check runs on the core form, and it solves the
         capability variables. Without a core form, every capability
         variable is solved as the empty set. *)
      let form = if whole then Some (build ()) else None in
      (match form with
      | Some form -> Capabilities.check state lowered form
      | None -> state.capability_solution <- Some (Hashtbl.create 1));
      (* If there were capability variables, substitute their solutions
         into the recorded types and build the core form again from them. A
         definition that failed the capability check has no core form. *)
      let has_capability_variables = state.unifier.capability_variable_count > 0 in
      if has_capability_variables then finalize state;
      let core : Core.t option =
        match form with
        | Some form when state.diagnostics = [] ->
            Some (if has_capability_variables then build () else form)
        | _ -> None
      in
      Some
        {
          tables = Tables.publish state.tables;
          core;
          diagnostics =
            List.sort_uniq
              (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                compare (left.span, left.code, left.message) (right.span, right.code, right.message))
              state.diagnostics;
          evidence = List.sort_uniq compare state.evidence;
        }
  | _ -> None

let type_check_result =
  Query.query ~name:"type_check_result" ~phase:Phases.bodies ~show:Names.show_key ~saved:true
    ~about:(fun (key : Names.key) -> Some { Query.path = key.path; part = Some "body" })
    (fun database key ->
      Compiler_bug.while_doing ~stage:"Infer" (Names.show_key key) (fun () -> check database key))

(* The diagnostics of every body in a file, in file offsets and in order. *)
let diagnostics database file =
  Names.per_definition database file (fun key ->
      match Query.demand database type_check_result key with
      | Some result -> result.diagnostics
      | None -> [])
