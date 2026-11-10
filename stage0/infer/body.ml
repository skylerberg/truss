(* Checking a definition's bodies: a function's body, defaults, and
   clauses; a type's invariants, potential, and field defaults; a trait's
   provided methods and laws; an [impl]'s methods; a constant's value; and
   the bodies of tests, theorems, and proofs. A part the parser did not
   build as written is not checked. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower
open State
open Statements
open Expressions

type result = {
  checked : C.t;
  core : Core.t option;
      (** The definition's core form, when it parsed whole and nothing in it is an error. *)
  diagnostics : Diagnostic.t list;
  evidence : string list;  (** The packages whose [impl]s met a bound in the definition *)
}

let no_output : env =
  {
    output = None;
    specification = false;
    self = None;
    self_mode = T.Read;
    loop_element = None;
    own = [];
  }

(* A body: each statement settles its own types, and the last is checked
   against the result type. *)
let body state env (written : block) =
  let rec go = function
    | [] -> (
        match env.output with
        | Some (Returns output) ->
            if not (unify state output T.unit) then
              report state Mismatch
                (Span.make written.span.stop written.span.stop)
                (Printf.sprintf "This body must end with a value of type `%s`." (show state output))
        | _ -> ())
    | [ (last : statement) ] ->
        in_statement state env last.span (fun () ->
            match (last.kind, env.output) with
            | Expression value, Some (Returns output) when resolve state output = T.unit ->
                (* A body that returns nothing ends with a statement, whose
                   value is unused like any other's. *)
                statement state env last ~last:false
            | Expression value, Some (Returns output) -> check state env value output
            | _, Some (Returns output) ->
                statement state env last ~last:true;
                if not (statement_never state last || unify state output T.unit) then
                  report state Mismatch last.span
                    (Printf.sprintf "This body must end with a value of type `%s`."
                       (show state output))
            | _ -> statement state env last ~last:false)
    | (first : statement) :: rest ->
        in_statement state env first.span (fun () -> statement state env first ~last:false);
        go rest
  in
  go written.statements

let declare_parameters state (written : parameter list) (signature : T.signature) =
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; _ } -> (
          match
            List.find_opt
              (fun (info : T.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some info -> declare state name info.type_ ~mutable_:false ~mode:info.mode
          | None -> ())
      | Self_parameter _ | Parameter_error -> ())
    written

let self_mode (signature : T.signature) =
  match signature.receiver with Some (Mut, _) -> T.Mut | Some (Own, _) -> T.Own | _ -> T.Read

let clause_expressions (clauses : clause list) =
  List.concat_map
    (fun (clause : clause) ->
      match clause.kind with
      | Requires value | Ensures value -> [ (value, `Bool) ]
      | Decreases measures -> List.map (fun measure -> (measure, `Measure)) measures
      | Cost { bound = Big_o value | At_most value | Exactly value; _ } -> [ (value, `Measure) ]
      | Cost { bound = Finite; _ } | Uses _ | Clause_error -> [])
    clauses

let check_clauses state env (clauses : clause list) =
  let env = { env with specification = true } in
  List.iter
    (fun ((value : expression), kind) ->
      in_statement state env value.span (fun () ->
          match kind with
          | `Bool -> check state env value T.bool
          | `Measure -> ignore (expression state env value)))
    (clause_expressions clauses)

(* The [requires] of a function-typed parameter, a specification over the
   type's named inputs and the parameters before it. *)
let check_function_type_requires state env (written : parameter list) (signature : T.signature) =
  let env = { env with specification = true } in
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { input_names; clauses; _ }; _ }; _ }
        when input_names <> [] -> (
          match
            List.find_opt
              (fun (info : T.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some { type_ = T.Function lowered; _ }
            when List.length lowered.inputs = List.length input_names ->
              List.iter2
                (fun (input : name) (mode, type_) ->
                  declare state input type_ ~mutable_:false ~mode)
                input_names lowered.inputs;
              List.iter
                (fun (clause : clause) ->
                  match clause.kind with
                  | Requires value ->
                      in_statement state env value.span (fun () -> check state env value T.bool)
                  | _ -> ())
                clauses
          | _ -> ())
      | _ -> ())
    written

let check_defaults state env (written : parameter list) (signature : T.signature) =
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; default = Some value; _ } -> (
          match
            List.find_opt
              (fun (info : T.parameter_info) -> info.name = name.text)
              signature.parameters
          with
          | Some info ->
              in_statement state env value.span (fun () -> check state env value info.type_);
              Constant.check state ~default:true value
          | None -> ())
      | _ -> ())
    written

(* The core form of a definition's parts *)

let core_cost state ({ amortized; resource; bound } : cost) : Core.cost =
  {
    amortized;
    resource;
    bound =
      (match bound with
      | Finite -> Finite
      | Big_o value -> Order_of (built state value)
      | At_most value -> At_most (built state value)
      | Exactly value -> Exactly (built state value));
  }

let core_contract state (clauses : clause list) : Core.contract =
  let each choose = List.concat_map (fun (clause : clause) -> choose clause.kind) clauses in
  let requires =
    each (function
      | Requires value ->
          let value = built state value in
          [ { Core.value; runs = Form.runs state value } ]
      | _ -> [])
  in
  let ensures = each (function Ensures value -> [ built state value ] | _ -> []) in
  let decreases =
    each (function Decreases measures -> List.map (built state) measures | _ -> [])
  in
  {
    requires;
    ensures;
    decreases;
    costs = each (function Cost cost -> [ core_cost state cost ] | _ -> []);
  }

(* The parameters as the body names them: [self] first when there is one,
   and each with the mode and the type its signature gives it. *)
let core_parameters state (written : parameter list) (signature : T.signature) : Core.parameter list
    =
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
                accepts = None;
              })
            signature.receiver
      | Named_parameter { name; default; type_; _ } ->
          Option.map
            (fun (info : T.parameter_info) : Core.parameter ->
              let default = Option.map (built state) default in
              {
                local = Bound name.id;
                name = name.text;
                mode = info.mode;
                type_ = info.type_;
                default;
                accepts =
                  (match type_.kind with
                  | Function_type { input_names = _ :: _ as inputs; clauses; _ } ->
                      Some
                        {
                          inputs =
                            List.map
                              (fun (input : name) : (Core.local * string) ->
                                (Bound input.id, input.text))
                              inputs;
                          requires =
                            List.filter_map
                              (fun (clause : clause) ->
                                match clause.kind with
                                | Requires value -> Some (built state value)
                                | _ -> None)
                              clauses;
                        }
                  | _ -> None);
              })
            (List.find_opt
               (fun (info : T.parameter_info) -> info.name = name.text)
               signature.parameters)
      | Parameter_error -> None)
    written

(* A function or method with its signature, as lowered. *)
let check_function state ~broken_body (written : signature) (body_block : block option)
    (signature : T.signature) =
  let env : env =
    {
      output = Some signature.output;
      (* A function for specifications only has a specification for a
         body: exact arithmetic, and [==>] and quantifiers over types. *)
      specification = signature.specification_only;
      self = Option.map snd signature.receiver;
      self_mode = self_mode signature;
      loop_element = None;
      own = T.capability_parameters signature.generics;
    }
  in
  declare_parameters state written.parameters signature;
  check_defaults state no_output written.parameters signature;
  check_function_type_requires state env written.parameters signature;
  check_clauses state env written.clauses;
  state.form.parts <-
    Some
      (fun () ->
        let parameters = core_parameters state written.parameters signature in
        let contract = core_contract state written.clauses in
        Function { parameters; contract; body = Option.map (built_block state) body_block });
  match body_block with Some block when not broken_body -> body state env block | _ -> ()

let check_definition state (lowered : Environment.lowered) =
  let definition = state.definition in
  let broken part = Resolve.Parts.broken definition part in
  if not (broken Header) then
    match (definition.kind, lowered.interface) with
    | Function { signature; body = written }, Function_interface lowered_signature ->
        check_function state ~broken_body:(broken Body) signature (Some written) lowered_signature
    (* A method without a body still has clauses to check. *)
    | Method_declaration signature, Function_interface lowered_signature ->
        check_function state ~broken_body:true signature None lowered_signature
    | Type_definition { body = type_body; clauses; _ }, Type_interface interface -> (
        let self =
          T.Named
            {
              path = state.key.path;
              arguments = Environment.generic_arguments interface.type_generics;
            }
        in
        let env : env = { no_output with specification = true; self = Some self } in
        List.iter
          (fun (clause : type_clause) ->
            match clause.kind with
            | Type_invariant value ->
                in_statement state env value.span (fun () -> check state env value T.bool)
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
        state.form.parts <-
          Some
            (fun () ->
              let defaults =
                List.map
                  (fun (variant, name, value) -> (variant, name, built state value))
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
                    clause (function Type_invariant value -> Some (built state value) | _ -> None);
                  potential =
                    (match
                       clause (function Potential value -> Some (built state value) | _ -> None)
                     with
                    | first :: _ -> Some first
                    | [] -> None);
                });
        let defaults (fields : field list) (lowered_fields : T.field list) =
          List.iter
            (fun (field : field) ->
              match field.kind with
              | Field_declaration { name; default = Some value; _ } -> (
                  match
                    List.find_opt
                      (fun (lowered : T.field) -> lowered.field_name = name.text)
                      lowered_fields
                  with
                  | Some lowered ->
                      in_statement state no_output value.span (fun () ->
                          check state no_output value lowered.field_type);
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
                      (fun (lowered : T.variant) -> lowered.variant_name = variant.name.text)
                      lowered_variants )
                with
                | Some fields, Some { fields = Some lowered_fields; _ } ->
                    defaults fields lowered_fields
                | _ -> ())
              variants
        | _ -> ())
    | Trait { members; _ }, Trait_interface _ ->
        let self = T.Parameter { owner = state.key.path; name = "Self" } in
        state.form.parts <-
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
                                          local = Bound name.id;
                                          name = name.text;
                                          mode = Read;
                                          type_ = Form.local_type state name.id;
                                          default = None;
                                          accepts = None;
                                        }
                                  | _ -> None)
                                law.parameters
                            in
                            let requires = List.map (built state) law.requires in
                            [
                              {
                                Core.name = law.name.text;
                                parameters;
                                requires;
                                body = built_block state law.body;
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
                          declare state name (Lower.type_ state.context type_) ~mutable_:false
                            ~mode:T.Read
                      | _ -> ())
                    law.parameters;
                  List.iter
                    (fun (requirement : expression) ->
                      in_statement state env requirement.span (fun () ->
                          check state env requirement T.bool))
                    law.requires;
                  if not (broken (Member_body index)) then
                    body state { env with output = Some (Returns T.bool) } law.body
              | Associated_type _ | Trait_member_error -> ())
          members
    | Constant { value; _ }, Constant_interface constant ->
        if not (broken Body) then begin
          in_statement state no_output value.span (fun () ->
              check state no_output value constant.constant_type);
          state.form.parts <- Some (fun () -> Constant (built state value));
          Constant.check state ~default:false value
        end
    | Test { body = written; _ }, _ ->
        state.form.parts <- Some (fun () -> Test (built_block state written));
        if not (broken Body) then
          body state { no_output with output = Some (Returns T.unit) } written
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        declare_parameters state parameters signature;
        let env : env = { no_output with specification = true; output = Some (Returns T.unit) } in
        check_clauses state env clauses;
        state.form.parts <-
          Some
            (fun () ->
              let parameters = core_parameters state parameters signature in
              let contract = core_contract state clauses in
              Function { parameters; contract; body = Some (built_block state written) });
        if not (broken Body) then body state env written
    | Law_proof { body = written; _ }, _ ->
        state.form.parts <- Some (fun () -> Law_proof (built_block state written));
        if not (broken Body) then
          body state { no_output with specification = true; output = Some (Returns T.unit) } written
    | _ -> ()

(* The checked form holds no inference variable: every table entry is
   given the statement's final substitution, normalized, and anything
   still unsolved, which was reported, is [Error]. Entries recorded while a
   statement was being checked, such as a call's type arguments, are
   final only once it settled. *)
let finalize (state : state) =
  let final = final state and argument = final_argument state in
  let trait (reference : T.trait_reference) =
    {
      reference with
      trait_arguments = List.map argument reference.trait_arguments;
      associated = List.map (fun (name, type_) -> (name, final type_)) reference.associated;
    }
  in
  let evidence : C.evidence -> C.evidence = function
    | Impl { impl; arguments } ->
        Impl
          {
            impl;
            arguments = List.map (fun (parameter, value) -> (parameter, argument value)) arguments;
          }
    | other -> other
  in
  let call (written : C.call) : C.call =
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
                self_type = final method_.self_type;
                type_arguments = List.map argument method_.type_arguments;
                evidence = evidence method_.evidence;
              }
        | Constructor constructor ->
            Constructor
              { constructor with type_arguments = List.map argument constructor.type_arguments }
        | Intrinsic intrinsic ->
            Intrinsic { intrinsic with type_arguments = List.map argument intrinsic.type_arguments }
        | other -> other);
      capability_arguments = written.capability_arguments;
      result = final written.result;
    }
  in
  let tables = state.tables in
  let update table f = Array.iteri (fun index entry -> table.(index) <- Option.map f entry) table in
  update tables.types final;
  update tables.local_types final;
  update tables.pattern_types final;
  update tables.calls call;
  update tables.meanings (function
    | C.Global { path; type_arguments } ->
        C.Global { path; type_arguments = List.map argument type_arguments }
    | Field_read { type_; field } -> Field_read { type_ = final type_; field }
    | Variant_value { type_; variant } -> Variant_value { type_ = final type_; variant }
    | Type_name type_ -> Type_name (final type_)
    | other -> other);
  update tables.loops (function
    | C.Integer_range { element; inclusive } ->
        C.Integer_range { element = final element; inclusive }
    | Yielding { call = written; mode } -> Yielding { call = call written; mode }
    | Pulled { cursor } -> Pulled { cursor = final cursor });
  update tables.patterns (function
    | C.Variant_pattern { type_; variant } -> C.Variant_pattern { type_ = final type_; variant }
    | Record_pattern { type_ } -> Record_pattern { type_ = final type_ }
    | other -> other);
  update tables.templates (fun (template : C.template) ->
      {
        template with
        from_template = Option.map call template.from_template;
        part_conversions = List.map (Option.map call) template.part_conversions;
      })

let check database (key : Names.key) =
  match
    (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
  with
  | Some definition, Some resolved ->
      (* The definition's module is in its key. Where it starts in its file
         is not read, so a definition that only moved is not checked again. *)
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
          tables = C.create (definition.id + 1);
          form =
            {
              expressions = Array.make (definition.id + 1) None;
              statements = Array.make (definition.id + 1) None;
              patterns = Array.make (definition.id + 1) None;
              parts = None;
              next = 0;
              made = 0;
            };
          obligations = [];
          diagnostics = [];
          unifier = Unify.create ();
          locals = Hashtbl.create 32;
          frames = [];
          references = [];
          receiver_modes = [];
          binding_spans;
          lambdas = [];
          unsolved = None;
          widened = Hashtbl.create 4;
          evidence = [];
        }
      in
      (* What lowering reported for the interface is the interface's to
         report; what it reports for the types written inside bodies, and
         their bounds, are the body's. *)
      let interface_diagnostics = List.length !(context.diagnostics) in
      let interface_named = List.length !(context.named) in
      check_definition state lowered;
      let since count list = List.filteri (fun index _ -> index < List.length list - count) list in
      state.diagnostics <- since interface_diagnostics !(context.diagnostics) @ state.diagnostics;
      state.diagnostics <-
        Interface.Check.bound_diagnostics database ~package:state.package ~bounds:(bounds state)
          (since interface_named !(context.named))
        @ state.diagnostics;
      finalize state;
      (* A definition has a core form when it parsed whole, nothing in it is
         an error, and every type in it is decided: an error elsewhere that
         reaches it through a type, or a [todo] whose type nothing fixes,
         leaves nothing to build on. *)
      let decided table =
        Array.for_all
          (function
            | Some type_ ->
                let decided = ref true in
                ignore
                  (T.map
                     (function
                       | T.Error _ | T.Hole ->
                           decided := false;
                           None
                       | _ -> None)
                     type_);
                !decided
            | None -> true)
          table
      in
      let whole =
        state.diagnostics = [] && resolved.diagnostics = []
        && (not (Resolve.Parts.broken definition Header || Resolve.Parts.broken definition Body))
        && (match lowered.interface with Error_interface _ -> false | _ -> true)
        && decided state.tables.types && decided state.tables.local_types
        && decided state.tables.pattern_types
      in
      (* What code may call is checked on the form, where every call is a
         node. A definition that fails it has no form to give out. *)
      let core : Core.t option =
        if whole then begin
          let parts = match state.form.parts with Some build -> build () | None -> Core.Nothing in
          let form : Core.t = { parts; nodes = state.form.next; made = state.form.made } in
          Capabilities.check state lowered form;
          if state.diagnostics = [] then Some form else None
        end
        else None
      in
      Some
        {
          checked = { state.tables with obligations = List.rev state.obligations };
          core;
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.code, left.message) (right.span, right.code, right.message))
              state.diagnostics;
          evidence = List.sort_uniq compare state.evidence;
        }
  | _ -> None

let checked =
  Query.query ~name:"checked" ~phase:Bodies ~show:Names.show_key ~saved:true
    ~about:(fun (key : Names.key) -> Some { Query.path = key.path; part = Some "body" })
    (fun database key ->
      Compiler_bug.within ~stage:"Infer" (Names.show_key key) (fun () -> check database key))

(* Every body error of a file, in its offsets and in order. *)
let diagnostics database module_ =
  Names.per_definition database module_ (fun key ->
      match Query.demand database checked key with Some result -> result.diagnostics | None -> [])
