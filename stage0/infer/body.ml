(* Checking a definition's bodies: a function's body, defaults, and
   clauses; a type's invariants, potential, and field defaults; a trait's
   provided methods and laws; an [impl]'s methods; a constant's value; and
   the bodies of tests, theorems, and proofs. See TYPECHECKER.md, "Checking
   bodies". A part the parser did not build as written is not checked. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower
open Expressions

type result = { checked : C.t; diagnostics : Diagnostic.t list }

let no_output : env = { output = None; specification = false; self = None; self_mode = T.Read }

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
              in_statement state env value.span (fun () -> check state env value info.type_)
          | None -> ())
      | _ -> ())
    written

(* A function or method with its signature, as lowered. *)
let check_function state ~broken_body (written : signature) (body_block : block option)
    (signature : T.signature) =
  let env : env =
    {
      output = Some signature.output;
      specification = false;
      self = Option.map snd signature.receiver;
      self_mode = self_mode signature;
    }
  in
  declare_parameters state written.parameters signature;
  check_defaults state no_output written.parameters signature;
  check_clauses state env written.clauses;
  match body_block with Some block when not broken_body -> body state env block | _ -> ()

let check_definition state (lowered : Environment.lowered) =
  let definition = state.definition in
  let broken part = Resolve.Parts.broken definition part in
  if not (broken Header) then
    match (definition.kind, lowered.interface) with
    | Function { signature; body = written }, Function_interface lowered_signature ->
        check_function state ~broken_body:(broken Body) signature (Some written) lowered_signature
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
                          check state no_output value lowered.field_type)
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
    | Trait { members; _ }, Trait_interface trait ->
        let self = T.Parameter { owner = state.key.path; name = "Self" } in
        List.iteri
          (fun index (line : trait_member line) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Trait_method { signature; body = Some written } -> (
                  let name =
                    match signature.name with Plain_name name | Member_name (_, name) -> name.text
                  in
                  let receiver = Names.receiver signature.parameters in
                  match
                    List.find_opt
                      (fun (method_ : T.trait_method) ->
                        method_.method_name = name && method_.method_receiver = receiver)
                      trait.methods
                  with
                  | Some method_ ->
                      check_function state ~broken_body:(broken (Member_body index)) signature
                        (Some written) method_.method_signature
                  | None -> ())
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
              | Trait_method { body = None; _ } | Associated_type _ | Trait_member_error -> ())
          members
    | Impl { members; _ }, Impl_interface impl ->
        List.iteri
          (fun index (line : impl_member line) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Impl_method { signature; body = written } -> (
                  let name =
                    match signature.name with Plain_name name | Member_name (_, name) -> name.text
                  in
                  let receiver = Names.receiver signature.parameters in
                  match
                    List.find_opt
                      (fun (method_name, method_receiver, _) ->
                        method_name = name && method_receiver = receiver)
                      impl.impl_methods
                  with
                  | Some (_, _, lowered_signature) ->
                      check_function state ~broken_body:(broken (Member_body index)) signature
                        (Some written) lowered_signature
                  | None -> ())
              | Associated_definition _ | Impl_member_error -> ())
          members
    | Constant { value; _ }, Constant_interface constant ->
        if not (broken Body) then
          in_statement state no_output value.span (fun () ->
              check state no_output value constant.constant_type)
    | Test { body = written; _ }, _ ->
        if not (broken Body) then
          body state { no_output with output = Some (Returns T.unit) } written
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        declare_parameters state parameters signature;
        let env : env = { no_output with specification = true; output = Some (Returns T.unit) } in
        check_clauses state env clauses;
        if not (broken Body) then body state env written
    | Law_proof { body = written; _ }, _ ->
        if not (broken Body) then
          body state { no_output with specification = true; output = Some (Returns T.unit) } written
    | _ -> ()

(* The checked form holds no inference variable: every table entry is
   given the statement's final substitution, normalized, and anything
   still unsolved, which was reported, is [Error]. Entries recorded while a
   statement was being checked, such as a call's type arguments, are
   final only once it settled. *)
let finalize (state : state) =
  let final type_ =
    T.map
      (function T.Variable _ | T.Literal _ | T.Hole -> Some T.Error | _ -> None)
      (Interface.Impls.normalize state.database ~bounds:(bounds state) (zonk state type_))
  in
  let argument = function
    | T.Type type_ -> T.Type (final type_)
    | T.Value value -> (
        match Unify.resolve_value state.unifier value with
        | T.Value_variable _ -> T.Type T.Error
        | value -> T.Value value)
    | T.Capabilities _ as capabilities -> capabilities
  in
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

(* The [Self] a body's annotations name: a method's type, a trait's
   [Self], or an [impl]'s type with its associated types. *)
let body_context (context : Lower.context) (interface : Environment.interface) key =
  match interface with
  | Environment.Impl_interface impl ->
      {
        context with
        self_type = Some impl.for_type;
        self_trait = Some impl.implements;
        self_associated = impl.implements.associated;
      }
  | Trait_interface _ ->
      let self = T.Parameter { owner = key; name = "Self" } in
      { context with self_type = Some self }
  | Function_interface { receiver = Some (_, self); _ } -> { context with self_type = Some self }
  | Type_interface interface ->
      {
        context with
        self_type =
          Some
            (T.Named
               { path = key; arguments = Environment.generic_arguments interface.type_generics });
      }
  | _ -> context

let check database (key : Names.key) =
  match
    ( Query.demand database Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Names.base key )
  with
  | Some definition, Some resolved, Some (module_, _) ->
      let lowered, context = Environment.lower_definition database key definition resolved in
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
          context = body_context context lowered.interface key.path;
          text;
          tables = C.create (definition.id + 1);
          obligations = [];
          diagnostics = [];
          unifier = Unify.create ();
          locals = Hashtbl.create 32;
          frames = [];
          references = [];
          receiver_modes = [];
          binding_spans;
          lambdas = [];
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
      List.iter
        (fun (span, message) -> report state Unsatisfied_bound span message)
        (Interface.Check.unmet_bounds database ~bounds:(bounds state)
           (since interface_named !(context.named)));
      finalize state;
      Some
        {
          checked = { state.tables with obligations = List.rev state.obligations };
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.code, left.message) (right.span, right.code, right.message))
              state.diagnostics;
        }
  | _ -> None

let checked = Query.query ~name:"checked" ~show:Names.show_key check

(* Every body error of a file, in its offsets and in order. *)
let diagnostics database module_ =
  List.concat_map
    (fun (declaration : Names.declaration) ->
      let key = Names.key_of declaration in
      match (Query.demand database checked key, Query.demand database Names.base key) with
      | Some result, Some (_, base) -> List.map (Diagnostic.move base) result.diagnostics
      | _ -> [])
    (Query.demand database Names.declarations module_)
  |> List.sort (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code) (right.span, right.code))
