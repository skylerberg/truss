(* The rules on use: every variable is used, and no code is unreachable.
   Unused values are reported by body checking, and unused imports by
   resolution. *)

open Syntax
module T = Types

type context = {
  resolved : Resolve.resolved;
  tables : Infer.tables;
  text : string;
  mutable diagnostics : Syntax.diagnostic list;
}

let report context ?(fixes = []) code (span : span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes ~code:(Usage code) span message :: context.diagnostics

(* How many times a definition reads each name, by the id of the name's
   binding. *)
let count_uses (resolved : Resolve.resolved) =
  let counts = Hashtbl.create 32 in
  Array.iter
    (function
      | Some (Resolve.Local id) ->
          Hashtbl.replace counts id (1 + Option.value ~default:0 (Hashtbl.find_opt counts id))
      | _ -> ())
    resolved.names;
  counts

(* Function parameters are exempt, since an implementation may not need
   every parameter its trait declares, and so are generic parameters. *)
let parameter_names (definition : definition) =
  let names = ref [] in
  let add (parameters : parameter list) =
    List.iter
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name; _ } -> names := name.id :: !names
        | _ -> ())
      parameters
  in
  (match definition.kind with
  | Function { signature; _ } | Method_declaration signature -> add signature.parameters
  | Theorem { parameters; _ } -> add parameters
  | Trait { members; _ } ->
      List.iter
        (fun (line : trait_member line) ->
          match line.kind with Law law -> add law.parameters | _ -> ())
        members
  | _ -> ());
  !names

(* The bindings in patterns, with whether each is a bare field of a pattern
   with several fields, which [_] alone would no longer name. *)
let pattern_bindings (definition : definition) =
  let bindings = ref [] in
  let rec pattern ~bare_field (written : pattern) =
    match written.kind with
    | Binding_or_constant name -> bindings := (name, bare_field) :: !bindings
    | Variant { fields = Some fields; _ } | Record fields -> pattern_fields fields
    | Alternatives alternatives -> List.iter (pattern ~bare_field) alternatives
    | _ -> ()
  and pattern_fields (fields : pattern_field list) =
    let several =
      List.length (List.filter (fun (field : pattern_field) -> field.kind <> Rest) fields) > 1
    in
    List.iter
      (fun (field : pattern_field) ->
        match field.kind with
        | Named_field (_, inner) -> pattern ~bare_field:false inner
        | Field inner -> pattern ~bare_field:several inner
        | Rest -> ())
      fields
  in
  let rec expression (value : expression) =
    (match value.kind with
    | Is { pattern = written; _ } -> pattern ~bare_field:false written
    | Lambda { parameters; _ } -> List.iter (pattern ~bare_field:false) parameters
    | Match { arms; _ } ->
        List.iter (fun (arm : arm) -> List.iter (pattern ~bare_field:false) arm.patterns) arms
    | Quantified { binder = Binder_in (written, _); _ } -> pattern ~bare_field:false written
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : statement) =
    (match written.kind with
    | Let { pattern = written_pattern; _ } | For { pattern = written_pattern; _ } ->
        pattern ~bare_field:false written_pattern
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  Syntax_walk.definition ~statement expression definition;
  List.rev !bindings

let check_unused context (definition : definition) =
  let counts = count_uses context.resolved in
  let parameters = parameter_names definition in
  List.iter
    (fun ((name : name), bare_field) ->
      if
        context.resolved.names.(name.id) = Some Binding
        && (not (List.mem name.id parameters))
        && not (Hashtbl.mem counts name.id)
      then
        let replacement = if bare_field then name.text ^ ": _" else "_" in
        report context Unused_variable name.span
          ~fixes:
            [
              Diagnostic.fix
                (Printf.sprintf "Write `%s`." replacement)
                [ Diagnostic.replace name.span replacement ];
            ]
          (Printf.sprintf "`%s` is never used. Bind it to `_` instead." name.text))
    (pattern_bindings definition)

let diverges context (value : expression) =
  match context.tables.types.(value.id) with Some T.Never -> true | _ -> false

(* Whether a statement diverges, from types alone. *)
let rec statement_diverges context (written : statement) =
  match written.kind with
  (* A [parallel] or [concurrent] block ends only when every branch does. *)
  | Parallel body | Concurrent body -> List.exists (statement_diverges context) body.statements
  | Expression value -> diverges context value
  | Let { value; _ } -> diverges context value
  | Assignment { value; _ } -> diverges context value
  | While { condition = { kind = True; _ }; body; _ } ->
      let breaks (block : block) =
        let has_break = ref false in
        let rec statement (written : statement) =
          match written.kind with
          | For _ | While _ -> ()
          | _ -> Syntax_walk.statement_parts ~expression ~statement written
        and expression (value : expression) =
          match value.kind with
          | Break -> has_break := true
          | Lambda _ -> ()
          | _ -> Syntax_walk.expression_parts ~expression ~statement value
        in
        List.iter statement block.statements;
        !has_break
      in
      not (breaks body)
  | _ -> false

let check_block context (written : block) =
  let rec check_statements = function
    | first :: (next :: _ as rest) ->
        if statement_diverges context first then begin
          let last = List.nth rest (List.length rest - 1) in
          let start = Source.fragment_line_start context.text next.span.start in
          let start = if start > 0 then start - 1 else start in
          report context Unreachable_code next.span
            ~fixes:
              [
                Diagnostic.fix "Delete the code that cannot run."
                  [ Diagnostic.delete (Span.make start last.span.stop) ];
              ]
            "This code can never run: the statement before it never finishes."
        end
        else check_statements rest
    | _ -> ()
  in
  check_statements written.statements

let check_unreachable context (definition : definition) =
  let rec expression (value : expression) =
    (match value.kind with
    | Block block | Lambda { body = block; _ } | Provide { body = block; _ } ->
        check_block context block
    | If { then_; else_; _ } -> (
        check_block context then_;
        match else_ with Some (Else block) -> check_block context block | _ -> ())
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : statement) =
    (match written.kind with
    | For { body; _ } | While { body; _ } | Proof body -> check_block context body
    (* The branches of a [parallel] or [concurrent] block do not run one
       after another, so a branch after one that never finishes still
       runs. *)
    | Parallel _ | Concurrent _ -> ()
    | Let { else_ = Some block; _ } -> check_block context block
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  let bodies =
    match definition.kind with
    | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
        [ body ]
    | Trait { members; _ } ->
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with Law law -> Some law.body | _ -> None)
          members
    | _ -> []
  in
  List.iter (check_block context) bodies;
  Syntax_walk.definition ~statement expression definition

(* A definition's errors of use, in its own offsets. *)
let definition_diagnostics =
  Query.query ~name:"usage_diagnostics" ~phase:Phases.bodies ~saved:true
    ~show:Resolve.Names.show_key (fun database key ->
      match
        ( Query.demand database Resolve.Names.definition key,
          Query.demand database Resolve.resolved key,
          Infer.clean_tables database key,
          Query.demand database Resolve.Names.text key )
      with
      | Some definition, Some resolved, Some tables, Some text ->
          let context = { resolved; tables; text; diagnostics = [] } in
          check_unused context definition;
          check_unreachable context definition;
          List.sort
            (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
              compare left.span right.span)
            context.diagnostics
      | _ -> [])

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (Query.demand database definition_diagnostics)
