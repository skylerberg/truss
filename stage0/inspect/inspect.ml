(* What the tools ask about one definition: its holes, with the type each
   must have and the names in scope there, and what is at a position. See
   DATABASE.md, "Requests", and SYNTAX.md, "Unfinished code". These read the
   type checker's results, and decide nothing of their own. *)

open Syntax

type hole = {
  offset : int;  (** Relative to the definition *)
  expected : string;  (** The type the hole must have *)
  scope : (string * string) list;  (** Each name in scope, with its type, in the order bound *)
}

let show_type (checked : Checked.t) id =
  match if id < Array.length checked.types then checked.types.(id) else None with
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let local_type (checked : Checked.t) id =
  match if id < Array.length checked.local_types then checked.local_types.(id) else None with
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

(* The names a pattern binds, in order. *)
let rec bindings (resolved : Resolve.resolved) (pattern : pattern) =
  match pattern.kind with
  | Binding_or_constant name -> (
      match if name.id < Array.length resolved.names then resolved.names.(name.id) else None with
      | Some Binding -> [ name ]
      | _ -> [])
  | Variant { fields = Some fields; _ } | Record fields -> List.concat_map (field resolved) fields
  | Alternatives (first :: _) -> bindings resolved first
  | Variant { fields = None; _ }
  | Alternatives []
  | Wildcard | Qualified_constant _ | Literal _ | Pattern_range _ | Pattern_error ->
      []

and field resolved (written : pattern_field) =
  match written.kind with
  | Named_field (_, pattern) | Field pattern -> bindings resolved pattern
  | Rest -> []

(* The bindings an [is] test in a condition makes, which the block it guards
   can use. *)
let rec tested resolved (value : expression) =
  match value.kind with
  | Is { pattern; _ } -> bindings resolved pattern
  | Binary { operator = And; left; right; _ } -> tested resolved left @ tested resolved right
  | Parenthesized inner -> tested resolved inner
  | _ -> []

let holes (definition : definition) (resolved : Resolve.resolved) (checked : Checked.t) =
  let found = ref [] in
  let named scope names =
    scope @ List.map (fun (name : name) -> (name.text, local_type checked name.id)) names
  in
  let rec expression scope (value : expression) =
    match value.kind with
    | Todo ->
        found :=
          { offset = value.span.start; expected = show_type checked value.id; scope } :: !found
    | Lambda { parameters; body } ->
        block (named scope (List.concat_map (bindings resolved) parameters)) body
    | Match { scrutinees; arms } ->
        List.iter (expression scope) scrutinees;
        List.iter
          (fun (arm : arm) ->
            let inner = named scope (List.concat_map (bindings resolved) arm.patterns) in
            Option.iter (expression inner) arm.guard;
            ignore (statement inner arm.body))
          arms
    | If { condition; then_; else_ } -> (
        expression scope condition;
        block (named scope (tested resolved condition)) then_;
        match else_ with
        | Some (Else otherwise) -> block scope otherwise
        | Some (Else_if next) -> expression scope next
        | None -> ())
    | Block inner -> block scope inner
    | Provide { implementations; body } ->
        List.iter (expression scope) implementations;
        block scope body
    | _ ->
        Syntax_walk.expression_parts ~expression:(expression scope)
          ~statement:(fun s -> ignore (statement scope s))
          value
  and statement scope (written : statement) =
    match written.kind with
    | Let { pattern; annotation = _; value; else_; _ } ->
        expression scope value;
        Option.iter (block scope) else_;
        named scope (bindings resolved pattern)
    | For { pattern; iterable; body; clauses = _; _ } ->
        expression scope iterable;
        block (named scope (bindings resolved pattern)) body;
        scope
    | While { condition; body; clauses = _ } ->
        expression scope condition;
        block (named scope (tested resolved condition)) body;
        scope
    | _ ->
        Syntax_walk.statement_parts ~expression:(expression scope)
          ~statement:(fun s -> ignore (statement scope s))
          written;
        scope
  and block scope (written : block) = ignore (List.fold_left statement scope written.statements) in
  let parameters (list : parameter list) =
    List.concat_map
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name; _ } -> [ (name.text, local_type checked name.id) ]
        | Self_parameter _ -> [ ("self", "the type the method is on") ]
        | Parameter_error -> [])
      list
  in
  let function_ (f : function_definition) = block (parameters f.signature.parameters) f.body in
  (match definition.kind with
  | Function f -> function_ f
  | Impl { members; _ } ->
      List.iter
        (fun (member : impl_member line) ->
          match member.kind with Impl_method f -> function_ f | _ -> ())
        members
  | Trait { members; _ } ->
      List.iter
        (fun (member : trait_member line) ->
          match member.kind with
          | Trait_method { signature; body = Some body } ->
              block (parameters signature.parameters) body
          | Law law -> block (parameters law.parameters) law.body
          | _ -> ())
        members
  | Test { body; _ } | Law_proof { body; _ } -> block [] body
  | Theorem { parameters = written; body; _ } -> block (parameters written) body
  | Constant { value; _ } -> expression [] value
  | Type_definition _ | Capability _ | Definition_error _ -> ());
  List.rev !found

(* What is at a position *)

type explanation = {
  text : string;  (** The name or expression as written *)
  meaning : string option;  (** What a name refers to *)
  refers_to : Path.t option;  (** The definition a name refers to, for its signature *)
  type_ : string option;
}

let describe_target (target : Resolve.target) =
  match target with
  | Definition path -> (Printf.sprintf "the definition %s" (Path.show path), Some path)
  | Local _ -> ("a local variable or parameter", None)
  | Binding -> ("a name bound here", None)
  | Generic _ -> ("a generic parameter", None)
  | Variant (path, name) -> (Printf.sprintf "the variant %s of %s" name (Path.show path), None)
  | Module module_ -> (Printf.sprintf "the module %s" (Path.show_module module_), None)
  | Field name -> (Printf.sprintf "the field %s" name, None)
  | Result_value -> ("the result, in a specification", None)
  | Old -> ("a value as it was when the function was called", None)
  | Cost_function _ -> ("a cost function", None)
  | Unknown -> ("nothing: the name is not known", None)

let contains (span : span) offset = span.start <= offset && offset <= span.stop

(* The innermost expression at an offset, relative to the definition, and
   what it means. *)
let at (definition : definition) (resolved : Resolve.resolved) (checked : Checked.t option) ~text
    offset =
  let best = ref None in
  let rec visit (value : expression) =
    if contains value.span offset then begin
      (match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ -> best := Some value
      | _ -> if !best = None then best := Some value);
      Syntax_walk.children visit value
    end
  in
  Syntax_walk.definition visit definition;
  match !best with
  | None -> None
  | Some value ->
      let written =
        let start = max 0 value.span.start and stop = min (String.length text) value.span.stop in
        if stop > start then String.sub text start (stop - start) else ""
      in
      let meaning, refers_to =
        match value.kind with
        | Name path -> (
            match
              if path.last.id < Array.length resolved.names then resolved.names.(path.last.id)
              else None
            with
            | Some target ->
                let meaning, refers_to = describe_target target in
                (Some meaning, refers_to)
            | None -> (None, None))
        | _ -> (
            match checked with
            | Some checked when value.id < Array.length checked.meanings -> (
                match checked.meanings.(value.id) with
                | Some (Global { path; _ }) ->
                    (Some (Printf.sprintf "the definition %s" (Path.show path)), Some path)
                | Some meaning -> (Some (Checked.show_meaning meaning), None)
                | None -> (None, None))
            | _ -> (None, None))
      in
      let type_ = Option.map (fun checked -> show_type checked value.id) checked in
      Some { text = written; meaning; refers_to; type_ }
