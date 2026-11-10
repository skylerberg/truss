(* Preparing a body's walk: what each local is, owned, a view, or [mut]
   access, where each is bound, and where each is read, with the branches
   and loops around each point. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties
open Context

let prepare context =
  let paths = context.paths and loops = context.loops in
  (* What a pattern binds follows the matched value's mode, in a [match],
     an [is], and a [let] alike: an owned value's parts are owned, a place's
     are views of it, and a [mut] place's are [mut] access to it. A mark on
     a method call's receiver, as in [mut file.read_line()], leaves the
     call's result, which is owned. *)
  let matched (value : expression) =
    match (lending context value, value.kind) with
    | Some (_, T.Mut), _ -> Mut_access
    | Some _, _ -> Viewing
    | None, Mode (Mut, inner) when place_of context inner <> None -> Mut_access
    | None, Mode (_, _) -> Owned
    | None, _ -> if place_of context value <> None then Viewing else Owned
  in
  let rec expression ~path ~loop_ids (value : expression) =
    Hashtbl.replace paths value.span.start path;
    Hashtbl.replace loops value.span.start loop_ids;
    (match value.kind with
    | Name name -> (
        match context.resolved.names.(name.last.id) with
        | Some (Local id) ->
            Hashtbl.replace context.uses id
              (value.span.start :: Option.value ~default:[] (Hashtbl.find_opt context.uses id))
        | _ -> ())
    | _ -> ());
    match value.kind with
    | If { condition; then_; else_ } ->
        expression ~path ~loop_ids condition;
        block ~path:((value.id, 0) :: path) ~loop_ids then_;
        Option.iter
          (function
            | Else other -> block ~path:((value.id, 1) :: path) ~loop_ids other
            | Else_if other -> expression ~path:((value.id, 1) :: path) ~loop_ids other)
          else_
    | Match { scrutinees; arms } ->
        List.iter (expression ~path ~loop_ids) scrutinees;
        let kinds = List.map matched scrutinees in
        List.iteri
          (fun index (arm : arm) ->
            let path = (value.id, index) :: path in
            if List.length arm.patterns = List.length kinds then
              List.iter2 (fun kind written -> bind ~kind ~path ~loop_ids written) kinds arm.patterns
            else List.iter (pattern ~path ~loop_ids) arm.patterns;
            Option.iter (expression ~path ~loop_ids) arm.guard;
            statement ~path ~loop_ids arm.body)
          arms
    | Is { value = tested; pattern = written; _ } ->
        expression ~path ~loop_ids tested;
        bind ~kind:(matched tested) ~path ~loop_ids written
    | Lambda { parameters; body } ->
        List.iter (pattern ~path ~loop_ids) parameters;
        block ~path ~loop_ids body
    | _ ->
        Syntax_walk.expression_parts ~expression:(expression ~path ~loop_ids)
          ~statement:(statement ~path ~loop_ids) value
  and statement ~path ~loop_ids (written : statement) =
    Hashtbl.replace paths written.span.start path;
    Hashtbl.replace loops written.span.start loop_ids;
    match written.kind with
    | Let { mutable_; pattern = written_pattern; value; else_; _ } ->
        expression ~path ~loop_ids value;
        Option.iter (block ~path ~loop_ids) else_;
        bind ~kind:(if mutable_ then Owned else matched value) ~path ~loop_ids written_pattern
    | For { pattern = written_pattern; iterable; body; _ } ->
        expression ~path ~loop_ids iterable;
        let loop_ids = written.id :: loop_ids in
        let kind =
          match iterable.kind with
          | Mode (Mut, _) -> Mut_access
          | Mode (Own, _) -> Owned
          | _ -> Viewing
        in
        bind ~kind ~path ~loop_ids written_pattern;
        block ~path ~loop_ids body
    | While { condition; body; _ } ->
        let loop_ids = written.id :: loop_ids in
        expression ~path ~loop_ids condition;
        block ~path ~loop_ids body
    | _ ->
        Syntax_walk.statement_parts ~expression:(expression ~path ~loop_ids)
          ~statement:(statement ~path ~loop_ids) written
  and block ~path ~loop_ids (written : block) =
    List.iter (statement ~path ~loop_ids) written.statements
  and pattern ~path ~loop_ids written = bind ~kind:Viewing ~path ~loop_ids written
  (* A binding is declared where its pattern starts, in the branches and
     loops around it, so a binding inside a loop is a new one each time. *)
  and bind ~kind ~path ~loop_ids (written : pattern) =
    Hashtbl.replace paths written.span.start path;
    Hashtbl.replace loops written.span.start loop_ids;
    List.iter
      (fun id ->
        if not (Hashtbl.mem context.kinds id) then Hashtbl.replace context.kinds id kind;
        Hashtbl.replace context.declared id written.span.start)
      (bound_names written)
  in
  let bodies =
    match context.definition.kind with
    | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
        [ body ]
    | Impl { members; _ } ->
        List.filter_map
          (fun (line : impl_member line) ->
            match line.kind with Impl_method { body; _ } -> Some body | _ -> None)
          members
    | Trait { members; _ } ->
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with Trait_method { body; _ } -> body | _ -> None)
          members
    | _ -> []
  in
  List.iter (block ~path:[] ~loop_ids:[]) bodies
