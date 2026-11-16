module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

type context = {
  lookups : Lookups.t;
  list_bounds : Types.parameter -> Types.trait_reference list;
  spans : Source.Definition_span.t array Lazy.t;
  mode_keywords : (Core.origin, Types.mode * Core.mode_keyword) Hashtbl.t;
  places_without_own : (Core.origin, unit) Hashtbl.t;
  names : string Local_table.t;
  binding_modes : Types.mode Local_table.t;
  types : Types.ty Local_table.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable must_be_disjoint : (Core.origin * Core.origin) list;
}

let is_plain context type_ =
  Interface.Impls.is_plain context.lookups.interface ~list_bounds:context.list_bounds type_

let is_copyable context type_ =
  Interface.Impls.is_copyable context.lookups.interface ~list_bounds:context.list_bounds type_

let is_view context type_ =
  Interface.Impls.is_view context.lookups.interface ~list_bounds:context.list_bounds type_

let holds_function context type_ =
  Interface.Impls.holds_function context.lookups.interface ~list_bounds:context.list_bounds type_

let list_callee_signatures context (callee : Mir.callee) : Types.signature list =
  let list_signatures path =
    Option.to_list (Interface.Impls.read_signature context.lookups.interface path)
  in
  match callee with
  | Function { path; _ } -> list_signatures path
  | Trait_method { trait; name; receiver; _ } ->
      list_signatures (Method { owner = trait.trait; name; receiver })
  | Capability_method { capability; name } ->
      list_signatures (Path.make_capability_method capability name)
  | Intrinsic _ | Indirect _ -> []

let stores_function context (callee : Mir.callee) position =
  let is_declared (signature : Types.signature) =
    let parameter =
      match signature.receiver with
      | None -> List.nth_opt signature.parameters position
      | Some _ when position = 0 -> None
      | Some _ -> List.nth_opt signature.parameters (position - 1)
    in
    match parameter with
    | Some parameter -> List.mem parameter.name signature.capture_free_parameters
    | None -> false
  in
  match callee with
  | Indirect _ -> true
  | _ -> List.exists is_declared (list_callee_signatures context callee)

let locate_origin context (origin : Core.origin) : Source.Definition_span.t =
  Source.Definition_span.locate (Lazy.force context.spans) origin

let report context ?(fixes = []) ?(notes = []) code (at : Source.Definition_span.t) message =
  let is_reported =
    List.exists
      (fun (reported : _ Diagnostic.diagnostic) -> reported.span = at && reported.message = message)
      context.diagnostics
  in
  if not is_reported then
    context.diagnostics <-
      Diagnostic.make ~fixes ~notes ~code:(Ownership code) at message :: context.diagnostics

let classify_binding_mode context (root : Place.root) : Types.mode =
  match root with
  | Constant _ -> Read
  | Environment | Temporary _ -> Own
  | Local local ->
      Option.value ~default:Types.Own (Local_table.find_opt context.binding_modes local)

let show_root context (root : Place.root) =
  match root with
  | Local Self -> "self"
  | Local local -> Option.value ~default:"this" (Local_table.find_opt context.names local)
  | Temporary _ -> "temporary"
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> name
  | Constant path -> Path.show path
  | Environment -> "the lambda's captured variables"

let show context (place : Place.t) =
  show_root context place.root
  ^ String.concat ""
      (List.map (function Place.Field name -> "." ^ name | Element _ -> "[...]") place.steps)

let collect context (mir : Mir.Graph.t) =
  let record_mode_keyword (argument : Mir.argument) =
    match argument with
    | Passed
        {
          mode;
          value = Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ };
          mode_keyword = Some mode_keyword;
          _;
        } ->
        Hashtbl.replace context.mode_keywords origin (mode, mode_keyword)
    | Passed _ | Default -> ()
  in
  let record_mode_keywords (call : Mir.call) = List.iter record_mode_keyword call.arguments in
  let visit_body (body : Mir.Graph.body) =
    Array.iteri
      (fun local (info : Mir.local_info) ->
        match info.kind with
        | Source { local = core; mode; name = Some name; is_var }
          when not (List.mem local body.captures) ->
            Local_table.replace context.names core name;
            Local_table.replace context.binding_modes core mode;
            Local_table.replace context.types core info.type_;
            if is_var then context.mutable_locals <- core :: context.mutable_locals
        | Source _ | Temporary | Lent _ -> ())
      body.locals;
    Array.iter
      (fun (block : Mir.Graph.basic_block) ->
        List.iter
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
                record_mode_keywords call
            | Assign _ | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end
            | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ ->
                ())
          block.statements)
      body.blocks
  in
  visit_body mir.body;
  Array.iter visit_body mir.lambdas;
  context.parameters <-
    List.rev
      (List.filter_map
         (fun local ->
           match mir.body.locals.(local).kind with
           | Source { local = core; _ } -> Some core
           | Temporary | Lent _ -> None)
         mir.body.parameters)

let copy_edits context (moved : Core.origin) =
  (match Hashtbl.find_opt context.mode_keywords moved with
    | Some (Own, { written; operand }) ->
        [
          Diagnostic.delete
            (Source.Definition_span.make (locate_origin context written).start
               (locate_origin context operand).start);
        ]
    | Some ((Read | Mut), _) | None -> [])
  @ [
      Diagnostic.insert
        (Source.Definition_span.make_zero_width (locate_origin context moved).stop)
        ".copy()";
    ]

let locate_with_mode_keyword context (place : Core.origin) : Source.Definition_span.t =
  match Hashtbl.find_opt context.mode_keywords place with
  | Some (_, { written; _ }) -> locate_origin context written
  | None -> locate_origin context place
