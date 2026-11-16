module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

type context = {
  lookups : Lookups.t;
  list_bounds : Types.parameter -> Types.trait_reference list;
  spans : Source.Definition_span.t array Lazy.t;
  mode_keywords : (Core.origin, Core.mode_keyword) Hashtbl.t;
  places_without_keyword : (Core.origin, Types.mode) Hashtbl.t;
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

let collect context (mir : Mir.Graph.t) ~mode_keywords =
  List.iter
    (fun (keyword : Core.mode_keyword) ->
      Hashtbl.replace context.mode_keywords keyword.place keyword)
    mode_keywords;
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
      body.locals
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
    | Some { mode = Own; written; operand; _ } ->
        [
          Diagnostic.delete
            (Source.Definition_span.make (locate_origin context written).start
               (locate_origin context operand).start);
        ]
    | Some { mode = Read | Mut; _ } | None -> [])
  @ [
      Diagnostic.insert
        (Source.Definition_span.make_zero_width (locate_origin context moved).stop)
        ".copy()";
    ]

let copy_fix context title type_ (moved : Core.origin) =
  if is_copyable context type_ then [ Diagnostic.fix title (copy_edits context moved) ] else []

let locate_with_mode_keyword context (place : Core.origin) : Source.Definition_span.t =
  match Hashtbl.find_opt context.mode_keywords place with
  | Some { written; _ } ->
      Source.Definition_span.make (locate_origin context written).start
        (locate_origin context place).stop
  | None -> locate_origin context place
