module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

type owned_scrutinee = { scrutinee : Core.local; written : Core.origin; is_part : bool }

type context = {
  lookups : Lookups.t;
  list_bounds : Types.parameter -> Types.trait_reference list;
  spans : Source.Definition_span.t array Lazy.t;
  text : string Lazy.t;
  mode_keywords : (Syntax.id, Core.mode_keyword) Hashtbl.t;
  places_without_keyword : (Syntax.id, Language.Mode.t) Hashtbl.t;
  names : string Local_table.t;
  origins : Core.origin Local_table.t;
  binding_modes : Language.Mode.t Local_table.t;
  literal_views : unit Local_table.t;
  owned_scrutinees : owned_scrutinee Local_table.t;
  types : Types.ty Local_table.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable must_be_disjoint : (Core.id list * Core.id list) list;
}

let is_plain context type_ =
  Interface.Impls.is_plain context.lookups.interface ~list_bounds:context.list_bounds type_

let is_copyable context type_ =
  Interface.Impls.is_copyable context.lookups.interface ~list_bounds:context.list_bounds type_

let is_view context type_ =
  Interface.Impls.is_view context.lookups.interface ~list_bounds:context.list_bounds type_

let holds_function context type_ =
  Interface.Impls.holds_function context.lookups.interface ~list_bounds:context.list_bounds type_

let rec holds_array context (type_ : Types.ty) =
  match type_ with
  | Named { path; arguments } -> (
      Types.is_builtin Array type_
      ||
      match Interface.Definition.find_type_interface context.lookups.interface path with
      | Some interface ->
          let holds_array_in fields =
            List.exists (fun (field : Types.field) -> holds_array context field.field_type) fields
          in
          Option.fold ~none:false ~some:holds_array_in
            (Types.instantiate_fields interface arguments)
          || List.exists
               (fun (variant : Types.variant) ->
                 Option.fold ~none:false ~some:holds_array_in variant.fields)
               (Option.value ~default:[] (Types.instantiate_variants interface arguments))
      | None -> false)
  | Parameter _ | Projection _ -> true
  | Function _ | Any _ | Never | Integer | Variable _ | Hole | Error _ -> false

let lends_nothing context type_ = is_plain context type_ && not (holds_array context type_)

let list_callee_signatures context (callee : Mir.callee) : Types.signature list =
  let list_signatures path =
    Option.to_list (Interface.Impls.read_signature context.lookups.interface path)
  in
  match callee.target with
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
  match callee.target with
  | Indirect _ -> true
  | _ -> List.exists is_declared (list_callee_signatures context callee)

let locate_node context (node : Syntax.id) : Source.Definition_span.t =
  Source.Definition_span.locate (Lazy.force context.spans) node

let locate_origin context (origin : Core.origin) : Source.Definition_span.t =
  locate_node context (Core_walk.locate_origin origin)

let quote_origin context (origin : Core.origin) =
  Source.Definition_span.quote (Lazy.force context.text) (locate_origin context origin)

let describe_call context (origin : Core.origin) =
  Core_walk.describe_call origin ~quote:(fun () -> quote_origin context origin) ()

let find_mode_keyword context (place : Core.origin) =
  Hashtbl.find_opt context.mode_keywords (Core_walk.locate_origin place)

let find_place_without_keyword context (place : Core.origin) =
  Hashtbl.find_opt context.places_without_keyword (Core_walk.locate_origin place)

let report context ?(fixes = []) ?(notes = []) code (at : Source.Definition_span.t) message =
  let is_reported =
    List.exists
      (fun (reported : _ Diagnostic.diagnostic) -> reported.span = at && reported.message = message)
      context.diagnostics
  in
  if not is_reported then
    context.diagnostics <-
      Diagnostic.make ~fixes ~notes ~code:(Ownership code) at message :: context.diagnostics

let classify_binding_mode context (root : Place.root) : Language.Mode.t =
  match root with
  | Constant _ -> Read
  | Environment | Temporary _ -> Own
  | Local local ->
      Option.value ~default:Language.Mode.Own (Local_table.find_opt context.binding_modes local)

let views_literal context (root : Place.root) =
  match root with
  | Local local -> Local_table.mem context.literal_views local
  | Temporary _ | Constant _ | Environment -> false

let show_root context (root : Place.root) =
  match root with
  | Local Self -> "self"
  | Local local -> (
      match
        (Local_table.find_opt context.names local, Local_table.find_opt context.origins local)
      with
      | Some name, _ -> name
      | None, Some origin -> quote_origin context origin
      | None, None -> Compiler_bug.raise_bug ~stage:"Ownership" "a local that no body holds")
  | Temporary _ -> "temporary"
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> name
  | Constant path -> Path.show path
  | Environment -> "the lambda's captured variables"

let show context (place : Place.t) =
  show_root context place.root
  ^ String.concat ""
      (List.map
         (function Place.Field name -> "." ^ name | Element _ | Range _ -> "[...]")
         place.steps)

let note_owned_scrutinee context (body : Mir.Graph.body) ~bound ~(viewed : Mir.place) ~written =
  match (body.locals.(bound).kind, viewed.root) with
  | Source { local = binding; mode = Read; is_binding = true; _ }, Local scrutinee_local
    when not (List.mem scrutinee_local body.captures) -> (
      match body.locals.(scrutinee_local).kind with
      | Source { local = scrutinee; _ }
        when classify_binding_mode context (Local scrutinee) = Own
             && List.for_all
                  (function Mir.Field _ | Variant_field _ -> true | Element _ | Range _ -> false)
                  viewed.projections ->
          Local_table.replace context.owned_scrutinees binding
            { scrutinee; written; is_part = viewed.projections <> [] }
      | Source _ | Temporary | Lent _ -> ())
  | _ -> ()

let find_owned_scrutinee context (root : Place.root) =
  match root with
  | Local local -> (
      match Local_table.find_opt context.owned_scrutinees local with
      | Some owned
        when Source.Definition_span.quote (Lazy.force context.text)
               (locate_origin context owned.written)
             = show_root context (Local owned.scrutinee) ->
          Some owned
      | Some _ | None -> None)
  | Temporary _ | Constant _ | Environment -> None

let collect context (mir : Mir.Graph.t) ~mode_keywords =
  List.iter
    (fun (keyword : Core.mode_keyword) ->
      Hashtbl.replace context.mode_keywords keyword.place keyword)
    mode_keywords;
  let visit_body (body : Mir.Graph.body) =
    Array.iteri
      (fun local (info : Mir.local_info) ->
        (match info.kind with
        | Source { local = core; _ } -> (
            match Mir.find_local_name core with
            | Some name -> Local_table.replace context.names core name
            | None -> Local_table.replace context.origins core info.origin)
        | Temporary | Lent _ -> ());
        match info.kind with
        | Source { local = core; mode; is_var; is_binding = true }
          when not (List.mem local body.captures) ->
            Local_table.replace context.binding_modes core mode;
            Local_table.replace context.types core info.type_;
            if is_var then context.mutable_locals <- core :: context.mutable_locals
        | Source _ | Temporary | Lent _ -> ())
      body.locals;
    Array.iter
      (fun (basic : Mir.Graph.basic_block) ->
        List.iter
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Basic
                (Assign
                   {
                     target = { root = Local local; projections = [] };
                     value = Operand (Borrow { place = { root = Literal _; _ }; _ });
                   }) -> (
                match body.locals.(local).kind with
                | Source { local = core; is_binding = true; _ } ->
                    Local_table.replace context.literal_views core ()
                | Source { is_binding = false; _ } | Temporary | Lent _ -> ())
            | Basic
                (Assign
                   {
                     target = { root = Local bound; projections = [] };
                     value = Operand (Borrow { place = viewed; mode = Read; origin; _ });
                   }) ->
                note_owned_scrutinee context body ~bound ~viewed ~written:origin
            | Basic _ | Provide_start _ | Provide_end -> ())
          basic.statements)
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
  (match find_mode_keyword context moved with
    | Some { mode = Own; written; operand; _ } ->
        [
          Diagnostic.delete
            (Source.Definition_span.make (locate_node context written).start
               (locate_node context operand).start);
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
  match find_mode_keyword context place with
  | Some { written; _ } ->
      Source.Definition_span.make (locate_node context written).start
        (locate_origin context place).stop
  | None -> locate_origin context place
