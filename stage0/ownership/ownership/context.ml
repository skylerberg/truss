module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

module Type_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.ty
end))

type owned_scrutinee = { scrutinee : Core.local; written : Core.origin; is_part : bool }

type decided_type = {
  plain : bool Lazy.t;
  view : bool Lazy.t;
  holds_function : bool Lazy.t;
  holds_array : bool Lazy.t;
}

type context = {
  lookups : Lookups.t;
  list_bounds : Interface.Impls.bounds;
  mode_keywords : (Syntax.id, Core.mode_keyword) Hashtbl.t;
  bare_names : (Syntax.id, string) Hashtbl.t Lazy.t;
  places_without_keyword : (Syntax.id, Language.Mode.t) Hashtbl.t;
  names : string Local_table.t;
  origins : Core.origin Local_table.t;
  binding_modes : Language.Mode.t Local_table.t;
  literal_views : unit Local_table.t;
  owned_scrutinees : owned_scrutinee Local_table.t;
  types : Types.ty Local_table.t;
  decided_types : decided_type Type_table.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  is_constant : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Catalog.description list;
  mutable must_be_disjoint : (Core.id list * Core.id list) list;
}

let is_copyable context type_ =
  Interface.Impls.is_copyable context.lookups.interface ~list_bounds:context.list_bounds type_

let rec decide context (type_ : Types.ty) =
  match Type_table.find_opt context.decided_types type_ with
  | Some decided -> decided
  | None ->
      let interface = context.lookups.interface and list_bounds = context.list_bounds in
      let decided =
        {
          plain = lazy (Interface.Impls.is_plain interface ~list_bounds type_);
          view = lazy (Interface.Impls.is_view interface ~list_bounds type_);
          holds_function = lazy (Interface.Impls.holds_function interface ~list_bounds type_);
          holds_array = lazy (compute_holds_array context type_);
        }
      in
      Type_table.replace context.decided_types type_ decided;
      decided

and holds_array context type_ = Lazy.force (decide context type_).holds_array

and compute_holds_array context (type_ : Types.ty) =
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
  | Function _ | Never | Integer | Variable _ | Hole | Error _ -> false

let is_plain context type_ = Lazy.force (decide context type_).plain
let is_view context type_ = Lazy.force (decide context type_).view
let holds_function context type_ = Lazy.force (decide context type_).holds_function
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

let find_mode_keyword context (place : Core.origin) =
  Hashtbl.find_opt context.mode_keywords (Core_walk.locate_origin place)

let find_place_without_keyword context (place : Core.origin) =
  Hashtbl.find_opt context.places_without_keyword (Core_walk.locate_origin place)

let report context diagnostic =
  let (description : Catalog.description) = Catalog.Ownership.describe diagnostic in
  let is_reported =
    List.exists
      (fun (reported : Catalog.description) ->
        reported.location = description.location && reported.message = description.message)
      context.diagnostics
  in
  if not is_reported then context.diagnostics <- description :: context.diagnostics

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

let find_root context (root : Place.root) : Catalog.Ownership.root =
  match root with
  | Local Self -> Self
  | Local local -> (
      match
        (Local_table.find_opt context.names local, Local_table.find_opt context.origins local)
      with
      | Some name, _ -> Named name
      | None, Some origin -> Unnamed origin
      | None, None -> Compiler_bug.raise_bug ~stage:"Ownership" "a local that no body holds")
  | Temporary _ -> Temporary
  | Constant path -> Constant path
  | Environment -> Environment

let find_place context (place : Place.t) : Catalog.Ownership.place =
  {
    root = find_root context place.root;
    steps =
      List.map
        (function
          | Place.Field name -> Catalog.Ownership.Field name | Element _ | Range _ -> Indexed)
        place.steps;
  }

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

let is_written_as context (written : Core.origin) (root : Catalog.Ownership.root) =
  let written = Core_walk.locate_origin written in
  match root with
  | Self -> Hashtbl.find_opt (Lazy.force context.bare_names) written = Some "self"
  | Named name -> Hashtbl.find_opt (Lazy.force context.bare_names) written = Some name
  | Unnamed origin -> Core_walk.locate_origin origin = written
  | Temporary | Constant _ | Environment -> false

let find_owned_scrutinee context (root : Place.root) : Catalog.Ownership.scrutinee option =
  match root with
  | Local local -> (
      match Local_table.find_opt context.owned_scrutinees local with
      | Some owned ->
          let scrutinee = find_root context (Local owned.scrutinee) in
          if is_written_as context owned.written scrutinee then
            Some { scrutinee; written = owned.written; is_part = owned.is_part }
          else None
      | None -> None)
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

let find_copy context type_ (moved : Core.origin) : Catalog.Ownership.copy option =
  if is_copyable context type_ then
    Some
      {
        moved;
        own_keyword =
          (match find_mode_keyword context moved with
          | Some { mode = Own; written; operand; _ } -> Some (Written written, Written operand)
          | Some { mode = Read | Mut; _ } | None -> None);
      }
  else None

let cover_with_mode_keyword context (place : Core.origin) : Core.origin Catalog.range =
  match find_mode_keyword context place with
  | Some { written; _ } -> { covering = [ Written written; place ] }
  | None -> { covering = [ place ] }
