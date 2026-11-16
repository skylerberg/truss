let make_trait_substitution (interface : Types.trait_interface) ~self
    (reference : Types.trait_reference) : Types.substitution =
  (({ owner = reference.trait; name = "Self" } : Types.parameter), Types.Type self)
  :: Option.value ~default:[]
       (Types.make_substitution interface.trait_generics reference.trait_arguments)

let list_bound_closure lookups ~self (bound : Types.trait_reference) =
  let closure = ref [] in
  let rec visit ancestors (bound : Types.trait_reference) =
    if not (List.exists (Path.equal bound.trait) ancestors || List.mem bound !closure) then begin
      closure := bound :: !closure;
      match Definition.read_trait_interface lookups bound.trait with
      | Some trait ->
          List.iter
            (fun required ->
              visit (bound.trait :: ancestors)
                (Types.substitute_trait (make_trait_substitution trait ~self bound) required))
            trait.requires
      | None -> ()
    end
  in
  visit [] bound;
  List.rev !closure

let list_associated_bounds lookups ~base (trait : Types.trait_reference) name =
  match Definition.read_trait_interface lookups trait.trait with
  | Some interface -> (
      match
        List.find_opt
          (fun (associated : Types.associated_type) -> associated.associated_name = name)
          interface.associated_types
      with
      | Some associated ->
          List.map
            (Types.substitute_trait (make_trait_substitution interface ~self:base trait))
            associated.associated_bounds
      | None -> [])
  | None -> []

let list_known_bounds lookups ~bounds (type_ : Types.ty) =
  match type_ with
  | Types.Parameter parameter ->
      List.concat_map (list_bound_closure lookups ~self:type_) (bounds parameter)
  | Types.Projection { base; trait; name } ->
      List.concat_map
        (list_bound_closure lookups ~self:type_)
        (list_associated_bounds lookups ~base trait name)
  | _ -> []

let has_bound lookups ~bounds type_ trait =
  List.exists
    (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
    (list_known_bounds lookups ~bounds type_)

type property = Copyable | Plain | View | Holds_function
type occurrence = Environment.occurrence = In_place | Indirect | Function_input
type requirement = Environment.requirement = Never | Requires of Types.ty list
type exposure = Environment.exposure = Always | If_any of Types.ty list

let compose_occurrences outer inner =
  match (outer, inner) with
  | Function_input, _ | _, Function_input -> Function_input
  | In_place, In_place -> In_place
  | _ -> Indirect

let empty : Environment.type_facts =
  {
    copyable = Requires [];
    plain = Requires [];
    view = If_any [];
    holds_function = If_any [];
    contains = [];
  }

let to_requirement = function None -> Never | Some types -> Requires types
let to_exposure = function None -> Always | Some types -> If_any types
let of_requirement = function Never -> None | Requires types -> Some types
let of_exposure = function Always -> None | If_any types -> Some types
let read_facts (lookups : Lookups.t) path = Option.value ~default:empty (lookups.type_facts path)

let find_stored_conditions (facts : Environment.type_facts) = function
  | Copyable -> of_requirement facts.copyable
  | Plain -> of_requirement facts.plain
  | View -> of_exposure facts.view
  | Holds_function -> of_exposure facts.holds_function

let list_type_arguments arguments =
  List.filter_map (function Types.Type type_ -> Some type_ | _ -> None) arguments

let instantiate ~resolve (interface : Types.type_interface) arguments conditions =
  let substitution =
    Option.value ~default:[] (Types.make_substitution interface.type_generics arguments)
  in
  List.map (fun condition -> resolve (Types.substitute substitution condition)) conditions

let combine_conditions find_conditions types =
  List.fold_left
    (fun collected type_ ->
      match (collected, find_conditions type_) with
      | Some collected, Some more -> Some (collected @ more)
      | _ -> None)
    (Some []) types

exception Recursion_limit of string

let recursion_limit = 64
let largest_condition = 64

let show_property = function
  | Copyable -> "is `Copyable`"
  | Plain -> "is `Plain`"
  | View -> "is a view"
  | Holds_function -> "holds a function"

let fail_at_recursion_limit query =
  raise
    (Recursion_limit
       (Printf.sprintf
          "%s needs more than %d nested types. The compiler stops there: an associated type that \
           holds a larger type can grow a type forever."
          query recursion_limit))

let rec compute_conditions lookups ~facts_of ~resolve ~leaf ?(in_progress = []) property
    (type_ : Types.ty) =
  let each =
    combine_conditions (compute_conditions lookups ~facts_of ~resolve ~leaf ~in_progress property)
  in
  match type_ with
  | Types.Error _ | Types.Hole | Types.Variable _ | Types.Never | Types.Literal _ | Types.Integer ->
      Some []
  | Types.Function _ -> (
      match property with View | Holds_function -> None | Copyable | Plain -> Some [])
  | Types.Parameter _ | Types.Projection _ -> leaf type_
  | Types.Any trait -> (
      let requires traits =
        List.exists
          (fun (bound : Types.trait_reference) -> List.exists (Path.equal bound.trait) traits)
          (list_bound_closure lookups ~self:type_ trait)
      in
      match property with
      | Copyable ->
          if requires [ Well_known.path Copyable; Well_known.path Plain ] then Some [] else None
      | Plain -> None
      | View -> if requires [ Well_known.path Storable ] then Some [] else None
      | Holds_function -> None)
  | Types.Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, property) with
      | Some Storage, Plain | Some View, View | Some Handle, (Copyable | Plain) -> None
      | Some Shared, Copyable -> Some []
      | Some Shared, Plain -> None
      | Some Shared, View | Some (Shared | View), Holds_function ->
          each (list_type_arguments arguments)
      | Some (Storage | Array), _ -> each (list_type_arguments arguments)
      | Some _, _ -> Some []
      | None, _ -> (
          match Definition.read_type_interface lookups path with
          | None -> (
              match property with View | Holds_function -> Some [] | Copyable | Plain -> None)
          | Some _ when List.exists (Types.equal type_) in_progress -> Some []
          | Some _ when List.length in_progress > recursion_limit ->
              fail_at_recursion_limit
                (Printf.sprintf "Deciding whether `%s` %s" (Types.show type_)
                   (show_property property))
          | Some interface ->
              Option.bind
                (find_stored_conditions (facts_of path) property)
                (fun arguments_conditions ->
                  combine_conditions
                    (compute_conditions lookups ~facts_of ~resolve ~leaf
                       ~in_progress:(type_ :: in_progress) property)
                    (instantiate ~resolve interface arguments arguments_conditions))))

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

let walk_contents lookups ~(facts_of : Path.t -> Environment.type_facts) ~resolve (type_ : Types.ty)
    =
  let contained = ref [] and recursions = ref [] in
  let rec visit ~enclosing occurrence (type_ : Types.ty) =
    let inside ?named ?(defining = []) step =
      visit
        ~enclosing:
          (Option.to_list (Option.map (fun named -> (named, step, defining)) named)
          @ List.map
              (fun (other, occurrence_in_named, earlier) ->
                (other, compose_occurrences occurrence_in_named step, defining @ earlier))
              enclosing)
        (compose_occurrences occurrence step)
    in
    match type_ with
    | Types.Parameter _ | Types.Projection _ -> contained := (type_, occurrence) :: !contained
    | Types.Function ({ inputs; output; _ } as function_) ->
        List.iter
          (fun (_, input) ->
            inside (if Types.terminates function_ then Function_input else Indirect) input)
          inputs;
        inside Indirect output
    | Types.Any { trait_arguments; associated; _ } ->
        List.iter (inside Indirect) (list_type_arguments trait_arguments @ List.map snd associated)
    | Types.Named { path; arguments } -> (
        match Intrinsic.builtin_of_path path with
        | Some Array -> List.iter (inside In_place) (list_type_arguments arguments)
        | Some _ -> List.iter (inside Indirect) (list_type_arguments arguments)
        | None -> (
            contained := (type_, occurrence) :: !contained;
            match
              ( List.find_opt (fun (named, _, _) -> Types.equal named type_) enclosing,
                Definition.read_type_interface lookups path )
            with
            | Some (_, occurrence, defining), _ ->
                recursions := { recursive = type_; occurrence; defining } :: !recursions
            | None, Some ({ shape = Record _ | Sum _; _ } as interface) ->
                if List.length enclosing > recursion_limit then
                  fail_at_recursion_limit
                    (Printf.sprintf "Listing the types that `%s` holds" (Types.show type_));
                let substitution =
                  Option.value ~default:[]
                    (Types.make_substitution interface.type_generics arguments)
                in
                List.iter
                  (fun (condition, step) ->
                    let condition, defining = resolve (Types.substitute substitution condition) in
                    inside ~named:type_ ~defining step condition)
                  (facts_of path).contains
            | None, Some { shape = Todo_type | Builtin_type _; _ } ->
                List.iter (inside Indirect) (list_type_arguments arguments)
            | None, _ -> ()))
    | _ -> ()
  in
  visit ~enclosing:[] In_place type_;
  { contained = List.rev !contained; recursions = List.rev !recursions }

let count_nodes type_ =
  let count = ref 0 in
  ignore
    (Types.map
       (fun _ ->
         incr count;
         None)
       type_);
  !count

let compute_facts lookups ~facts_of (interface : Types.type_interface) : Environment.type_facts =
  let is_small type_ = count_nodes type_ <= largest_condition in
  let find_conditions property types =
    Option.map (List.sort_uniq compare)
      (combine_conditions
         (compute_conditions lookups ~facts_of ~resolve:Fun.id
            ~leaf:(fun type_ -> if is_small type_ then Some [ type_ ] else None)
            property)
         types)
  in
  let fields =
    let list_variant_fields indirect fields =
      List.map (fun (field : Types.field) -> (indirect, field.field_type)) fields
    in
    match interface.shape with
    | Record fields -> list_variant_fields false fields
    | Sum variants ->
        List.concat_map
          (fun (variant : Types.variant) ->
            list_variant_fields variant.indirect (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ -> []
  in
  let field_types = List.map snd fields in
  let is_declared trait = List.exists (Path.equal trait) interface.derives in
  let allocates =
    match interface.shape with
    | Sum variants -> List.exists (fun (variant : Types.variant) -> variant.indirect) variants
    | _ -> false
  in
  let is_undeclared property =
    interface.opaque
    && not
         (is_declared (Well_known.path Plain)
         || (property = Copyable && is_declared (Well_known.path Copyable)))
  in
  let find_owned_conditions property =
    if is_undeclared property || (property = Plain && allocates) then None
    else find_conditions property field_types
  in
  match interface.shape with
  | Builtin_type _ -> empty
  | Todo_type -> { empty with copyable = Never; plain = Never; holds_function = Always }
  | Record _ | Sum _ ->
      {
        copyable = to_requirement (find_owned_conditions Copyable);
        plain = to_requirement (find_owned_conditions Plain);
        view = to_exposure (find_conditions View field_types);
        holds_function = to_exposure (find_conditions Holds_function field_types);
        contains =
          List.sort_uniq compare
            (List.concat_map
               (fun (indirect, type_) ->
                 List.filter_map
                   (function
                     | ((Types.Parameter _ | Types.Projection _) as condition), occurrence
                       when is_small condition ->
                         Some
                           ( condition,
                             compose_occurrences
                               (if indirect then Indirect else In_place)
                               occurrence )
                     | _ -> None)
                   (walk_contents lookups ~facts_of ~resolve:(fun type_ -> (type_, [])) type_)
                     .contained)
               fields);
      }

let list_field_type_paths ~package (interface : Types.type_interface) =
  let list_named type_ =
    let named_types = ref [] in
    ignore
      (Types.map
         (function
           | Types.Named { path = named; _ } when Path.package named = package ->
               named_types := named :: !named_types;
               None
           | _ -> None)
         type_);
    !named_types
  in
  List.concat_map list_named (Types.list_field_types interface)

let compute_component_facts (lookups : Lookups.t) interfaces =
  let each facts =
    List.fold_left
      (fun facts_by_path (path, interface) ->
        Path.Map.add path (facts path interface) facts_by_path)
      Path.Map.empty interfaces
  in
  let rec settle assumed =
    let facts_of path =
      match Path.Map.find_opt path assumed with
      | Some facts -> facts
      | None -> read_facts lookups path
    in
    let next = each (fun _ interface -> compute_facts lookups ~facts_of interface) in
    if Path.Map.equal ( = ) next assumed then next else settle next
  in
  Path.Map.bindings (settle (each (fun _ _ -> empty)))

let rec is_open = function
  | Types.Parameter _ | Types.Variable _ | Types.Hole | Types.Error _ -> true
  | Types.Projection { base; _ } -> is_open base
  | _ -> false

let has_property (lookups : Lookups.t) ~bounds ~normalize property type_ =
  let leaf type_ =
    let bounded trait = has_bound lookups ~bounds type_ trait in
    let adds_nothing =
      match property with
      | Copyable -> bounded (Well_known.path Copyable) || bounded (Well_known.path Plain)
      | Plain -> bounded (Well_known.path Plain)
      | View -> is_open type_
      | Holds_function -> true
    in
    if adds_nothing then Some [] else None
  in
  let type_conditions =
    compute_conditions lookups ~facts_of:(read_facts lookups) ~resolve:normalize ~leaf property
      (normalize type_)
  in
  match property with
  | Copyable | Plain -> Option.is_some type_conditions
  | View | Holds_function -> Option.is_none type_conditions

let is_storable (lookups : Lookups.t) ~bounds ~normalize type_ =
  let leaf type_ =
    if has_bound lookups ~bounds type_ (Well_known.path Storable) then Some [] else None
  in
  Option.is_some
    (compute_conditions lookups ~facts_of:(read_facts lookups) ~resolve:normalize ~leaf View
       (normalize type_))

let collect_contents (lookups : Lookups.t) ~normalize type_ =
  walk_contents lookups ~facts_of:(read_facts lookups) ~resolve:normalize (fst (normalize type_))
