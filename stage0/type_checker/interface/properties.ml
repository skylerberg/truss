let copyable_trait = Well_known.path Copyable
let plain_trait = Well_known.path Plain
let storable_trait = Well_known.path Storable

let trait_substitution (interface : Types.trait_interface) ~self (reference : Types.trait_reference)
    : Types.substitution =
  (({ owner = reference.trait; name = "Self" } : Types.parameter), Types.Type self)
  :: Option.value ~default:[]
       (Types.substitution_of interface.trait_generics reference.trait_arguments)

let rec bound_closure database ?(seen = []) ~self (bound : Types.trait_reference) =
  if List.exists (fun (other : Types.trait_reference) -> Path.equal other.trait bound.trait) seen
  then []
  else
    let required =
      match Query.demand database Environment.trait_interface bound.trait with
      | Some trait ->
          List.map (Types.substitute_trait (trait_substitution trait ~self bound)) trait.requires
      | None -> []
    in
    bound :: List.concat_map (bound_closure database ~seen:(bound :: seen) ~self) required

let associated_bounds database ~base (trait : Types.trait_reference) name =
  match Query.demand database Environment.trait_interface trait.trait with
  | Some interface -> (
      match
        List.find_opt
          (fun (associated : Types.associated_type) -> associated.associated_name = name)
          interface.associated_types
      with
      | Some associated ->
          List.map
            (Types.substitute_trait (trait_substitution interface ~self:base trait))
            associated.associated_bounds
      | None -> [])
  | None -> []

let known_bounds database ~bounds (type_ : Types.ty) =
  match type_ with
  | Types.Parameter parameter ->
      List.concat_map (bound_closure database ~self:type_) (bounds parameter)
  | Types.Projection { base; trait; name } ->
      List.concat_map
        (bound_closure database ~self:type_)
        (associated_bounds database ~base trait name)
  | _ -> []

let has_bound database ~bounds type_ trait =
  List.exists
    (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
    (known_bounds database ~bounds type_)

type property = Copyable | Plain | View | Holds_function
type occurrence = In_place | Indirect | Function_input

let through outer inner =
  match (outer, inner) with
  | Function_input, _ | _, Function_input -> Function_input
  | In_place, In_place -> In_place
  | _ -> Indirect

type requirement = Never | Requires of Types.ty list
type exposure = Always | If_any of Types.ty list

type facts = {
  copyable : requirement;
  plain : requirement;
  view : exposure;
  holds_function : exposure;
  contains : (Types.ty * occurrence) list;
}

let empty =
  {
    copyable = Requires [];
    plain = Requires [];
    view = If_any [];
    holds_function = If_any [];
    contains = [];
  }

let requirement = function None -> Never | Some types -> Requires types
let exposure = function None -> Always | Some types -> If_any types
let of_requirement = function Never -> None | Requires types -> Some types
let of_exposure = function Always -> None | If_any types -> Some types

let conditions_of facts = function
  | Copyable -> of_requirement facts.copyable
  | Plain -> of_requirement facts.plain
  | View -> of_exposure facts.view
  | Holds_function -> of_exposure facts.holds_function

let type_arguments arguments =
  List.filter_map (function Types.Type type_ -> Some type_ | _ -> None) arguments

let instantiate ~resolve (interface : Types.type_interface) arguments conditions =
  let substitution =
    Option.value ~default:[] (Types.substitution_of interface.type_generics arguments)
  in
  List.map (fun condition -> resolve (Types.substitute substitution condition)) conditions

let all conditions types =
  List.fold_left
    (fun collected type_ ->
      match (collected, conditions type_) with
      | Some collected, Some more -> Some (collected @ more)
      | _ -> None)
    (Some []) types

let limit = 64

let rec conditions database ~facts_of ~resolve ~leaf ?(in_progress = []) property (type_ : Types.ty)
    =
  let each = all (conditions database ~facts_of ~resolve ~leaf ~in_progress property) in
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
          (bound_closure database ~self:type_ trait)
      in
      match property with
      | Copyable -> if requires [ copyable_trait; plain_trait ] then Some [] else None
      | Plain -> None
      | View -> if requires [ storable_trait ] then Some [] else None
      | Holds_function -> None)
  | Types.Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, property) with
      | Some Storage, Plain | Some View, View | Some Handle, (Copyable | Plain) -> None
      | Some Shared, Copyable -> Some []
      | Some Shared, Plain -> None
      | Some Shared, View | Some (Shared | View), Holds_function -> each (type_arguments arguments)
      | Some (Storage | Array), _ -> each (type_arguments arguments)
      | Some _, _ -> Some []
      | None, _ -> (
          match Query.demand database Environment.type_interface path with
          | None -> (
              match property with View | Holds_function -> Some [] | Copyable | Plain -> None)
          | Some _ when List.exists (Types.equal type_) in_progress -> Some []
          | Some _ when List.length in_progress > limit -> None
          | Some interface ->
              Option.bind
                (conditions_of (facts_of path) property)
                (fun arguments_conditions ->
                  all
                    (conditions database ~facts_of ~resolve ~leaf
                       ~in_progress:(type_ :: in_progress) property)
                    (instantiate ~resolve interface arguments arguments_conditions))))

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

let contents database ~facts_of ~resolve (type_ : Types.ty) =
  let contained = ref [] and recursions = ref [] in
  let rec visit ~enclosing occurrence (type_ : Types.ty) =
    let inside ?named ?(defining = []) step =
      visit
        ~enclosing:
          (Option.to_list (Option.map (fun named -> (named, step, defining)) named)
          @ List.map
              (fun (other, occurrence_in_named, earlier) ->
                (other, through occurrence_in_named step, defining @ earlier))
              enclosing)
        (through occurrence step)
    in
    match type_ with
    | Types.Parameter _ | Types.Projection _ -> contained := (type_, occurrence) :: !contained
    | Types.Function ({ inputs; output; _ } as function_) ->
        List.iter
          (fun (_, input) ->
            inside (if Types.terminates function_ then Function_input else Indirect) input)
          inputs;
        inside Indirect (Types.result_type output)
    | Types.Any { trait_arguments; associated; _ } ->
        List.iter (inside Indirect) (type_arguments trait_arguments @ List.map snd associated)
    | Types.Named { path; arguments } -> (
        match Intrinsic.builtin_of_path path with
        | Some Array -> List.iter (inside In_place) (type_arguments arguments)
        | Some _ -> List.iter (inside Indirect) (type_arguments arguments)
        | None -> (
            contained := (type_, occurrence) :: !contained;
            match
              ( List.find_opt (fun (named, _, _) -> Types.equal named type_) enclosing,
                Query.demand database Environment.type_interface path )
            with
            | Some (_, occurrence, defining), _ ->
                recursions := { recursive = type_; occurrence; defining } :: !recursions
            | None, Some ({ shape = Record _ | Sum _; _ } as interface)
              when List.length enclosing <= limit ->
                let substitution =
                  Option.value ~default:[] (Types.substitution_of interface.type_generics arguments)
                in
                List.iter
                  (fun (condition, step) ->
                    let condition, defining = resolve (Types.substitute substitution condition) in
                    inside ~named:type_ ~defining step condition)
                  (facts_of path).contains
            | None, Some { shape = Todo_type | Builtin_type _ | Error_shape _; _ } ->
                List.iter (inside Indirect) (type_arguments arguments)
            | None, _ -> ()))
    | _ -> ()
  in
  visit ~enclosing:[] In_place type_;
  { contained = List.rev !contained; recursions = List.rev !recursions }

let size type_ =
  let count = ref 0 in
  ignore
    (Types.map
       (fun _ ->
         incr count;
         None)
       type_);
  !count

let facts_from database ~facts_of (interface : Types.type_interface) =
  let small type_ = size type_ <= limit in
  let conditions property types =
    Option.map (List.sort_uniq compare)
      (all
         (conditions database ~facts_of ~resolve:Fun.id
            ~leaf:(fun type_ -> if small type_ then Some [ type_ ] else None)
            property)
         types)
  in
  let fields =
    let of_variant indirect fields =
      List.map (fun (field : Types.field) -> (indirect, field.field_type)) fields
    in
    match interface.shape with
    | Record fields -> of_variant false fields
    | Sum variants ->
        List.concat_map
          (fun (variant : Types.variant) ->
            of_variant variant.indirect (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ | Error_shape _ -> []
  in
  let field_types = List.map snd fields in
  let declared trait = List.exists (Path.equal trait) interface.derives in
  let allocates =
    match interface.shape with
    | Sum variants -> List.exists (fun (variant : Types.variant) -> variant.indirect) variants
    | _ -> false
  in
  let undeclared property =
    interface.opaque
    && not (declared plain_trait || (property = Copyable && declared copyable_trait))
  in
  let owned property =
    if undeclared property || (property = Plain && allocates) then None
    else conditions property field_types
  in
  match interface.shape with
  | Error_shape _ | Builtin_type _ -> empty
  | Todo_type -> { empty with copyable = Never; plain = Never; holds_function = Always }
  | Record _ | Sum _ ->
      {
        copyable = requirement (owned Copyable);
        plain = requirement (owned Plain);
        view = exposure (conditions View field_types);
        holds_function = exposure (conditions Holds_function field_types);
        contains =
          List.sort_uniq compare
            (List.concat_map
               (fun (indirect, type_) ->
                 List.filter_map
                   (function
                     | ((Types.Parameter _ | Types.Projection _) as condition), occurrence
                       when small condition ->
                         Some
                           (condition, through (if indirect then Indirect else In_place) occurrence)
                     | _ -> None)
                   (contents database ~facts_of ~resolve:(fun type_ -> (type_, [])) type_).contained)
               fields);
      }

let group =
  Query.query ~name:"type_group" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      let package = Path.package path in
      let named type_ =
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
      let successors path =
        match Query.demand database Environment.type_interface path with
        | Some { shape = Record fields; _ } ->
            List.concat_map (fun (field : Types.field) -> named field.field_type) fields
        | Some { shape = Sum variants; _ } ->
            List.concat_map
              (fun (variant : Types.variant) ->
                List.concat_map
                  (fun (field : Types.field) -> named field.field_type)
                  (Option.value ~default:[] variant.fields))
              variants
        | _ -> []
      in
      Option.value ~default:[ path ]
        (List.find_opt
           (List.exists (Path.equal path))
           (Components.of_graph ~compare:Path.compare ~successors [ path ])))

let rec group_facts =
  lazy
    (Query.query ~name:"type_group_facts" ~phase:Phases.interfaces ~saved:true ~show:Path.show
       (fun database first ->
         let interfaces =
           List.filter_map
             (fun path ->
               Option.map
                 (fun interface -> (path, interface))
                 (Query.demand database Environment.type_interface path))
             (Query.demand database group first)
         in
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
             | None -> facts_of database path
           in
           let next = each (fun _ interface -> facts_from database ~facts_of interface) in
           if Path.Map.equal ( = ) next assumed then next else settle next
         in
         settle (each (fun _ _ -> empty))))

and facts_of database path =
  Option.value ~default:empty
    (Path.Map.find_opt path
       (Query.demand database (Lazy.force group_facts) (List.hd (Query.demand database group path))))

let () = ignore (Lazy.force group_facts)
let facts = Query.query ~name:"type_facts" ~phase:Phases.interfaces ~show:Path.show facts_of

let rec is_open = function
  | Types.Parameter _ | Types.Variable _ | Types.Hole | Types.Error _ -> true
  | Types.Projection { base; _ } -> is_open base
  | _ -> false

let has database ~bounds ~normalize property type_ =
  let leaf type_ =
    let bounded trait = has_bound database ~bounds type_ trait in
    let adds_nothing =
      match property with
      | Copyable -> bounded copyable_trait || bounded plain_trait
      | Plain -> bounded plain_trait
      | View -> is_open type_
      | Holds_function -> true
    in
    if adds_nothing then Some [] else None
  in
  let type_conditions =
    conditions database ~facts_of:(Query.demand database facts) ~resolve:normalize ~leaf property
      (normalize type_)
  in
  match property with
  | Copyable | Plain -> Option.is_some type_conditions
  | View | Holds_function -> Option.is_none type_conditions

let storable database ~bounds ~normalize type_ =
  let leaf type_ = if has_bound database ~bounds type_ storable_trait then Some [] else None in
  Option.is_some
    (conditions database ~facts_of:(Query.demand database facts) ~resolve:normalize ~leaf View
       (normalize type_))

let contents database ~normalize type_ =
  contents database ~facts_of:(Query.demand database facts) ~resolve:normalize
    (fst (normalize type_))
