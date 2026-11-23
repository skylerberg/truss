let list_bound_closure_over ~find_requirements ~self (bound : Types.trait_reference) =
  let closure = ref [] in
  let rec visit ancestors (bound : Types.trait_reference) =
    if not (List.exists (Path.equal bound.trait) ancestors || List.mem bound !closure) then begin
      closure := bound :: !closure;
      match find_requirements bound.trait with
      | Some (trait_generics, requires) ->
          let substitution =
            Types.bind_argument
              (Types.make_self_parameter bound.trait)
              (Types.Type self)
              (Types.make_substitution trait_generics bound.trait_arguments)
          in
          List.iter
            (fun required ->
              visit (bound.trait :: ancestors) (Types.substitute_trait substitution required))
            requires
      | None -> ()
    end
  in
  visit [] bound;
  List.rev !closure

let list_bound_closure lookups ~self (bound : Types.trait_reference) =
  match Definition.find_trait_interface lookups bound.trait with
  | Some interface ->
      let substitution =
        Types.bind_argument
          (Types.make_self_parameter bound.trait)
          (Types.Type self)
          (Types.make_substitution interface.trait_generics bound.trait_arguments)
      in
      List.fold_left
        (fun closure supertrait ->
          let supertrait = Types.substitute_trait substitution supertrait in
          if List.mem supertrait closure then closure else closure @ [ supertrait ])
        [ bound ] interface.supertraits
  | None -> [ bound ]

module Bounds = struct
  type t = Types.parameter -> Types.trait_reference list

  let none : t = fun _ -> []

  let of_known (known : (Types.parameter * Types.trait_reference list) list) : t =
   fun parameter -> Option.value ~default:[] (List.assoc_opt parameter known)

  let close lookups (declared : Types.parameter -> Types.trait_reference list) : t =
   fun parameter ->
    List.concat_map
      (list_bound_closure lookups ~self:(Types.Parameter parameter))
      (declared parameter)

  let append (first : t) (second : t) : t = fun parameter -> first parameter @ second parameter

  let override (outer : t) ~for_ (inner : t) : t =
   fun parameter -> if List.mem parameter for_ then inner parameter else outer parameter

  let list (bounds : t) parameter = bounds parameter
end

let find_declaring_trait lookups ~base (trait : Types.trait_reference) ~is_declared =
  List.find_opt
    (fun (reference : Types.trait_reference) ->
      match Definition.find_interface lookups reference.trait with
      | Some (Environment.Trait_interface interface) -> is_declared interface
      | Some (Environment.Error_interface _) -> true
      | _ -> false)
    (list_bound_closure lookups ~self:base trait)

let find_trait_declaring_type lookups ~base trait name =
  find_declaring_trait lookups ~base trait ~is_declared:(fun (interface : Types.trait_interface) ->
      List.exists
        (fun (associated : Types.associated_type) -> associated.associated_name = name)
        interface.associated_types)

let find_trait_declaring_capability_set lookups ~base trait name =
  find_declaring_trait lookups ~base trait ~is_declared:(fun (interface : Types.trait_interface) ->
      List.mem name interface.associated_capabilities)

let list_associated_bounds lookups ~base trait name =
  match
    Option.bind (find_trait_declaring_type lookups ~base trait name)
      (fun (declaring : Types.trait_reference) ->
        Option.map
          (fun interface -> (declaring, interface))
          (Definition.find_trait_interface lookups declaring.trait))
  with
  | Some (declaring, interface) ->
      List.concat_map
        (fun (associated : Types.associated_type) ->
          if associated.associated_name = name then
            List.map
              (Types.substitute_trait
                 (Types.make_trait_substitution interface.trait_generics ~self:base declaring))
              associated.associated_bounds
          else [])
        interface.associated_types
  | None -> []

let list_known_bounds lookups ~list_bounds (type_ : Types.ty) =
  match type_ with
  | Types.Parameter parameter -> Bounds.list list_bounds parameter
  | Types.Projection { base; trait; name } ->
      List.concat_map
        (list_bound_closure lookups ~self:type_)
        (list_associated_bounds lookups ~base trait name)
  | _ -> []

let list_rigid_members lookups ~list_bounds type_ =
  Option.value ~default:[]
    (Types.find_bound_integer_implementors (list_known_bounds lookups ~list_bounds type_))

let has_bound lookups ~list_bounds type_ trait =
  List.exists
    (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
    (list_known_bounds lookups ~list_bounds type_)

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
    generics = [];
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

let find_stored_conditions (facts : Environment.type_facts) = function
  | Copyable -> of_requirement facts.copyable
  | Plain -> of_requirement facts.plain
  | View -> of_exposure facts.view
  | Holds_function -> of_exposure facts.holds_function

let list_type_arguments arguments =
  List.filter_map (function Types.Type type_ -> Some type_ | _ -> None) arguments

let instantiate ~resolve generics arguments conditions =
  let substitution = Types.make_substitution generics arguments in
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

let raise_bug format = Compiler_bug.raise_bug ~stage:"Interface" format

let rec strip_projections = function
  | Types.Projection { base; _ } -> strip_projections base
  | type_ -> type_

let rec compute_conditions lookups ~facts_of ~resolve ~compute_leaf ?(in_progress = []) property
    (type_ : Types.ty) =
  let combine_each =
    combine_conditions
      (compute_conditions lookups ~facts_of ~resolve ~compute_leaf ~in_progress property)
  in
  match type_ with
  | Types.Never | Types.Integer -> Some []
  | Types.Error _ | Types.Hole | Types.Variable _ -> Some [ type_ ]
  | Types.Function _ -> (
      match property with View | Holds_function -> None | Copyable | Plain -> Some [])
  | Types.Parameter _ | Types.Projection _ -> (
      match strip_projections type_ with
      | root when Types.is_open_type root -> Some [ root ]
      | _ -> compute_leaf type_)
  | Types.Named { path; arguments } -> (
      match (Well_known.find_builtin_type path, property) with
      | Some Storage, Plain | Some View, View | Some Handle, (Copyable | Plain) -> None
      | Some Shared, Copyable -> Some []
      | Some Shared, Plain -> None
      | Some Shared, View | Some (Shared | View), Holds_function ->
          combine_each (list_type_arguments arguments)
      | Some (Storage | Array), _ -> combine_each (list_type_arguments arguments)
      | Some _, _ -> Some []
      | None, _ ->
          if List.exists (Types.equal type_) in_progress then Some []
          else if List.length in_progress > recursion_limit then
            fail_at_recursion_limit
              (Printf.sprintf "Deciding whether `%s` %s" (Types.show type_) (show_property property))
          else
            let (facts : Environment.type_facts) = facts_of path in
            Option.bind (find_stored_conditions facts property) (fun arguments_conditions ->
                combine_conditions
                  (compute_conditions lookups ~facts_of ~resolve ~compute_leaf
                     ~in_progress:(type_ :: in_progress) property)
                  (instantiate ~resolve facts.generics arguments arguments_conditions)))

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

let walk_contents lookups ~(facts_of : Path.t -> Environment.type_facts) ~resolve (type_ : Types.ty)
    =
  let contained = ref [] and recursions = ref [] in
  let rec visit ~enclosing occurrence (type_ : Types.ty) =
    let step_inside ?named ?(defining = []) step =
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
            step_inside (if Types.terminates function_.uses then Function_input else Indirect) input)
          inputs;
        step_inside Indirect output
    | Types.Named { path; arguments } -> (
        match Well_known.find_builtin_type path with
        | Some Array -> List.iter (step_inside In_place) (list_type_arguments arguments)
        | Some _ -> List.iter (step_inside Indirect) (list_type_arguments arguments)
        | None -> (
            contained := (type_, occurrence) :: !contained;
            match
              ( List.find_opt (fun (named, _, _) -> Types.equal named type_) enclosing,
                Definition.find_type_interface lookups path )
            with
            | Some (_, occurrence, defining), _ ->
                recursions := { recursive = type_; occurrence; defining } :: !recursions
            | None, Some ({ shape = Record _ | Sum _; _ } as interface) ->
                if List.length enclosing > recursion_limit then
                  fail_at_recursion_limit
                    (Printf.sprintf "Listing the types that `%s` holds" (Types.show type_));
                let substitution = Types.make_substitution interface.type_generics arguments in
                List.iter
                  (fun (condition, step) ->
                    let condition, defining = resolve (Types.substitute substitution condition) in
                    step_inside ~named:type_ ~defining step condition)
                  (facts_of path).contains
            | None, Some { shape = Todo_type | Builtin_type _; _ } ->
                List.iter (step_inside Indirect) (list_type_arguments arguments)
            | None, _ -> ()))
    | Types.Never | Types.Integer -> ()
    | Types.Error _ | Types.Hole | Types.Variable _ ->
        raise_bug "the contents of the inference type `%s` are listed" (Types.show type_)
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
            ~compute_leaf:(fun type_ -> if is_small type_ then Some [ type_ ] else None)
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
         (is_declared (Well_known.make_path Plain)
         || (property = Copyable && is_declared (Well_known.make_path Copyable)))
  in
  let find_owned_conditions property =
    if is_undeclared property || (property = Plain && allocates) then None
    else find_conditions property field_types
  in
  match interface.shape with
  | Builtin_type _ -> { empty with generics = interface.type_generics }
  | Todo_type ->
      {
        empty with
        generics = interface.type_generics;
        copyable = Never;
        plain = Never;
        holds_function = Always;
      }
  | Record _ | Sum _ ->
      {
        generics = interface.type_generics;
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
           | Types.Named { path = named; _ } when Path.locate_package named = package ->
               named_types := named :: !named_types;
               None
           | _ -> None)
         type_);
    !named_types
  in
  List.concat_map list_named (Types.list_field_types interface)

let compute_component_facts (lookups : Lookups.t) interfaces =
  let map_each select_facts =
    List.fold_left
      (fun facts_by_path (path, interface) ->
        Path.Map.add path (select_facts path interface) facts_by_path)
      Path.Map.empty interfaces
  in
  let rec settle assumed =
    let facts_of path =
      match Path.Map.find_opt path assumed with
      | Some facts -> facts
      | None -> lookups.read_type_facts path
    in
    let next = map_each (fun _ interface -> compute_facts lookups ~facts_of interface) in
    if Path.Map.equal ( = ) next assumed then next else settle next
  in
  Path.Map.bindings
    (settle
       (map_each (fun _ (interface : Types.type_interface) ->
            { empty with generics = interface.type_generics })))

type decision = Holds | Fails | Depends_on of Types.ty

let compute_decision ~is_conjunction conditions =
  match conditions with
  | Some [] -> if is_conjunction then Holds else Fails
  | None -> if is_conjunction then Fails else Holds
  | Some (open_type :: _) -> Depends_on open_type

let decide_property (lookups : Lookups.t) ~list_bounds ~normalize property type_ =
  let compute_leaf type_ =
    let is_bounded trait = has_bound lookups ~list_bounds type_ trait in
    let adds_nothing =
      match property with
      | Copyable ->
          is_bounded (Well_known.make_path Copyable) || is_bounded (Well_known.make_path Plain)
      | Plain -> is_bounded (Well_known.make_path Plain)
      | View -> ( match strip_projections type_ with Types.Parameter _ -> true | _ -> false)
      | Holds_function -> true
    in
    if adds_nothing then Some [] else None
  in
  compute_decision
    ~is_conjunction:
      (match property with Copyable | Plain -> true | View | Holds_function -> false)
    (compute_conditions lookups ~facts_of:lookups.read_type_facts ~resolve:normalize ~compute_leaf
       property (normalize type_))

let decide_storable (lookups : Lookups.t) ~list_bounds ~normalize type_ =
  let compute_leaf type_ =
    if has_bound lookups ~list_bounds type_ (Well_known.make_path Storable) then Some [] else None
  in
  compute_decision ~is_conjunction:true
    (compute_conditions lookups ~facts_of:lookups.read_type_facts ~resolve:normalize ~compute_leaf
       View (normalize type_))

let collect_contents (lookups : Lookups.t) ~normalize type_ =
  walk_contents lookups ~facts_of:lookups.read_type_facts ~resolve:normalize (fst (normalize type_))
