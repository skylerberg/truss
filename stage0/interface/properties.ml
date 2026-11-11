(* The properties of a type that are derived from its shape: [Copyable],
   [Plain], the view property, and the types that it holds in place.

   An opaque type is [Copyable] or [Plain] only when it declares so with
   [derives]. It then has the property under the conditions that its fields
   give, as any other type does: [Slice[Element]] is [Plain] for every
   [Element], because it holds a view of its elements, and [List[Element]]
   is [Copyable] when [Element] is. A generic parameter has these properties
   only when it is bounded by them, and an associated type of a parameter
   only when its declared bounds include them. The view property is part of
   a type's shape, so it is derived from the fields. *)

module T = Types

let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }
let copyable_trait = core "Copyable"
let plain_trait = core "Plain"
let storable_trait = core "Storable"

(* The substitution for a trait reference: the types that the trait's [Self]
   and parameters are instantiated with. A reference with the wrong number
   of arguments, which lowering reported, substitutes [Self] only: an
   unsubstituted parameter equals no type. *)
let trait_substitution (interface : T.trait_interface) ~self (reference : T.trait_reference) :
    T.substitution =
  (({ owner = reference.trait; name = "Self" } : T.parameter), T.Type self)
  :: Option.value ~default:[] (T.substitution_of interface.trait_generics reference.trait_arguments)

(* The closure of a bound on a type: the bound's trait and, transitively,
   the traits that it requires, with [Self] in the required traits
   substituted by the type. *)
let rec bound_closure database ?(seen = []) ~self (bound : T.trait_reference) =
  if List.exists (fun (other : T.trait_reference) -> Path.equal other.trait bound.trait) seen then
    []
  else
    let required =
      match Query.demand database Environment.trait_interface bound.trait with
      | Some trait ->
          List.map (T.substitute_trait (trait_substitution trait ~self bound)) trait.requires
      | None -> []
    in
    bound :: List.concat_map (bound_closure database ~seen:(bound :: seen) ~self) required

(* The declared bounds of an associated type, for a base type: the [Key:
   Hash] in [trait Keyed { type Key: Hash }]. *)
let associated_bounds database ~base (trait : T.trait_reference) name =
  match Query.demand database Environment.trait_interface trait.trait with
  | Some interface -> (
      match
        List.find_opt
          (fun (associated : T.associated_type) -> associated.associated_name = name)
          interface.associated_types
      with
      | Some associated ->
          List.map
            (T.substitute_trait (trait_substitution interface ~self:base trait))
            associated.associated_bounds
      | None -> [])
  | None -> []

(* The traits that a type implements according to bounds: the bounds of a
   generic parameter, or the declared bounds of a projection, each with its
   closure. *)
let known_bounds database ~bounds (type_ : T.ty) =
  match type_ with
  | T.Parameter parameter -> List.concat_map (bound_closure database ~self:type_) (bounds parameter)
  | T.Projection { base; trait; name } ->
      List.concat_map
        (bound_closure database ~self:type_)
        (associated_bounds database ~base trait name)
  | _ -> []

let has_bound database ~bounds type_ trait =
  List.exists
    (fun (bound : T.trait_reference) -> Path.equal bound.trait trait)
    (known_bounds database ~bounds type_)

type property = Copyable | Plain | View

(* The facts that a type definition gives about every instantiation of it,
   as conditions on its type arguments. They are computed once per
   definition. A query about [Option[Option[List[Int64]]]] instantiates
   [Option]'s condition with its argument. It never traverses fields, so a
   type nested in itself cannot be mistaken for a recursive type. A
   condition is a parameter or an associated type, and it is decided where
   the parameter's instantiation is known. *)
type facts = {
  copyable : T.ty list option;
      (** The types that must be [Copyable] for the type to be. [None] if the type never is. *)
  plain : T.ty list option;  (** The same for [Plain]. *)
  view : T.ty list option;
      (** The types of which any one makes the type a view. [None] if the type always is one. *)
  in_place : T.ty list;
      (** The types that a value holds in place: in a field of a variant that is not [indirect], and
          not inside a collection's storage, a function, or an [any]. *)
}

(* The facts of a type with no fields. *)
let empty = { copyable = Some []; plain = Some []; view = Some []; in_place = [] }

let conditions_of facts = function
  | Copyable -> facts.copyable
  | Plain -> facts.plain
  | View -> facts.view

let type_arguments arguments =
  List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments

(* A definition's conditions, instantiated with the given type arguments and
   normalized by [resolve]. *)
let instantiate ~resolve (interface : T.type_interface) arguments conditions =
  let substitution =
    Option.value ~default:[] (T.substitution_of interface.type_generics arguments)
  in
  List.map (fun condition -> resolve (T.substitute substitution condition)) conditions

(* The conditions of all of some types. [None] if any of them gives [None]. *)
let all conditions types =
  List.fold_left
    (fun found type_ ->
      match (found, conditions type_) with
      | Some found, Some more -> Some (found @ more)
      | _ -> None)
    (Some []) types

(* A depth limit. No program nests types this deeply or has a condition this
   large. Past the limit a query gets the conservative answer, which
   terminates a query about types whose arguments grow as they contain each
   other. *)
let limit = 64

(* The conditions under which a type has a property. For [Copyable] and
   [Plain]: the types that must have it. For [View]: the types of which any
   one makes the type a view. [None] if the type never has the first two, or
   always is a view. [leaf] decides a parameter and an associated type,
   [facts_of] gives a definition's facts, and [resolve] normalizes a
   definition's condition for its arguments.

   Computing a condition can reach a type whose answer is being computed,
   when an associated type is that type. [within] holds the types in
   progress. A type that is reached again adds no condition: a recursive
   type has a property unless another part of it prevents that, and is a
   view only if another part of it is. *)
let rec conditions database ~facts_of ~resolve ~leaf ?(within = []) property (type_ : T.ty) =
  let each = all (conditions database ~facts_of ~resolve ~leaf ~within property) in
  match type_ with
  | T.Error _ | T.Hole | T.Variable _ | T.Never | T.Literal _ | T.Integer -> Some []
  (* A function value may be a capturing lambda, which views its captures.
     The type does not state whether the function captures, so every
     function type is a view type. *)
  | T.Function _ -> if property = View then None else Some []
  | T.Parameter _ | T.Projection _ -> leaf type_
  | T.Any trait -> (
      let requires traits =
        List.exists
          (fun (bound : T.trait_reference) -> List.exists (Path.equal bound.trait) traits)
          (bound_closure database ~self:type_ trait)
      in
      match property with
      | Copyable -> if requires [ copyable_trait; plain_trait ] then Some [] else None
      | Plain -> None
      (* The type does not name the type of the value that it holds, so an
         [any] is a view type unless its trait requires [Storable]. *)
      | View -> if requires [ storable_trait ] then Some [] else None)
  (* A cursor from an [own self] method owns the collection that it iterates
     over. A cursor from a [self] method views it. *)
  | T.Cursor { method_ = Method { receiver = Own; _ }; arguments } when property = View ->
      each (type_arguments arguments)
  | T.Cursor _ -> None
  | T.Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, property) with
      | Some Storage, Plain | Some View, View | Some Handle, (Copyable | Plain) -> None
      (* Every copy of a [Shared] refers to one value, so copying it copies
         no value. It holds a view only if its value does. *)
      | Some Shared, Copyable -> Some []
      | Some Shared, Plain -> None
      | Some Shared, View -> each (type_arguments arguments)
      | Some (Storage | Array), _ -> each (type_arguments arguments)
      | Some _, _ -> Some []
      | None, _ -> (
          match Query.demand database Environment.type_interface path with
          | None -> if property = View then Some [] else None
          | Some _ when List.exists (T.equal type_) within -> Some []
          | Some _ when List.length within > limit -> None
          | Some interface ->
              Option.bind
                (conditions_of (facts_of path) property)
                (fun found ->
                  all
                    (conditions database ~facts_of ~resolve ~leaf ~within:(type_ :: within) property)
                    (instantiate ~resolve interface arguments found))))

(* The types that a value of a type holds in place: named types, parameters,
   and associated types, including those reached through the arguments of
   generic types that hold their arguments in place. *)
let rec in_place database ~facts_of ~resolve ?(within = []) (type_ : T.ty) =
  match type_ with
  | T.Parameter _ | T.Projection _ -> [ type_ ]
  | T.Named { path; arguments } -> (
      match Intrinsic.builtin_of_path path with
      | Some Array ->
          List.concat_map (in_place database ~facts_of ~resolve ~within) (type_arguments arguments)
      | Some _ -> []
      | None when List.exists (T.equal type_) within || List.length within > limit -> []
      | None ->
          type_
          ::
          (match Query.demand database Environment.type_interface path with
          | Some interface ->
              List.concat_map
                (in_place database ~facts_of ~resolve ~within:(type_ :: within))
                (instantiate ~resolve interface arguments (facts_of path).in_place)
          | None -> []))
  | _ -> []

let size type_ =
  let count = ref 0 in
  ignore
    (T.map
       (fun _ ->
         incr count;
         None)
       type_);
  !count

(* A definition's facts, derived from its shape and from the facts of its
   field types. The definition's parameters are uninstantiated here, so each
   parameter that a fact depends on is a condition, and so is each
   associated type. *)
let facts_from database ~facts_of (interface : T.type_interface) =
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
      List.map (fun (field : T.field) -> (indirect, field.field_type)) fields
    in
    match interface.shape with
    | Record fields -> of_variant false fields
    | Sum variants ->
        List.concat_map
          (fun (variant : T.variant) ->
            of_variant variant.indirect (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ | Error_shape _ -> []
  in
  let contents = List.map snd fields in
  let declared trait = List.exists (Path.equal trait) interface.derives in
  let allocates =
    match interface.shape with
    | Sum variants -> List.exists (fun (variant : T.variant) -> variant.indirect) variants
    | _ -> false
  in
  let undeclared property =
    interface.opaque
    && not (declared plain_trait || (property = Copyable && declared copyable_trait))
  in
  let owned property =
    if undeclared property || (property = Plain && allocates) then None
    else conditions property contents
  in
  match interface.shape with
  | Error_shape _ | Builtin_type _ -> empty
  | Todo_type -> { empty with copyable = None; plain = None }
  | Record _ | Sum _ ->
      {
        copyable = owned Copyable;
        plain = owned Plain;
        view = conditions View contents;
        in_place =
          List.sort_uniq compare
            (List.concat_map
               (fun (indirect, type_) ->
                 if indirect then []
                 else
                   List.filter
                     (function
                       | (T.Parameter _ | T.Projection _) as condition -> small condition
                       | _ -> false)
                     (in_place database ~facts_of ~resolve:Fun.id type_))
               fields);
      }

(* The types of a package, each with its group of mutually recursive types:
   the types that name each other in their fields, including itself.
   Packages cannot depend on each other in a cycle, so a group is within one
   package. *)
let groups =
  Query.query ~name:"type_groups" ~phase:Interfaces ~show:Fun.id (fun database package ->
      let types =
        List.filter_map
          (fun (declaration : Resolve.Names.declaration) ->
            if declaration.kind = Type && declaration.ordinal = 0 then Some declaration.path
            else None)
          (Query.demand database Resolve.Names.package_declarations package)
      in
      let known = Path.Set.of_list types in
      let named type_ =
        let found = ref [] in
        ignore
          (T.map
             (function
               | T.Named { path; _ } when Path.Set.mem path known ->
                   found := path :: !found;
                   None
               | _ -> None)
             type_);
        !found
      in
      let successors path =
        match Query.demand database Environment.type_interface path with
        | Some { shape = Record fields; _ } ->
            List.concat_map (fun (field : T.field) -> named field.field_type) fields
        | Some { shape = Sum variants; _ } ->
            List.concat_map
              (fun (variant : T.variant) ->
                List.concat_map
                  (fun (field : T.field) -> named field.field_type)
                  (Option.value ~default:[] variant.fields))
              variants
        | _ -> []
      in
      List.fold_left
        (fun groups group ->
          List.fold_left (fun groups member -> Path.Map.add member group groups) groups group)
        Path.Map.empty
        (Components.of_graph ~compare:Path.compare ~successors types))

let group =
  Query.query ~name:"type_group" ~phase:Interfaces ~show:Path.show (fun database path ->
      Option.value ~default:[ path ]
        (Path.Map.find_opt path (Query.demand database groups (Path.package path))))

(* The facts of a group of mutually recursive types, keyed by the group's
   first member. A recursive type is [Copyable] and [Plain] unless a part of
   it prevents that, and is a view, or holds a type in place, only if a part
   of it does. So the facts are a fixed point: the iteration starts from the
   facts of the types without fields, and each round recomputes every
   member's facts from the others' facts of the previous round, until none
   changes. A round only adds conditions, and the set of possible conditions
   is finite, so the iteration terminates. *)
let rec group_facts =
  lazy
    (Query.query ~name:"type_group_facts" ~phase:Interfaces ~saved:true ~show:Path.show
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
             (fun found (path, interface) -> Path.Map.add path (facts path interface) found)
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

(* The facts of a type definition. *)
let facts = Query.query ~name:"type_facts" ~phase:Interfaces ~show:Path.show facts_of

(* Whether the base of an associated type is a generic parameter or a type
   that is not inferred yet, so that the projection cannot be normalized
   here. *)
let rec is_open = function
  | T.Parameter _ | T.Variable _ | T.Hole | T.Error _ -> true
  | T.Projection { base; _ } -> is_open base
  | _ -> false

(* Whether a type has a property. [bounds] gives the bounds of each generic
   parameter in scope, and [normalize] replaces an associated type by its
   definition in the matching [impl]. An associated type that no [impl]
   defines is assumed not to be [Copyable] or [Plain], and to be a view. *)
let has database ~bounds ~normalize property type_ =
  let leaf type_ =
    let bounded trait = has_bound database ~bounds type_ trait in
    let adds_nothing =
      match property with
      | Copyable -> bounded copyable_trait || bounded plain_trait
      | Plain -> bounded plain_trait
      | View -> is_open type_
    in
    if adds_nothing then Some [] else None
  in
  let found =
    conditions database ~facts_of:(Query.demand database facts) ~resolve:normalize ~leaf property
      (normalize type_)
  in
  match property with Copyable | Plain -> Option.is_some found | View -> Option.is_none found

(* Whether a type is [Storable]: it is not a view type for every
   instantiation of its generic parameters. A generic parameter, or an
   associated type of one, is [Storable] only when it is bounded by
   [Storable], because it may be instantiated with a view type. So
   [List[Element]] is [Storable] where [Element] is. *)
let storable database ~bounds ~normalize type_ =
  let leaf type_ = if has_bound database ~bounds type_ storable_trait then Some [] else None in
  Option.is_some
    (conditions database ~facts_of:(Query.demand database facts) ~resolve:normalize ~leaf View
       (normalize type_))

(* The named types a value of a type holds in place. *)
let held database ~normalize type_ =
  List.filter_map
    (function T.Named { path; _ } -> Some path | _ -> None)
    (in_place database ~facts_of:(Query.demand database facts) ~resolve:normalize (normalize type_))
