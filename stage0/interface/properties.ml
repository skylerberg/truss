(* Whether a type is [Copyable], [Plain], or a view, and what it holds in
   place, worked out from its shape.

   An opaque type has [Copyable] or [Plain] only when it declares so with
   [derives]. It then has the property under the conditions that its fields
   give, as any other type does: [Slice[Element]] is [Plain] whatever
   [Element] is, because it holds a view of its elements, and
   [List[Element]] is [Copyable] when [Element] is. A generic parameter has
   them only when bounded, and so does an associated type of one, by its
   declared bounds. Whether a type is a view is part of its shape, so it is
   worked out from the fields. *)

module T = Types

let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }
let copyable_trait = core "Copyable"
let plain_trait = core "Plain"

(* What a trait's [Self] and parameters stand for in a reference to it. A
   reference with the wrong number of arguments, which lowering reported,
   gives [Self] alone: a parameter left standing equals nothing. *)
let trait_substitution (interface : T.trait_interface) ~self (reference : T.trait_reference) :
    T.substitution =
  (({ owner = reference.trait; name = "Self" } : T.parameter), T.Type self)
  :: Option.value ~default:[] (T.substitution_of interface.trait_generics reference.trait_arguments)

(* Every trait a bound gives a type, with the traits each requires, and
   [Self] in what they require replaced by the type. *)
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

(* The bounds an associated type is declared with, for a base type: the
   [Key: Hash] in [trait Keyed { type Key: Hash }]. *)
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

(* The traits a type is known to have from bounds: a generic parameter's,
   or a projection's declared ones, each with what it requires. *)
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

(* What a type definition says of every type built from it, as conditions
   on what stands for its parameters. Each is worked out once for the
   definition, so a question about [Option[Option[List[Int64]]]] is
   [Option]'s condition asked of its argument, and never a walk of fields
   that could take a type nested in itself for a type that contains
   itself. A condition is a parameter, or an associated type, which is
   decided where what the parameter stands for is known. *)
type facts = {
  copyable : T.ty list option;
      (** What must be [Copyable] for the type to be. [None] when it never is. *)
  plain : T.ty list option;  (** The same for [Plain]. *)
  view : T.ty list option;
      (** What makes the type a view when any of it is one. [None] when it always is. *)
  in_place : T.ty list;
      (** What a value holds in place: in a field of a variant that is not [indirect], outside
          collections' storage, functions, and [any]. *)
}

(* The facts of a type with no fields. *)
let empty = { copyable = Some []; plain = Some []; view = Some []; in_place = [] }

let conditions_of facts = function
  | Copyable -> facts.copyable
  | Plain -> facts.plain
  | View -> facts.view

let type_arguments arguments =
  List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments

(* A definition's conditions for the arguments it is given, each worked
   out by [resolve]. *)
let instantiate ~resolve (interface : T.type_interface) arguments conditions =
  let substitution =
    Option.value ~default:[] (T.substitution_of interface.type_generics arguments)
  in
  List.map (fun condition -> resolve (T.substitute substitution condition)) conditions

(* The conditions of every one of some types: [None] when any gives it. *)
let all conditions types =
  List.fold_left
    (fun found type_ ->
      match (found, conditions type_) with
      | Some found, Some more -> Some (found @ more)
      | _ -> None)
    (Some []) types

(* No program nests types this deep, or writes a condition this large:
   past it a question gets the safe answer, which ends one about types
   whose arguments grow as they contain each other. *)
let limit = 64

(* The conditions a type has a property on: for [Copyable] and [Plain]
   what must have it, for [View] what makes it one, and [None] when it
   never has the first two or always is the third. [leaf] answers for a
   parameter and an associated type, [facts_of] gives a definition's
   facts, and [resolve] works out a definition's condition for its
   arguments.

   Working a condition out can come back to a type whose answer is being
   worked out, when an associated type is that type. [within] holds those
   types, whole, and one met again adds nothing: a type that contains
   itself has a property when nothing else in it says otherwise, and is a
   view only when something else in it is one. *)
let rec conditions database ~facts_of ~resolve ~leaf ?(within = []) property (type_ : T.ty) =
  let each = all (conditions database ~facts_of ~resolve ~leaf ~within property) in
  match type_ with
  | T.Error _ | T.Hole | T.Variable _ | T.Never | T.Literal _ | T.Integer | T.Function _ -> Some []
  | T.Parameter _ | T.Projection _ -> leaf type_
  | T.Any trait -> (
      match property with
      | Copyable ->
          if
            List.exists
              (fun (bound : T.trait_reference) ->
                Path.equal bound.trait copyable_trait || Path.equal bound.trait plain_trait)
              (bound_closure database ~self:type_ trait)
          then Some []
          else None
      | Plain -> None
      | View -> each (List.map snd trait.associated))
  (* A cursor from an [own self] method owns what it goes over; one from a
     [self] method views it. *)
  | T.Cursor { method_ = Method { receiver = Own; _ }; arguments } when property = View ->
      each (type_arguments arguments)
  | T.Cursor _ -> None
  | T.Named { path; arguments } -> (
      match (Intrinsic.builtin_of_path path, property) with
      | Some Storage, Plain | Some View, View | Some Handle, (Copyable | Plain) -> None
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

(* What a value of a type holds in place: the named types, and the
   parameters and associated types, through the arguments of generic types
   that hold them in place. *)
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

(* A definition's facts, from its shape and the facts of what its fields
   name. Nothing is known of its parameters here, so each one a fact turns
   on is a condition, and so is each associated type. *)
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

(* A package's types, each with the group of those that name each other
   in their fields, itself among them. Packages do not depend on each other
   in a cycle, so a group is within one package. *)
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

(* The facts of a group of types, by its first member. A type that
   contains itself is [Copyable] and [Plain] when nothing in it says
   otherwise, and is a view, or holds something in place, only when
   something in it does. So the group starts with the facts of types with no
   fields, and each round works every member's facts out from the others'
   as the round before left them, until nothing changes. A round only adds
   conditions, and there are only so many small ones, so the rounds end. *)
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

(* Whether an associated type is of a generic parameter, or of a type not
   worked out yet, and so of a type the code asking does not have. *)
let rec is_open = function
  | T.Parameter _ | T.Variable _ | T.Hole | T.Error _ -> true
  | T.Projection { base; _ } -> is_open base
  | _ -> false

(* Whether a type has a property, where [bounds] gives what is known of
   each generic parameter in scope and [normalize] replaces an associated
   type by what its [impl] chooses. An associated type that no [impl]
   answers is taken not to be [Copyable] or [Plain], and to be a view. *)
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

(* The named types a value of a type holds in place. *)
let held database ~normalize type_ =
  List.filter_map
    (function T.Named { path; _ } -> Some path | _ -> None)
    (in_place database ~facts_of:(Query.demand database facts) ~resolve:normalize (normalize type_))
