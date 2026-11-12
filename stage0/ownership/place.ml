(* The places of a core form that the ownership check tracks. *)
type root =
  | Local of Core.local
  | Constant of Path.t
  | Environment
      (** A lambda's environment record, which stores the lambda's captures. It is a local of the
          enclosing function. Every capturing lambda views it. *)

(* [Element] identifies the index call or the slice that selects the
   elements, by its node id and its origin. The check does not compare index
   values, so an [Element] step denotes an unknown subset of the
   collection's elements. *)
type step = Field of string | Element of { node : Core.id; origin : Core.origin }
type t = { root : root; steps : step list }

type overlap =
  | Disjoint
  | Overlapping
  | Maybe_disjoint of Core.origin * Core.origin
      (** The places are disjoint if the two index calls or slices, identified by their origins,
          select disjoint elements of one collection. The prover decides. *)

(* Two places overlap if one is a prefix of the other. *)
let overlap left right =
  if left.root <> right.root then Disjoint
  else
    let rec steps_overlap left right =
      match (left, right) with
      | [], _ | _, [] -> Overlapping
      | Field first :: left, Field second :: right ->
          if first = second then steps_overlap left right else Disjoint
      | Element first :: left, Element second :: right -> (
          if first.node = second.node then steps_overlap left right
          else
            match steps_overlap left right with
            | Disjoint -> Disjoint
            | _ -> Maybe_disjoint (first.origin, second.origin))
      | _ :: left, _ :: right -> steps_overlap left right
    in
    steps_overlap left.steps right.steps

let is_prefix prefix place =
  prefix.root = place.root
  &&
  let rec steps_prefix = function
    | [], _ -> true
    | Field first :: prefix, Field second :: place -> first = second && steps_prefix (prefix, place)
    | Element _ :: prefix, Element _ :: place -> steps_prefix (prefix, place)
    | _ -> false
  in
  steps_prefix (prefix.steps, place.steps)

(* A [List], a [Slice], or an [Array]. An element of one of these is a
   place. An index of any other collection is a call of the collection's
   [at], which lends the element. *)
let is_storage type_ =
  Types.is_well_known List type_ || Types.is_well_known Slice type_ || Types.is_builtin Array type_

(* If the expression is an index of a [List], a [Slice], or an [Array],
   the collection that is indexed. *)
let storage_index (value : Core.expression) : Core.place option =
  match value.kind with
  | Call
      {
        callee = Trait_method { trait; name = "at"; self_type; _ };
        arguments = Passed { value = Place collection; _ } :: _;
        _;
      }
    when Well_known.is Index trait.trait && is_storage self_type ->
      Some collection
  | _ -> None

(* The tracked place that a core place denotes. [None] for a temporary and
   for a part that a call lends, other than an element of a [List], a
   [Slice], or an [Array]. *)
let rec of_core (place : Core.place) : t option =
  let with_step base step =
    Option.map (fun base -> { base with steps = base.steps @ [ step ] }) (of_core base)
  in
  match place with
  | Local { local; _ } -> Some { root = Local local; steps = [] }
  | Constant { path; _ } -> Some { root = Constant path; steps = [] }
  | Field { base; field; _ } -> with_step base (Field field)
  | Lent index -> (
      match storage_index index with
      | Some collection -> with_step collection (Element { node = index.id; origin = index.origin })
      | None -> None)
  | Temporary _ -> None

(* A [Slice] or a [StringSlice]: a view that an owned collection converts
   to, and through which the collection's elements can be mutated. *)
let is_slice_type type_ = Types.is_well_known Slice type_ || Types.is_well_known String_slice type_
