(* The places of a core form that the ownership check tracks. *)

module T = Types

type root = Local of Core.local | Constant of Path.t

(* [Element] names the index call or the slice that selects the elements,
   by its node id and its origin. The check does not compare indexes, so an
   [Element] step stands for some elements of the collection. *)
type step = Field of string | Element of { node : Core.id; origin : Core.origin }
type t = { root : root; steps : step list }

type overlap =
  | Apart
  | Overlap
  | Maybe_apart of Core.origin * Core.origin
      (** The places are different elements of one collection if the two index calls or slices,
          named by their origins, select different elements. The prover decides. *)

(* Two places overlap if one is a prefix of the other. *)
let overlap left right =
  if left.root <> right.root then Apart
  else
    let rec go left right =
      match (left, right) with
      | [], _ | _, [] -> Overlap
      | Field first :: left, Field second :: right ->
          if first = second then go left right else Apart
      | Element first :: left, Element second :: right -> (
          if first.node = second.node then go left right
          else
            match go left right with
            | Apart -> Apart
            | _ -> Maybe_apart (first.origin, second.origin))
      | _ :: left, _ :: right -> go left right
    in
    go left.steps right.steps

let is_prefix prefix place =
  prefix.root = place.root
  &&
  let rec go = function
    | [], _ -> true
    | Field first :: prefix, Field second :: place -> first = second && go (prefix, place)
    | Element _ :: prefix, Element _ :: place -> go (prefix, place)
    | _ -> false
  in
  go (prefix.steps, place.steps)

(* A [List], a [Slice], or an [Array]. An element of one of these is a
   place. An index of any other collection is a call of the collection's
   [at], which lends the element. *)
let is_storage (type_ : T.ty) =
  match type_ with
  | T.Named
      {
        path =
          Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" | "Slice" };
        _;
      } ->
      true
  | _ -> T.is_builtin Array type_

let index_trait : Path.t =
  Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Index" }

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
    when Path.equal trait.trait index_trait && is_storage self_type ->
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

let slice_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "Slice" }

let string_slice_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "text" ] }; name = "StringSlice" }

(* A [Slice] or a [StringSlice]: a view that an owned collection converts
   to, and through which the collection's elements can be changed. *)
let is_slice_type (type_ : T.ty) =
  match type_ with
  | T.Named { path; _ } -> Path.equal path slice_path || Path.equal path string_slice_path
  | _ -> false

(* The slice that a mutation of a place writes through, if there is one:
   the innermost place of a slice type on the way to the mutated place.
   [whole] is true if the place itself is borrowed [mut], and false if it
   is assigned. Assigning a slice variable replaces the view and writes
   through nothing. *)
let rec written_slice ~whole (place : Core.place) : Core.place option =
  if whole && is_slice_type (Core_walk.place_type place) then Some place
  else
    match place with
    | Field { base; _ } -> written_slice ~whole:false base
    | Lent index -> (
        match storage_index index with
        | Some collection ->
            if is_slice_type (Core_walk.place_type collection) then Some collection
            else written_slice ~whole:false collection
        | None -> None)
    | Local _ | Constant _ | Temporary _ -> None

(* The place that a slice views: some elements of its base. *)
let of_slice (slice : Core.expression) : t option =
  match slice.kind with
  | Slice { base; _ } ->
      Option.map
        (fun base ->
          { base with steps = base.steps @ [ Element { node = slice.id; origin = slice.origin } ] })
        (of_core base)
  | _ -> None

(* Whether a core place is part of what a call lends, and is not a tracked
   place. *)
let rec is_lent_part (place : Core.place) =
  match place with
  | Lent index -> Option.is_none (storage_index index)
  | Field { base; _ } -> is_lent_part base
  | Local _ | Constant _ | Temporary _ -> false

(* The place that lends a part, and how: the receiver of the lending call
   that the part comes from. [None] if the place is not a lent part, or if
   the receiver is not a tracked place. *)
let rec lender (place : Core.place) : (t * T.mode) option =
  match place with
  | Field { base; _ } -> lender base
  | Lent
      ({ kind = Call { arguments = Passed { mode; value = Place receiver } :: _; _ }; _ } as call)
    when Option.is_none (storage_index call) ->
      Option.map (fun lent -> (lent, if mode = T.Mut then T.Mut else T.Read)) (of_core receiver)
  | Lent _ | Local _ | Constant _ | Temporary _ -> None
