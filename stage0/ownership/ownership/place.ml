(* The places of a core form that the ownership check tracks. *)
type root =
  | Local of Core.local
  | Temporary of Mir.local
      (** A temporary of the MIR that owns a new value, which is dropped where the MIR makes the
          temporary [Dead]. *)
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

(* A [Slice] or a [StringSlice]: a view that an owned collection converts
   to, and through which the collection's elements can be mutated. *)
let is_slice_type type_ = Types.is_well_known Slice type_ || Types.is_well_known String_slice type_
