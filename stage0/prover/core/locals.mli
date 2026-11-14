(** A map from the locals of the core form, which name a frame's values. *)

include Map.S with type key = Core.local
