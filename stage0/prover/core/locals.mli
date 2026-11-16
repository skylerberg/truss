type local = Core_local of Core.local | Mir_local of Mir.local

include Map.S with type key = local

val make_key : Mir.local_info array -> Mir.local -> local
