type local = Core_local of Core.local | Mir_local of Mir.local

include Map.Make (struct
  type t = local

  let compare = compare
end)

let make_key (infos : Mir.local_info array) (local : Mir.local) =
  match infos.((local :> int)).kind with
  | Source { local = core; _ } -> Core_local core
  | Temporary | Lent _ -> Mir_local local
