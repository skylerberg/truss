include Map.Make (struct
  type t = Core.local

  let compare = compare
end)
