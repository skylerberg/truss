type t = Time | Allocations | Allocated_bytes

let all = [ Time; Allocations; Allocated_bytes ]

let show = function
  | Time -> "time"
  | Allocations -> "allocations"
  | Allocated_bytes -> "allocated_bytes"

let find word = List.find_opt (fun metric -> show metric = word) all
