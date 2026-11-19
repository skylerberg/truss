type t = Time | Allocations | Allocated_bytes

let all = [ Time; Allocations; Allocated_bytes ]

let show = function
  | Time -> "time"
  | Allocations -> "allocations"
  | Allocated_bytes -> "allocated_bytes"
