type t = int
type counter = int ref

let create_counter () = ref 0

let allocate counter =
  let node = !counter in
  incr counter;
  node
