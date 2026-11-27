type 'state key = { id : 'state Type.Id.t; create : unit -> 'state }
type binding = Binding : 'state Type.Id.t * 'state -> binding
type t = { mutable bindings : binding list }

let create () = { bindings = [] }
let make_key create = { id = Type.Id.make (); create }

let read (type state) holder (key : state key) : state =
  let rec find : binding list -> state = function
    | Binding (id, state) :: rest -> (
        match Type.Id.provably_equal id key.id with Some Equal -> state | None -> find rest)
    | [] ->
        let state = key.create () in
        holder.bindings <- Binding (key.id, state) :: holder.bindings;
        state
  in
  find holder.bindings
