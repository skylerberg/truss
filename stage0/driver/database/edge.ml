type reason = Read | Call | Reference | Claim
type t = { target : Part.t; reasons : reason list }

let add reason reasons =
  if List.mem reason reasons then reasons else List.sort compare (reason :: reasons)

let list_targets reason edges =
  List.filter_map
    (fun edge -> if List.mem reason edge.reasons then Some edge.target else None)
    edges

let keep_reasons is_kept edges =
  List.filter_map
    (fun edge ->
      match List.filter is_kept edge.reasons with
      | [] -> None
      | reasons -> Some { edge with reasons })
    edges

let is_equal_beyond_reads before after =
  let list_sorted edges = List.sort compare (keep_reasons (fun reason -> reason <> Read) edges) in
  list_sorted before = list_sorted after
