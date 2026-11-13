let find ?(occurrence = 1) text part =
  let length = String.length part in
  let rec search index seen =
    if index + length > String.length text then None
    else if String.sub text index length = part then
      if seen + 1 = occurrence then Some index else search (index + 1) (seen + 1)
    else search (index + 1) seen
  in
  search 0 0

let contains text part = find text part <> None
