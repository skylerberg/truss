let version = Unicode_tables.unicode_version

let is_in_ranges ranges value =
  let rec search low high =
    low <= high
    &&
    let middle = (low + high) / 2 in
    if value < ranges.(2 * middle) then search low (middle - 1)
    else value <= ranges.((2 * middle) + 1) || search (middle + 1) high
  in
  search 0 ((Array.length ranges / 2) - 1)

let find_key keys value =
  let rec search low high =
    if low > high then None
    else
      let middle = (low + high) / 2 in
      let key = keys.(middle) in
      if value < key then search low (middle - 1)
      else if value > key then search (middle + 1) high
      else Some middle
  in
  search 0 (Array.length keys - 1)

type property = { ascii : Bytes.t; ranges : int array }

let make_property ranges =
  let ascii = Bytes.init 128 (fun value -> if is_in_ranges ranges value then '\001' else '\000') in
  { ascii; ranges }

let has property scalar_value =
  let code_point = Uchar.to_int scalar_value in
  if code_point < 128 then Bytes.unsafe_get property.ascii code_point <> '\000'
  else is_in_ranges property.ranges code_point

let xid_start = make_property Unicode_tables.xid_start
let xid_continue = make_property Unicode_tables.xid_continue
let forbidden = make_property Unicode_tables.forbidden
let is_xid_start = has xid_start
let is_xid_continue = has xid_continue
let is_forbidden = has forbidden

let is_bidi_control scalar_value =
  is_in_ranges Unicode_tables.bidi_control (Uchar.to_int scalar_value)

let is_control scalar_value = is_in_ranges Unicode_tables.control (Uchar.to_int scalar_value)

let find_forbidden_name scalar_value =
  Option.map
    (Array.get Unicode_tables.forbidden_name_values)
    (find_key Unicode_tables.forbidden_name_keys (Uchar.to_int scalar_value))
