let version = Unicode_tables.unicode_version

module Decoded = struct
  type t = Uchar.utf_decode

  let is_valid = Uchar.utf_decode_is_valid
  let code_point decoded = Uchar.to_int (Uchar.utf_decode_uchar decoded)
  let length = Uchar.utf_decode_length
end

let past_end = Uchar.utf_decode_invalid 0

let decode text offset =
  if offset < String.length text then String.get_utf_8_uchar text offset else past_end

let encode buffer value = Buffer.add_utf_8_uchar buffer (Uchar.of_int value)

let of_code_points values =
  let buffer = Buffer.create 16 in
  List.iter (encode buffer) values;
  Buffer.contents buffer

let in_ranges ranges value =
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

let property ranges =
  let ascii = Bytes.init 128 (fun value -> if in_ranges ranges value then '\001' else '\000') in
  { ascii; ranges }

let has property value =
  if value < 128 then Bytes.unsafe_get property.ascii value <> '\000'
  else in_ranges property.ranges value

let xid_start = property Unicode_tables.xid_start
let xid_continue = property Unicode_tables.xid_continue
let forbidden = property Unicode_tables.forbidden
let is_xid_start = has xid_start
let is_xid_continue = has xid_continue
let is_forbidden = has forbidden
let is_bidi_control = in_ranges Unicode_tables.bidi_control
let is_control = in_ranges Unicode_tables.control

let forbidden_name value =
  Option.map
    (Array.get Unicode_tables.forbidden_name_values)
    (find_key Unicode_tables.forbidden_name_keys value)
