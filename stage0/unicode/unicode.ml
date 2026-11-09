module Tables = Unicode_tables

let version = Tables.unicode_version

(* UTF-8 *)

let decoded_code_point packed = packed lsr 3
let decoded_length packed = packed land 7

let decode text offset =
  let length = String.length text in
  let byte index = Char.code (String.unsafe_get text index) in
  let continuation index = index < length && byte index land 0xC0 = 0x80 in
  let first = byte offset in
  if first < 0x80 then (first lsl 3) lor 1
  else if first < 0xC2 then -1
  else if first < 0xE0 then
    if continuation (offset + 1) then
      ((((first land 0x1F) lsl 6) lor (byte (offset + 1) land 0x3F)) lsl 3) lor 2
    else -1
  else if first < 0xF0 then
    if continuation (offset + 1) && continuation (offset + 2) then
      let second = byte (offset + 1) in
      if (first = 0xE0 && second < 0xA0) || (first = 0xED && second >= 0xA0) then -1
      else
        let value =
          ((first land 0x0F) lsl 12) lor ((second land 0x3F) lsl 6) lor (byte (offset + 2) land 0x3F)
        in
        (value lsl 3) lor 3
    else -1
  else if first < 0xF5 then
    if continuation (offset + 1) && continuation (offset + 2) && continuation (offset + 3) then
      let second = byte (offset + 1) in
      if (first = 0xF0 && second < 0x90) || (first = 0xF4 && second >= 0x90) then -1
      else
        let value =
          ((first land 0x07) lsl 18)
          lor ((second land 0x3F) lsl 12)
          lor ((byte (offset + 2) land 0x3F) lsl 6)
          lor (byte (offset + 3) land 0x3F)
        in
        (value lsl 3) lor 4
    else -1
  else -1

let encode buffer value = Buffer.add_utf_8_uchar buffer (Uchar.of_int value)

let of_code_points values =
  let buffer = Buffer.create 16 in
  List.iter (encode buffer) values;
  Buffer.contents buffer

(* Tables *)

(* Binary search in a flat array of ranges with [stride] entries per range,
   [first; last; ...]. Returns the index of the range holding [value], or -1. *)
let find_range ranges ~stride value =
  let rec search low high =
    if low > high then -1
    else
      let middle = (low + high) / 2 in
      let index = middle * stride in
      if value < ranges.(index) then search low (middle - 1)
      else if value > ranges.(index + 1) then search (middle + 1) high
      else index
  in
  search 0 ((Array.length ranges / stride) - 1)

let find_key keys value =
  let rec search low high =
    if low > high then -1
    else
      let middle = (low + high) / 2 in
      let key = keys.(middle) in
      if value < key then search low (middle - 1)
      else if value > key then search (middle + 1) high
      else middle
  in
  search 0 (Array.length keys - 1)

(* A property with a 128-entry table for ASCII in front of its ranges. *)
type property = { ascii : Bytes.t; ranges : int array }

let property ranges =
  let ascii =
    Bytes.init 128 (fun value -> if find_range ranges ~stride:2 value >= 0 then '\001' else '\000')
  in
  { ascii; ranges }

let has property value =
  if value < 128 then Bytes.unsafe_get property.ascii value <> '\000'
  else find_range property.ranges ~stride:2 value >= 0

let xid_start = property Tables.xid_start
let xid_continue = property Tables.xid_continue
let forbidden = property Tables.forbidden
let is_xid_start = has xid_start
let is_xid_continue = has xid_continue
let is_forbidden = has forbidden
let is_bidi_control value = find_range Tables.bidi_control ~stride:2 value >= 0
let is_control value = find_range Tables.control ~stride:2 value >= 0

let forbidden_name value =
  let index = find_key Tables.forbidden_name_keys value in
  if index < 0 then None else Some Tables.forbidden_name_values.(index)
