type t =
  | Integer of Z.t
  | Bytes of string
  | Text of string
  | Array of t list
  | Map of (t * t) list
  | Tag of int * t
  | Bool of bool
  | Null
  | Float of float

let int value = Integer (Z.of_int value)
let two_64 = Z.shift_left Z.one 64

let write_head buffer major (argument : Z.t) =
  let major = major lsl 5 in
  let write_bytes count =
    for index = count - 1 downto 0 do
      let byte = Z.to_int (Z.logand (Z.shift_right argument (8 * index)) (Z.of_int 0xff)) in
      Buffer.add_char buffer (Char.chr byte)
    done
  in
  if Z.lt argument (Z.of_int 24) then
    Buffer.add_char buffer (Char.chr (major lor Z.to_int argument))
  else if Z.lt argument (Z.of_int 0x100) then (
    Buffer.add_char buffer (Char.chr (major lor 24));
    write_bytes 1)
  else if Z.lt argument (Z.of_int 0x10000) then (
    Buffer.add_char buffer (Char.chr (major lor 25));
    write_bytes 2)
  else if Z.lt argument (Z.shift_left Z.one 32) then (
    Buffer.add_char buffer (Char.chr (major lor 26));
    write_bytes 4)
  else (
    Buffer.add_char buffer (Char.chr (major lor 27));
    write_bytes 8)

let write_head_int buffer major argument = write_head buffer major (Z.of_int argument)

let encode_magnitude value =
  let rec encode_bytes value acc =
    if Z.equal value Z.zero then acc
    else
      encode_bytes (Z.shift_right value 8)
        (Char.chr (Z.to_int (Z.logand value (Z.of_int 0xff))) :: acc)
  in
  let list = encode_bytes value [] in
  String.init (List.length list) (List.nth list)

let find_half_bits value =
  let magnitude = Float.abs value in
  let sign = if Float.sign_bit value then 0x8000 else 0 in
  if magnitude = 0.0 then Some sign
  else if Float.is_finite magnitude = false then Some (sign lor 0x7c00)
  else if magnitude < Float.ldexp 1.0 (-14) then
    let scaled = Float.ldexp magnitude 24 in
    if Float.is_integer scaled then Some (sign lor int_of_float scaled) else None
  else
    let _, exponent = Float.frexp magnitude in
    let exponent = exponent - 1 in
    if exponent > 15 then None
    else
      let significand = Float.ldexp magnitude (10 - exponent) in
      if Float.is_integer significand then
        Some (sign lor ((exponent + 15) lsl 10) lor (int_of_float significand - 0x400))
      else None

let write_float buffer value =
  let add_bits count bits =
    for index = count - 1 downto 0 do
      Buffer.add_char buffer
        (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical bits (8 * index)) 0xffL)))
    done
  in
  if Float.is_nan value then Buffer.add_string buffer "\xf9\x7e\x00"
  else
    match find_half_bits value with
    | Some bits ->
        Buffer.add_char buffer '\xf9';
        add_bits 2 (Int64.of_int bits)
    | None ->
        let single = Int32.bits_of_float value in
        if Int32.float_of_bits single = value then (
          Buffer.add_char buffer '\xfa';
          add_bits 4 (Int64.logand (Int64.of_int32 single) 0xffffffffL))
        else (
          Buffer.add_char buffer '\xfb';
          add_bits 8 (Int64.bits_of_float value))

let rec write buffer = function
  | Integer value when Z.sign value >= 0 && Z.lt value two_64 -> write_head buffer 0 value
  | Integer value when Z.sign value < 0 && Z.leq (Z.neg value) two_64 ->
      write_head buffer 1 (Z.sub (Z.neg value) Z.one)
  | Integer value ->
      let tag, argument =
        if Z.sign value >= 0 then (2, value) else (3, Z.sub (Z.neg value) Z.one)
      in
      write_head_int buffer 6 tag;
      write buffer (Bytes (encode_magnitude argument))
  | Bytes bytes ->
      write_head_int buffer 2 (String.length bytes);
      Buffer.add_string buffer bytes
  | Text text ->
      write_head_int buffer 3 (String.length text);
      Buffer.add_string buffer text
  | Array items ->
      write_head_int buffer 4 (List.length items);
      List.iter (write buffer) items
  | Map entries ->
      let encoded = List.map (fun (key, value) -> (encode key, value)) entries in
      let sorted = List.sort (fun (left, _) (right, _) -> String.compare left right) encoded in
      let rec check = function
        | (first, _) :: ((second, _) :: _ as rest) ->
            if String.equal first second then invalid_arg "Cbor.encode: a map repeats a key";
            check rest
        | _ -> ()
      in
      check sorted;
      write_head_int buffer 5 (List.length sorted);
      List.iter
        (fun (key, value) ->
          Buffer.add_string buffer key;
          write buffer value)
        sorted
  | Tag (tag, _) when tag < 0 -> invalid_arg "Cbor.encode: a negative tag"
  | Tag (tag, value) ->
      write_head_int buffer 6 tag;
      write buffer value
  | Bool false -> Buffer.add_char buffer '\xf4'
  | Bool true -> Buffer.add_char buffer '\xf5'
  | Null -> Buffer.add_char buffer '\xf6'
  | Float value -> write_float buffer value

and encode value =
  let buffer = Buffer.create 64 in
  write buffer value;
  Buffer.contents buffer

exception Malformed

let decode_magnitude bytes =
  String.fold_left
    (fun value byte -> Z.logor (Z.shift_left value 8) (Z.of_int (Char.code byte)))
    Z.zero bytes

let decode_half bits =
  let exponent = (bits lsr 10) land 0x1f and significand = bits land 0x3ff in
  let magnitude =
    if exponent = 0 then Float.ldexp (float_of_int significand) (-24)
    else if exponent = 0x1f then if significand = 0 then Float.infinity else Float.nan
    else Float.ldexp (float_of_int (significand lor 0x400)) (exponent - 25)
  in
  if bits land 0x8000 = 0 then magnitude else Float.neg magnitude

let decode encoded =
  let length = String.length encoded in
  let position = ref 0 in
  let read_bytes count =
    if count > length - !position then raise Malformed;
    let bytes = String.sub encoded !position count in
    position := !position + count;
    bytes
  in
  let read_argument info =
    match info with
    | info when info < 24 -> Z.of_int info
    | 24 -> decode_magnitude (read_bytes 1)
    | 25 -> decode_magnitude (read_bytes 2)
    | 26 -> decode_magnitude (read_bytes 4)
    | 27 -> decode_magnitude (read_bytes 8)
    | _ -> raise Malformed
  in
  let read_count info =
    let count = read_argument info in
    if Z.fits_int count && Z.to_int count <= length - !position then Z.to_int count
    else raise Malformed
  in
  let rec read_items count items =
    if count = 0 then List.rev items else read_items (count - 1) (read_item () :: items)
  and read_item () =
    let head = Char.code (read_bytes 1).[0] in
    let info = head land 0x1f in
    match head lsr 5 with
    | 0 -> Integer (read_argument info)
    | 1 -> Integer (Z.pred (Z.neg (read_argument info)))
    | 2 -> Bytes (read_bytes (read_count info))
    | 3 -> Text (read_bytes (read_count info))
    | 4 -> Array (read_items (read_count info) [])
    | 5 ->
        let keys_and_values = read_items (2 * read_count info) [] in
        let rec pair = function
          | key :: value :: rest -> (key, value) :: pair rest
          | [] -> []
          | [ _ ] -> raise Malformed
        in
        Map (pair keys_and_values)
    | 6 -> (
        let tag = read_argument info in
        if not (Z.fits_int tag) then raise Malformed;
        match (Z.to_int tag, read_item ()) with
        | 2, Bytes magnitude -> Integer (decode_magnitude magnitude)
        | 3, Bytes magnitude -> Integer (Z.pred (Z.neg (decode_magnitude magnitude)))
        | tag, item -> Tag (tag, item))
    | _ -> (
        match info with
        | 20 -> Bool false
        | 21 -> Bool true
        | 22 -> Null
        | 25 -> Float (decode_half (String.get_uint16_be (read_bytes 2) 0))
        | 26 -> Float (Int32.float_of_bits (String.get_int32_be (read_bytes 4) 0))
        | 27 -> Float (Int64.float_of_bits (String.get_int64_be (read_bytes 8) 0))
        | _ -> raise Malformed)
  in
  match read_item () with
  | item when !position = length -> Some item
  | _ -> None
  | exception Malformed -> None

let find_int = function
  | Integer value when Z.fits_int value -> Some (Z.to_int value)
  | Integer _ | Bytes _ | Text _ | Array _ | Map _ | Tag _ | Bool _ | Null | Float _ -> None

let find_list decode_item = function
  | Array items ->
      let decoded = List.filter_map decode_item items in
      if List.compare_lengths decoded items = 0 then Some decoded else None
  | Integer _ | Bytes _ | Text _ | Map _ | Tag _ | Bool _ | Null | Float _ -> None
