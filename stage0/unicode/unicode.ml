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
          ((first land 0x0F) lsl 12)
          lor ((second land 0x3F) lsl 6)
          lor (byte (offset + 2) land 0x3F)
        in
        (value lsl 3) lor 3
    else -1
  else if first < 0xF5 then
    if continuation (offset + 1) && continuation (offset + 2) && continuation (offset + 3)
    then
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

let code_points text =
  let rec loop offset acc =
    if offset >= String.length text then List.rev acc
    else
      let packed = decode text offset in
      if packed < 0 then invalid_arg "Unicode.code_points: invalid UTF-8"
      else loop (offset + decoded_length packed) (decoded_code_point packed :: acc)
  in
  loop 0 []

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
    Bytes.init 128 (fun value ->
        if find_range ranges ~stride:2 value >= 0 then '\001' else '\000')
  in
  { ascii; ranges }

let has property value =
  if value < 128 then Bytes.unsafe_get property.ascii value <> '\000'
  else find_range property.ranges ~stride:2 value >= 0

let xid_start = property Tables.xid_start
let xid_continue = property Tables.xid_continue
let uppercase_or_titlecase = property Tables.uppercase_or_titlecase
let forbidden = property Tables.forbidden
let identifier_allowed = property Tables.identifier_allowed
let nfc_quick_check_not_yes = property Tables.nfc_quick_check_not_yes
let is_xid_start = has xid_start
let is_xid_continue = has xid_continue
let is_uppercase_or_titlecase = has uppercase_or_titlecase
let is_forbidden = has forbidden
let is_identifier_allowed = has identifier_allowed
let is_nfc_quick_check_yes value = not (has nfc_quick_check_not_yes value)
let is_bidi_control value = find_range Tables.bidi_control ~stride:2 value >= 0
let is_control value = find_range Tables.control ~stride:2 value >= 0

let forbidden_name value =
  let index = find_key Tables.forbidden_name_keys value in
  if index < 0 then None else Some Tables.forbidden_name_values.(index)

let map keys values value =
  let index = find_key keys value in
  if index < 0 then value else values.(index)

let to_lowercase = map Tables.lowercase_keys Tables.lowercase_values
let to_uppercase = map Tables.uppercase_keys Tables.uppercase_values

(* Normalization, following UAX #15. *)

let combining_class value =
  if value < 0x300 then 0
  else
    let index = find_range Tables.combining_class ~stride:3 value in
    if index < 0 then 0 else Tables.combining_class.(index + 2)

(* Hangul syllables are decomposed and composed by arithmetic (Unicode
   section 3.12). *)
let hangul_syllable_base = 0xAC00
let hangul_leading_base = 0x1100
let hangul_vowel_base = 0x1161
let hangul_trailing_base = 0x11A7
let hangul_vowel_count = 21
let hangul_trailing_count = 28
let hangul_syllable_count = 11172

let rec decompose_into output value =
  let syllable = value - hangul_syllable_base in
  if syllable >= 0 && syllable < hangul_syllable_count then begin
    let per_leading = hangul_vowel_count * hangul_trailing_count in
    Dynarray.add_last output (hangul_leading_base + (syllable / per_leading));
    Dynarray.add_last output
      (hangul_vowel_base + (syllable mod per_leading / hangul_trailing_count));
    let trailing = syllable mod hangul_trailing_count in
    if trailing <> 0 then Dynarray.add_last output (hangul_trailing_base + trailing)
  end
  else
    let index = find_key Tables.decomposition_keys value in
    if index < 0 then Dynarray.add_last output value
    else Array.iter (decompose_into output) Tables.decomposition_values.(index)

(* Puts each run of characters with non-zero combining classes in order of
   class, keeping the order of characters with equal classes. *)
let reorder characters =
  let length = Dynarray.length characters in
  for index = 1 to length - 1 do
    let value = Dynarray.get characters index in
    let class_ = combining_class value in
    if class_ <> 0 then begin
      let position = ref index in
      while
        !position > 0
        &&
        let before = combining_class (Dynarray.get characters (!position - 1)) in
        before > class_
      do
        Dynarray.set characters !position (Dynarray.get characters (!position - 1));
        decr position
      done;
      Dynarray.set characters !position value
    end
  done

let decompose_string text =
  let output = Dynarray.create () in
  List.iter (decompose_into output) (code_points text);
  reorder output;
  output

let compose_pair first second =
  let leading = first - hangul_leading_base in
  let vowel = second - hangul_vowel_base in
  let syllable = first - hangul_syllable_base in
  if leading >= 0 && leading < 19 && vowel >= 0 && vowel < hangul_vowel_count then
    hangul_syllable_base + (((leading * hangul_vowel_count) + vowel) * hangul_trailing_count)
  else if
    syllable >= 0
    && syllable < hangul_syllable_count
    && syllable mod hangul_trailing_count = 0
    && second > hangul_trailing_base
    && second < hangul_trailing_base + hangul_trailing_count
  then first + (second - hangul_trailing_base)
  else
    let index = find_key Tables.composition_keys ((first * 0x110000) + second) in
    if index < 0 then -1 else Tables.composition_values.(index)

let compose characters =
  let output = Dynarray.create () in
  (* The index in [output] of the last starter, and the combining class of the
     last character after it, or -1 when the starter is the last character. *)
  let starter = ref (-1) in
  let last_class = ref (-1) in
  Dynarray.iter
    (fun value ->
      let class_ = combining_class value in
      let composite =
        if !starter >= 0 && (!last_class < 0 || !last_class < class_) then
          compose_pair (Dynarray.get output !starter) value
        else -1
      in
      if composite >= 0 then Dynarray.set output !starter composite
      else begin
        Dynarray.add_last output value;
        if class_ = 0 then begin
          starter := Dynarray.length output - 1;
          last_class := -1
        end
        else last_class := class_
      end)
    characters;
  output

let string_of_dynarray characters =
  let buffer = Buffer.create (Dynarray.length characters * 2) in
  Dynarray.iter (encode buffer) characters;
  Buffer.contents buffer

let nfd text = string_of_dynarray (decompose_string text)
let nfc text = string_of_dynarray (compose (decompose_string text))

let is_nfc text =
  List.for_all is_nfc_quick_check_yes (code_points text) || String.equal (nfc text) text

(* Scripts *)

(* A set of scripts, as a sorted list of script numbers, or [None] for the
   set of every script, which is what Common and Inherited characters
   belong to. *)
type scripts = int list option

let script value =
  let index = find_range Tables.script ~stride:3 value in
  if index < 0 then Tables.script_unknown else Tables.script.(index + 2)

(* Script_Extensions, augmented as UTS #39 section 5.1 describes: Han adds
   Han with Bopomofo, Japanese, and Korean; Hiragana and Katakana add
   Japanese; Hangul adds Korean; Bopomofo adds Han with Bopomofo. *)
let augmented_script_extensions value : scripts =
  let index = find_range Tables.script_extensions ~stride:3 value in
  let base =
    if index < 0 then [ script value ]
    else Array.to_list Tables.script_extension_sets.(Tables.script_extensions.(index + 2))
  in
  match base with
  | [ single ] when single = Tables.script_common || single = Tables.script_inherited -> None
  | _ ->
      let added =
        List.concat_map
          (fun number ->
            if number = Tables.script_han then
              [ Tables.script_han_with_bopomofo; Tables.script_japanese; Tables.script_korean ]
            else if number = Tables.script_hiragana || number = Tables.script_katakana then
              [ Tables.script_japanese ]
            else if number = Tables.script_hangul then [ Tables.script_korean ]
            else if number = Tables.script_bopomofo then [ Tables.script_han_with_bopomofo ]
            else [])
          base
      in
      Some (List.sort_uniq compare (base @ added))

let intersect (first : scripts) (second : scripts) : scripts =
  match (first, second) with
  | None, other | other, None -> other
  | Some first, Some second -> Some (List.filter (fun number -> List.mem number second) first)

(* The resolved script set of a string (UTS #39 section 5.1), leaving out the
   characters [skip] selects. *)
let resolved_scripts ?(skip = fun _ -> false) text : scripts =
  List.fold_left
    (fun resolved value ->
      let extensions = augmented_script_extensions value in
      if skip extensions then resolved else intersect resolved extensions)
    None (code_points text)

let is_ascii text = String.for_all (fun character -> Char.code character < 0x80) text

let is_moderately_restrictive text =
  is_ascii text
  ||
  match resolved_scripts text with
  | None -> true
  | Some (_ :: _) -> true
  | Some [] -> (
      let contains_latin = function
        | None -> true
        | Some numbers -> List.mem Tables.script_latin numbers
      in
      match resolved_scripts ~skip:contains_latin text with
      | None -> true
      | Some numbers ->
          let has number = List.mem number numbers in
          has Tables.script_han_with_bopomofo
          || has Tables.script_japanese
          || has Tables.script_korean
          || (numbers <> [] && (not (has Tables.script_cyrillic)) && not (has Tables.script_greek)))

let script_names text =
  List.fold_left
    (fun names value ->
      let number = script value in
      let name = Tables.script_names.(number) in
      if number = Tables.script_common || number = Tables.script_inherited || List.mem name names
      then names
      else names @ [ name ])
    [] (code_points text)

(* Confusables *)

let skeleton text =
  let buffer = Buffer.create (String.length text) in
  Dynarray.iter
    (fun value ->
      let index = find_key Tables.confusable_keys value in
      if index < 0 then encode buffer value
      else Buffer.add_string buffer Tables.confusable_values.(index))
    (decompose_string text);
  nfd (Buffer.contents buffer)
