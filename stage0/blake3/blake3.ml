(* BLAKE3, following the specification's reference implementation. Words are
   32 bits, held in OCaml's native integers and masked after each
   operation. *)

(* Words are held in native integers, which need more than 32 bits. *)
let () = assert (Sys.int_size >= 63)
let mask = 0xffffffff
let[@inline] rotate_right value count = (value lsr count) lor (value lsl (32 - count)) land mask

let initial =
  [|
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19;
  |]

let permutation = [| 2; 6; 3; 10; 7; 0; 4; 13; 1; 11; 12; 5; 9; 14; 15; 8 |]
let chunk_start = 1
let chunk_end = 2
let parent = 4
let root = 8
let derive_key_context = 32
let derive_key_material = 64
let block_length = 64
let chunk_length = 1024

(* Which of the block's words each of the seven rounds mixes in, in order,
   sixteen to a round. The specification permutes the block's words after
   each round; these are the same words, by their places in the block as it
   was. *)
let schedule =
  let rounds = Array.make (7 * 16) 0 in
  let current = ref (Array.init 16 Fun.id) in
  for round = 0 to 6 do
    Array.blit !current 0 rounds (round * 16) 16;
    current := Array.init 16 (fun position -> !current.(permutation.(position)))
  done;
  rounds

let[@inline] word (block : int array) base place =
  Array.unsafe_get block (Array.unsafe_get schedule (base + place))

(* The compression function. Nearly all of a hash's time is spent here, so
   its sixteen words are local variables, which stay in registers, and each
   mixing step is written out. *)
let compress (chaining : int array) (block : int array) ~counter ~length ~flags =
  let v0 = ref (Array.unsafe_get chaining 0) in
  let v1 = ref (Array.unsafe_get chaining 1) in
  let v2 = ref (Array.unsafe_get chaining 2) in
  let v3 = ref (Array.unsafe_get chaining 3) in
  let v4 = ref (Array.unsafe_get chaining 4) in
  let v5 = ref (Array.unsafe_get chaining 5) in
  let v6 = ref (Array.unsafe_get chaining 6) in
  let v7 = ref (Array.unsafe_get chaining 7) in
  let v8 = ref (Array.unsafe_get initial 0) in
  let v9 = ref (Array.unsafe_get initial 1) in
  let v10 = ref (Array.unsafe_get initial 2) in
  let v11 = ref (Array.unsafe_get initial 3) in
  let v12 = ref (counter land mask) in
  let v13 = ref ((counter lsr 32) land mask) in
  let v14 = ref length in
  let v15 = ref flags in
  for round = 0 to 6 do
    let base = round * 16 in
    (* Down the four columns *)
    v0 := (!v0 + !v4 + word block base 0) land mask;
    v12 := rotate_right (!v12 lxor !v0) 16;
    v8 := (!v8 + !v12) land mask;
    v4 := rotate_right (!v4 lxor !v8) 12;
    v0 := (!v0 + !v4 + word block base 1) land mask;
    v12 := rotate_right (!v12 lxor !v0) 8;
    v8 := (!v8 + !v12) land mask;
    v4 := rotate_right (!v4 lxor !v8) 7;
    v1 := (!v1 + !v5 + word block base 2) land mask;
    v13 := rotate_right (!v13 lxor !v1) 16;
    v9 := (!v9 + !v13) land mask;
    v5 := rotate_right (!v5 lxor !v9) 12;
    v1 := (!v1 + !v5 + word block base 3) land mask;
    v13 := rotate_right (!v13 lxor !v1) 8;
    v9 := (!v9 + !v13) land mask;
    v5 := rotate_right (!v5 lxor !v9) 7;
    v2 := (!v2 + !v6 + word block base 4) land mask;
    v14 := rotate_right (!v14 lxor !v2) 16;
    v10 := (!v10 + !v14) land mask;
    v6 := rotate_right (!v6 lxor !v10) 12;
    v2 := (!v2 + !v6 + word block base 5) land mask;
    v14 := rotate_right (!v14 lxor !v2) 8;
    v10 := (!v10 + !v14) land mask;
    v6 := rotate_right (!v6 lxor !v10) 7;
    v3 := (!v3 + !v7 + word block base 6) land mask;
    v15 := rotate_right (!v15 lxor !v3) 16;
    v11 := (!v11 + !v15) land mask;
    v7 := rotate_right (!v7 lxor !v11) 12;
    v3 := (!v3 + !v7 + word block base 7) land mask;
    v15 := rotate_right (!v15 lxor !v3) 8;
    v11 := (!v11 + !v15) land mask;
    v7 := rotate_right (!v7 lxor !v11) 7;
    (* Along the four diagonals *)
    v0 := (!v0 + !v5 + word block base 8) land mask;
    v15 := rotate_right (!v15 lxor !v0) 16;
    v10 := (!v10 + !v15) land mask;
    v5 := rotate_right (!v5 lxor !v10) 12;
    v0 := (!v0 + !v5 + word block base 9) land mask;
    v15 := rotate_right (!v15 lxor !v0) 8;
    v10 := (!v10 + !v15) land mask;
    v5 := rotate_right (!v5 lxor !v10) 7;
    v1 := (!v1 + !v6 + word block base 10) land mask;
    v12 := rotate_right (!v12 lxor !v1) 16;
    v11 := (!v11 + !v12) land mask;
    v6 := rotate_right (!v6 lxor !v11) 12;
    v1 := (!v1 + !v6 + word block base 11) land mask;
    v12 := rotate_right (!v12 lxor !v1) 8;
    v11 := (!v11 + !v12) land mask;
    v6 := rotate_right (!v6 lxor !v11) 7;
    v2 := (!v2 + !v7 + word block base 12) land mask;
    v13 := rotate_right (!v13 lxor !v2) 16;
    v8 := (!v8 + !v13) land mask;
    v7 := rotate_right (!v7 lxor !v8) 12;
    v2 := (!v2 + !v7 + word block base 13) land mask;
    v13 := rotate_right (!v13 lxor !v2) 8;
    v8 := (!v8 + !v13) land mask;
    v7 := rotate_right (!v7 lxor !v8) 7;
    v3 := (!v3 + !v4 + word block base 14) land mask;
    v14 := rotate_right (!v14 lxor !v3) 16;
    v9 := (!v9 + !v14) land mask;
    v4 := rotate_right (!v4 lxor !v9) 12;
    v3 := (!v3 + !v4 + word block base 15) land mask;
    v14 := rotate_right (!v14 lxor !v3) 8;
    v9 := (!v9 + !v14) land mask;
    v4 := rotate_right (!v4 lxor !v9) 7
  done;
  [|
    !v0 lxor !v8;
    !v1 lxor !v9;
    !v2 lxor !v10;
    !v3 lxor !v11;
    !v4 lxor !v12;
    !v5 lxor !v13;
    !v6 lxor !v14;
    !v7 lxor !v15;
  |]

(* The sixteen little-endian words of up to 64 bytes of [input] from
   [offset], padded with zeros. *)
let words input offset length =
  let block = Array.make 16 0 in
  let whole = length / 4 in
  for place = 0 to whole - 1 do
    block.(place) <- Int32.to_int (String.get_int32_le input (offset + (place * 4))) land mask
  done;
  for position = whole * 4 to length - 1 do
    block.(whole) <-
      block.(whole) lor (Char.code input.[offset + position] lsl (8 * (position land 3)))
  done;
  block

(* What finishing a chunk or a parent node needs: compressed without [root]
   it is a chaining value, and with it the digest. *)
type output = { chaining : int array; block : int array; counter : int; length : int; flags : int }

let chaining_value ?(flags = 0) output =
  compress output.chaining output.block ~counter:output.counter ~length:output.length
    ~flags:(output.flags lor flags)

(* The output of the chunk numbered [counter], which holds [length] bytes of
   [input] from [offset]. Every block but the last is compressed here. [key]
   and [mode] are the chaining value and the flags that the hash's mode
   starts every chunk and parent node with. *)
let chunk_output ~key ~mode input ~offset ~length ~counter =
  let chaining = ref key in
  let blocks = if length = 0 then 1 else (length + block_length - 1) / block_length in
  for index = 0 to blocks - 2 do
    chaining :=
      compress !chaining
        (words input (offset + (index * block_length)) block_length)
        ~counter ~length:block_length
        ~flags:(mode lor if index = 0 then chunk_start else 0)
  done;
  let last_offset = (blocks - 1) * block_length in
  let last_length = length - last_offset in
  {
    chaining = !chaining;
    block = words input (offset + last_offset) last_length;
    counter;
    length = last_length;
    flags = mode lor (if blocks = 1 then chunk_start else 0) lor chunk_end;
  }

let parent_output ~key ~mode left right =
  {
    chaining = key;
    block = Array.append left right;
    counter = 0;
    length = block_length;
    flags = mode lor parent;
  }

(* The eight words of the root's chaining value, which are the first 32
   bytes of the hash's output. *)
let root_words ~key ~mode input =
  let total = String.length input in
  let chunks = if total = 0 then 1 else (total + chunk_length - 1) / chunk_length in
  (* The stack of chaining values of complete subtrees, merged as the
     reference implementation merges them: after chunk [n], once for each
     trailing zero bit of [n]. *)
  let stack = ref [] in
  for index = 0 to chunks - 2 do
    let output =
      chunk_output ~key ~mode input ~offset:(index * chunk_length) ~length:chunk_length
        ~counter:index
    in
    let value = ref (chaining_value output) in
    let finished = ref (index + 1) in
    while !finished land 1 = 0 do
      (match !stack with
      | left :: rest ->
          value := chaining_value (parent_output ~key ~mode left !value);
          stack := rest
      | [] -> assert false);
      finished := !finished lsr 1
    done;
    stack := !value :: !stack
  done;
  let last_offset = (chunks - 1) * chunk_length in
  let last =
    chunk_output ~key ~mode input ~offset:last_offset ~length:(total - last_offset)
      ~counter:(chunks - 1)
  in
  let output =
    List.fold_left
      (fun right left -> parent_output ~key ~mode left (chaining_value right))
      last !stack
  in
  chaining_value ~flags:root output

let bytes_of_words words =
  let digest = Bytes.create 32 in
  Array.iteri (fun place word -> Bytes.set_int32_le digest (place * 4) (Int32.of_int word)) words;
  Bytes.unsafe_to_string digest

let hash input = bytes_of_words (root_words ~key:initial ~mode:0 input)

let derive_key ~context =
  let key = root_words ~key:initial ~mode:derive_key_context context in
  fun material -> bytes_of_words (root_words ~key ~mode:derive_key_material material)

let to_hex digest =
  String.concat ""
    (List.init (String.length digest) (fun index ->
         Printf.sprintf "%02x" (Char.code digest.[index])))
