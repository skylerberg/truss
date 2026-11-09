(* BLAKE3, following the specification's reference implementation. Words are
   32 bits, held in OCaml's native integers and masked after each
   operation. *)

let mask = 0xffffffff
let add a b = (a + b) land mask
let rotate_right value count = (value lsr count) lor (value lsl (32 - count)) land mask

let initial =
  [|
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19;
  |]

let permutation = [| 2; 6; 3; 10; 7; 0; 4; 13; 1; 11; 12; 5; 9; 14; 15; 8 |]
let chunk_start = 1
let chunk_end = 2
let parent = 4
let root = 8
let block_length = 64
let chunk_length = 1024

let mix state a b c d x y =
  state.(a) <- add (add state.(a) state.(b)) x;
  state.(d) <- rotate_right (state.(d) lxor state.(a)) 16;
  state.(c) <- add state.(c) state.(d);
  state.(b) <- rotate_right (state.(b) lxor state.(c)) 12;
  state.(a) <- add (add state.(a) state.(b)) y;
  state.(d) <- rotate_right (state.(d) lxor state.(a)) 8;
  state.(c) <- add state.(c) state.(d);
  state.(b) <- rotate_right (state.(b) lxor state.(c)) 7

let round state message =
  mix state 0 4 8 12 message.(0) message.(1);
  mix state 1 5 9 13 message.(2) message.(3);
  mix state 2 6 10 14 message.(4) message.(5);
  mix state 3 7 11 15 message.(6) message.(7);
  mix state 0 5 10 15 message.(8) message.(9);
  mix state 1 6 11 12 message.(10) message.(11);
  mix state 2 7 8 13 message.(12) message.(13);
  mix state 3 4 9 14 message.(14) message.(15)

(* The compression function: eight words of chaining value and sixteen of
   block give sixteen words, of which the first eight are the next chaining
   value. *)
let compress chaining block ~counter ~length ~flags =
  let state =
    [|
      chaining.(0);
      chaining.(1);
      chaining.(2);
      chaining.(3);
      chaining.(4);
      chaining.(5);
      chaining.(6);
      chaining.(7);
      initial.(0);
      initial.(1);
      initial.(2);
      initial.(3);
      counter land mask;
      (counter lsr 32) land mask;
      length;
      flags;
    |]
  in
  let message = Array.copy block in
  for index = 1 to 7 do
    round state message;
    if index < 7 then begin
      let permuted = Array.init 16 (fun position -> message.(permutation.(position))) in
      Array.blit permuted 0 message 0 16
    end
  done;
  for index = 0 to 7 do
    state.(index) <- state.(index) lxor state.(index + 8);
    state.(index + 8) <- state.(index + 8) lxor chaining.(index)
  done;
  state

(* The sixteen little-endian words of up to 64 bytes of [input] from
   [offset], padded with zeros. *)
let words input offset length =
  Array.init 16 (fun word ->
      let byte index =
        let position = (word * 4) + index in
        if position < length then Char.code input.[offset + position] else 0
      in
      byte 0 lor (byte 1 lsl 8) lor (byte 2 lsl 16) lor (byte 3 lsl 24))

(* What finishing a chunk or a parent node needs: compressed without [root]
   it is a chaining value, and with it the digest. *)
type output = { chaining : int array; block : int array; counter : int; length : int; flags : int }

let chaining_value output =
  Array.sub
    (compress output.chaining output.block ~counter:output.counter ~length:output.length
       ~flags:output.flags)
    0 8

(* The output of the chunk numbered [counter], which holds [length] bytes of
   [input] from [offset]. Every block but the last is compressed here. *)
let chunk_output input ~offset ~length ~counter =
  let chaining = ref initial in
  let blocks = if length = 0 then 1 else (length + block_length - 1) / block_length in
  for index = 0 to blocks - 2 do
    let start = if index = 0 then chunk_start else 0 in
    chaining :=
      Array.sub
        (compress !chaining
           (words input (offset + (index * block_length)) block_length)
           ~counter ~length:block_length ~flags:start)
        0 8
  done;
  let last_offset = (blocks - 1) * block_length in
  let last_length = length - last_offset in
  {
    chaining = !chaining;
    block = words input (offset + last_offset) last_length;
    counter;
    length = last_length;
    flags = (if blocks = 1 then chunk_start else 0) lor chunk_end;
  }

let parent_output left right =
  {
    chaining = initial;
    block = Array.append left right;
    counter = 0;
    length = block_length;
    flags = parent;
  }

let hash input =
  let total = String.length input in
  let chunks = if total = 0 then 1 else (total + chunk_length - 1) / chunk_length in
  (* The stack of chaining values of complete subtrees, merged as the
     reference implementation merges them: after chunk [n], once for each
     trailing zero bit of [n]. *)
  let stack = ref [] in
  for index = 0 to chunks - 2 do
    let output =
      chunk_output input ~offset:(index * chunk_length) ~length:chunk_length ~counter:index
    in
    let value = ref (chaining_value output) in
    let finished = ref (index + 1) in
    while !finished land 1 = 0 do
      (match !stack with
      | left :: rest ->
          value := chaining_value (parent_output left !value);
          stack := rest
      | [] -> assert false);
      finished := !finished lsr 1
    done;
    stack := !value :: !stack
  done;
  let last_offset = (chunks - 1) * chunk_length in
  let last =
    chunk_output input ~offset:last_offset ~length:(total - last_offset) ~counter:(chunks - 1)
  in
  let output =
    List.fold_left (fun right left -> parent_output left (chaining_value right)) last !stack
  in
  let words =
    compress output.chaining output.block ~counter:output.counter ~length:output.length
      ~flags:(output.flags lor root)
  in
  String.init 32 (fun index -> Char.chr ((words.(index / 4) lsr (8 * (index mod 4))) land 0xff))

let to_hex digest =
  String.concat ""
    (List.init (String.length digest) (fun index ->
         Printf.sprintf "%02x" (Char.code digest.[index])))
