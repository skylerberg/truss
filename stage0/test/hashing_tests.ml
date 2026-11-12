(* The tests of deterministic CBOR and BLAKE3, the encoding and hash that
   keys are defined over. *)

open Harness

let hex bytes = Blake3.to_hex bytes

let encodes name value expected =
  test name (fun () ->
      let actual = hex (Cbor.encode value) in
      if actual <> expected then fail "expected %s, got %s" expected actual)

(* RFC 8949, appendix A, for the values whose preferred encoding is the
   deterministic one. *)
let () =
  encodes "zero is one byte" (Cbor.int 0) "00";
  encodes "23 is the largest one-byte integer" (Cbor.int 23) "17";
  encodes "24 takes a one-byte argument" (Cbor.int 24) "1818";
  encodes "1000 takes a two-byte argument" (Cbor.int 1000) "1903e8";
  encodes "1000000 takes a four-byte argument" (Cbor.int 1000000) "1a000f4240";
  encodes "a trillion takes an eight-byte argument"
    (Cbor.Integer (Z.of_string "1000000000000"))
    "1b000000e8d4a51000";
  encodes "the largest 64-bit integer is not a bignum"
    (Cbor.Integer (Z.of_string "18446744073709551615"))
    "1bffffffffffffffff";
  encodes "2^64 is a positive bignum"
    (Cbor.Integer (Z.of_string "18446744073709551616"))
    "c249010000000000000000";
  encodes "-1 is major type 1" (Cbor.int (-1)) "20";
  encodes "-1000" (Cbor.int (-1000)) "3903e7";
  encodes "-2^64 is not a bignum"
    (Cbor.Integer (Z.of_string "-18446744073709551616"))
    "3bffffffffffffffff";
  encodes "-2^64 - 1 is a negative bignum"
    (Cbor.Integer (Z.of_string "-18446744073709551617"))
    "c349010000000000000000";
  encodes "0.0 is a half float" (Cbor.Float 0.0) "f90000";
  encodes "-0.0 keeps its sign" (Cbor.Float (-0.0)) "f98000";
  encodes "1.5 is a half float" (Cbor.Float 1.5) "f93e00";
  encodes "65504.0 is the largest half float" (Cbor.Float 65504.0) "f97bff";
  encodes "the smallest half subnormal" (Cbor.Float 5.960464477539063e-8) "f90001";
  encodes "the smallest normal half float" (Cbor.Float (Float.ldexp 1.0 (-14))) "f90400";
  encodes "the largest half subnormal" (Cbor.Float (Float.ldexp 1023.0 (-24))) "f903ff";
  encodes "2^-25 is below every half float, so a single"
    (Cbor.Float (Float.ldexp 1.0 (-25)))
    "fa33000000";
  encodes "65520.0 rounds to infinity as a half, so a single" (Cbor.Float 65520.0) "fa477ff000";
  encodes "the smallest single subnormal" (Cbor.Float (Float.ldexp 1.0 (-149))) "fa00000001";
  encodes "2^-150 is below every single float, so a double"
    (Cbor.Float (Float.ldexp 1.0 (-150)))
    "fb3690000000000000";
  encodes "100000.0 is a single float" (Cbor.Float 100000.0) "fa47c35000";
  encodes "1.1 needs a double" (Cbor.Float 1.1) "fb3ff199999999999a";
  encodes "infinity is a half float" (Cbor.Float Float.infinity) "f97c00";
  encodes "every NaN is one encoding" (Cbor.Float (Float.of_string "-nan")) "f97e00";
  encodes "false" (Cbor.Bool false) "f4";
  encodes "null" Cbor.Null "f6";
  encodes "text is major type 3" (Cbor.Text "IETF") "6449455446";
  encodes "bytes are major type 2" (Cbor.Bytes "\x01\x02\x03\x04") "4401020304";
  encodes "arrays nest"
    (Cbor.Array [ Cbor.int 1; Cbor.Array [ Cbor.int 2; Cbor.int 3 ] ])
    "8201820203";
  encodes "a tag" (Cbor.Tag (1, Cbor.int 1363896240)) "c11a514b67b0";
  encodes "map keys are sorted by their encoding, whatever order they are given in"
    (Cbor.Map
       [ (Cbor.Text "b", Cbor.int 2); (Cbor.int 10, Cbor.int 1); (Cbor.Text "a", Cbor.int 3) ])
    "a30a01616103616202";
  test "a negative tag has no encoding" (fun () ->
      match Cbor.encode (Cbor.Tag (-1, Cbor.Null)) with
      | _ -> fail "encoded"
      | exception Invalid_argument _ -> ());
  test "a map that repeats a key has no encoding" (fun () ->
      match Cbor.encode (Cbor.Map [ (Cbor.int 1, Cbor.Null); (Cbor.int 1, Cbor.Null) ]) with
      | _ -> fail "encoded"
      | exception Invalid_argument _ -> ())

(* The official BLAKE3 test vectors, test_vectors.json in the BLAKE3
   repository: the input is [length] bytes of 0, 1, ..., 250, 0, 1, ...,
   and these are the first 32 bytes of each output, in the default mode and
   in the derive-key mode under the vectors' context. The lengths cover one
   block, several blocks, one chunk, and trees of several depths. *)
let vector_context = "BLAKE3 2019-12-27 16:29:52 test vectors context"

let vectors =
  [
    ( 0,
      "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
      "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d" );
    ( 1,
      "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213",
      "b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c" );
    ( 63,
      "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b",
      "b6451e30b953c206e34644c6803724e9d2725e0893039cfc49584f991f451af3" );
    ( 64,
      "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98",
      "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e" );
    ( 65,
      "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee",
      "51fd05c3c1cfbc8ed67d139ad76f5cf8236cd2acd26627a30c104dfd9d3ff8a8" );
    ( 1023,
      "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11",
      "74a16c1c3d44368a86e1ca6df64be6a2f64cce8f09220787450722d85725dea5" );
    ( 1024,
      "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7",
      "7356cd7720d5b66b6d0697eb3177d9f8d73a4a5c5e968896eb6a689684302706" );
    ( 1025,
      "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444",
      "effaa245f065fbf82ac186839a249707c3bddf6d3fdda22d1b95a3c970379bcb" );
    ( 2048,
      "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a",
      "7b2945cb4fef70885cc5d78a87bf6f6207dd901ff239201351ffac04e1088a23" );
    ( 2049,
      "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030",
      "2ea477c5515cc3dd606512ee72bb3e0e758cfae7232826f35fb98ca1bcbdf273" );
    ( 3072,
      "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2",
      "050df97f8c2ead654d9bb3ab8c9178edcd902a32f8495949feadcc1e0480c46b" );
    ( 4096,
      "015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969",
      "1e0d7f3db8c414c97c6307cbda6cd27ac3b030949da8e23be1a1a924ad2f25b9" );
    ( 4097,
      "9b4052b38f1c5fc8b1f9ff7ac7b27cd242487b3d890d15c96a1c25b8aa0fb995",
      "aca51029626b55fda7117b42a7c211f8c6e9ba4fe5b7a8ca922f34299500ead8" );
    ( 8193,
      "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b",
      "af1e0346e389b17c23200270a64aa4e1ead98c61695d917de7d5b00491c9b0f1" );
    ( 31744,
      "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47",
      "39772aef80e0ebe60596361e45b061e8f417429d529171b6764468c22928e28e" );
    ( 102400,
      "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085",
      "4652cff7a3f385a6103b5c260fc1593e13c778dbe608efb092fe7ee69df6e9c6" );
  ]

let () =
  List.iter
    (fun (length, expected_hash, expected_derived) ->
      let input = String.init length (fun index -> Char.chr (index mod 251)) in
      test (Printf.sprintf "BLAKE3 of the %d-byte test vector" length) (fun () ->
          let actual = hex (Blake3.hash input) in
          if actual <> expected_hash then fail "expected %s, got %s" expected_hash actual);
      test (Printf.sprintf "BLAKE3 derive-key of the %d-byte test vector" length) (fun () ->
          let actual = hex (Blake3.derive_key ~context:vector_context input) in
          if actual <> expected_derived then fail "expected %s, got %s" expected_derived actual))
    vectors
