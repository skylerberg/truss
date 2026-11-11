(* Drop elaboration. *)

open Memory_layout
open Codegen_support

(* Drop elaboration *)

let rec needs_drop (ty : Ground.ty) =
  match ty with
  | Named { path = Top { name = "Text" | "Box" | "Counter"; _ }; _ } -> true
  | Named { path = Top { name = "Pair"; _ }; _ } -> true
  | Named { path = Top { name = "Option"; _ }; arguments = [ Type inner ] } -> needs_drop inner
  | _ -> false

let elaborate f =
  Lir.canonical
    (Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop ~environment:(fun _ -> []) f)

let elaborated f = Lir.function_to_string (elaborate f)
let condition = local ~name:"ready" (Raw Bool)
let consume = call "consume" ~result:None ~parameters:[ value text ]

let expect_lir ~expected f =
  let actual = elaborated f in
  if actual <> String.concat "\n" expected then
    fail "expected:\n%s\ngot:\n%s" (String.concat "\n" expected) actual

let () =
  test "a drop of a place moved out on every path is removed" (fun () ->
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: call test::consume(move _0); return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value text) ]
           [ block [ consume [ Move (at 0) ] None; Drop (at 0) ] (Return None) ]));
  test "a drop of a place nothing moved out of is kept" (fun () ->
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: drop _0; return" ]
        (function_ ~parameters:[ 0 ] [ local (value text) ] [ block [ Drop (at 0) ] (Return None) ]));
  test "a drop of plain data is removed" (fun () ->
      expect_lir ~expected:[ "fn(_0: Int32)"; "b0: return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value int32) ]
           [ block [ Drop (at 0) ] (Return None) ]));
  test "a place moved out on one path is dropped behind a flag" (fun () ->
      expect_lir
        ~expected:
          [
            "fn(_0: Text, _1: raw Bool)";
            "b0: _2 = true; switch _1 [1 => b1, _ => b2]";
            "b1: call test::consume(move _0); _2 = false; goto b2";
            "b2: switch _2 [1 => b3, _ => b4]";
            "b3: drop _0; goto b4";
            "b4: _2 = false; return";
          ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value text); condition ]
           [
             block [] (Switch { value = copy 1; cases = [ (Z.one, 1) ]; default = Some 2 });
             block [ consume [ Move (at 0) ] None ] (Goto 2);
             block [ Drop (at 0) ] (Return None);
           ]));
  test "after a field is moved out, the rest of the record is dropped field by field" (fun () ->
      expect_lir
        ~expected:
          [ "fn(_0: Pair)"; "b0: call test::consume(move _0.first); drop _0.second; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value pair) ]
           [
             block
               [ consume [ Move (at ~projections:[ Field "first" ] 0) ] None; Drop (at 0) ]
               (Return None);
           ]));
  test "a record whose moved field is given a value again is dropped whole" (fun () ->
      expect_lir
        ~expected:
          [
            "fn(_0: Pair, _1: Text)";
            "b0: call test::consume(move _0.first); _0.first = move _1; drop _0; return";
          ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value pair); local (value text) ]
           [
             block
               [
                 consume [ Move (at ~projections:[ Field "first" ] 0) ] None;
                 Assign (at ~projections:[ Field "first" ] 0, Use (Move (at 1)));
                 Drop (at 0);
               ]
               (Return None);
           ]));
  test "a drop before a write is kept where the place holds a value" (fun () ->
      expect_lir
        ~expected:[ "fn(_0: Text, _1: Text)"; "b0: drop _0; _0 = move _1; drop _0; return" ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value text); local (value text) ]
           [ block [ Drop (at 0); Assign (at 0, Use (Move (at 1))); Drop (at 0) ] (Return None) ]));
  test "a write over a value that was not dropped is a compiler bug" (fun () ->
      match
        elaborated
          (function_ ~parameters:[ 0; 1 ]
             [ local (value text); local (value text) ]
             [ block [ Assign (at 0, Use (Move (at 1))); Drop (at 0) ] (Return None) ])
      with
      | _ -> fail "expected a compiler bug"
      | exception Compiler_bug.Bug bug ->
          if bug.message <> "a write over local 0, which may still own a value" then
            fail "got %s" bug.message);
  test "a local that still owns a value where the function returns is a compiler bug" (fun () ->
      match
        elaborated
          (function_ ~parameters:[ 0 ]
             [ local (value text); local (value text) ]
             [ block [ Assign (at 1, Use (Move (at 0))) ] (Return None) ])
      with
      | _ -> fail "expected a compiler bug"
      | exception Compiler_bug.Bug bug ->
          if bug.message <> "local 1 may still own a value where the function returns" then
            fail "got %s" bug.message);
  test "a borrowed local is neither dropped nor counted as owning" (fun () ->
      expect_lir ~expected:[ "fn(_0: Text)"; "b0: return" ]
        (function_ ~parameters:[ 0 ]
           [ local ~borrowed:true (value text) ]
           [ block [ Drop (at 0) ] (Return None) ]));
  test "an assignment that moves out of its own place first drops nothing" (fun () ->
      let rebuild = call "rebuild" ~result:(Some (value text)) ~parameters:[ value text ] in
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: _0 = call test::rebuild(move _0); drop _0; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value text) ]
           [ block [ rebuild [ Move (at 0) ] (Some (at 0)); Drop (at 0) ] (Return None) ]));
  test "an indirect variant whose fields were moved out frees its block" (fun () ->
      let full field = at ~projections:[ Variant_field { variant = "Full"; field } ] 0 in
      expect_lir
        ~expected:
          [ "fn(_0: Box)"; "b0: call test::consume(move _0.Full.contents); free _0.Full; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value (named "Box")) ]
           [ block [ consume [ Move (full "contents") ] None; Drop (at 0) ] (Return None) ]));
  test "a sum whose part was moved out on one path is asked its variant where the paths meet"
    (fun () ->
      let full field = at ~projections:[ Variant_field { variant = "Full"; field } ] 0 in
      expect_lir
        ~expected:
          [
            "fn(_0: Box, _1: raw Bool)";
            "b0: _2 = true; switch _1 [1 => b1, _ => b2]";
            "b1: call test::consume(move _0.Full.contents); _2 = false; goto b2";
            "b2: switch _0 [Full => b4, _ => b3]";
            "b3: drop _0; goto b7";
            "b4: switch _2 [1 => b5, _ => b6]";
            "b5: drop _0.Full.contents; goto b6";
            "b6: free _0.Full; goto b7";
            "b7: _2 = false; return";
          ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value (named "Box")); condition ]
           [
             block [] (Switch { value = copy 1; cases = [ (Z.one, 1) ]; default = Some 2 });
             block [ consume [ Move (full "contents") ] None ] (Goto 2);
             block [ Drop (at 0) ] (Return None);
           ]));
  test "a value moved out on one path is dropped exactly once when the program runs" (fun () ->
      let counter = named "Counter" in
      let pointer = Lir.Pointer { target = value counter; writable = true } in
      let drop_counter : Lir.t =
        {
          key = Drop counter;
          main =
            function_ ~parameters:[ 0 ]
              [ local pointer; local (Raw (Pointer (Data int32))) ]
              [
                block
                  [
                    Assign (at 1, Use (copy ~projections:[ Deref; Field "target" ] 0));
                    Assign
                      ( at ~projections:[ Deref ] 1,
                        Binary (Add, copy ~projections:[ Deref ] 1, constant_int32 1) );
                  ]
                  (Return None);
              ];
          nested = [||];
        }
      in
      let keep =
        instance "keep"
          (function_ ~parameters:[ 0 ]
             [ local (value counter) ]
             [ block [ Drop (at 0) ] (Return None) ])
      in
      let main =
        function_ ~result:(value int32)
          [
            local ~name:"count" (value int32);
            local ~name:"counter" (value counter);
            local (Raw Bool);
          ]
          [
            block
              [
                Assign (at 0, Use (constant_int32 0));
                Assign
                  ( at 1,
                    Build
                      {
                        ty = counter;
                        variant = None;
                        fields = [ ("target", Address { place = at 0; writable = true }) ];
                      } );
                Assign (at 2, Use (Constant (Bool true)));
              ]
              (Switch { value = copy 2; cases = [ (Z.one, 1) ]; default = Some 2 });
            block
              [ call "keep" ~result:None ~parameters:[ value counter ] [ Move (at 1) ] None ]
              (Goto 2);
            block [ Drop (at 1) ] (Return (Some (copy 0)));
          ]
      in
      let program =
        [
          drop_counter;
          {
            keep with
            main =
              Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop
                ~environment:(fun _ -> [])
                keep.main;
          };
          ( entry [] [] |> fun e ->
            {
              e with
              main =
                Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop
                  ~environment:(fun _ -> [])
                  main;
            } );
        ]
      in
      expect_status ~extra:drop_shapes 1 program)

(* Drop flags and regions *)

let make = call "make" ~result:(Some (value text)) ~parameters:[]

(* A function that makes a text, consumes it on one path, and drops what
   is left, with [before] and [after] around the three steps. *)
let made_and_maybe_consumed ~locals ~before ~after =
  function_ ~parameters:[ 0 ]
    ([ condition; local (value text) ] @ locals)
    [
      block
        (before @ [ make [] (Some (at 1)) ])
        (Switch { value = copy 0; cases = [ (Z.one, 1) ]; default = Some 2 });
      block [ consume [ Move (at 1) ] None ] (Goto 2);
      block (Drop (at 1) :: after) (Return None);
    ]

let () =
  test "the flag of a local that holds nothing at entry is first written where it is given a value"
    (fun () ->
      expect_lir
        ~expected:
          [
            "fn(_0: raw Bool)";
            "b0: _1 = call test::make(); _2 = true; switch _0 [1 => b1, _ => b2]";
            "b1: call test::consume(move _1); _2 = false; goto b2";
            "b2: switch _2 [1 => b3, _ => b4]";
            "b3: drop _1; goto b4";
            "b4: _2 = false; return";
          ]
        (made_and_maybe_consumed ~locals:[] ~before:[] ~after:[]));
  test "the flag of a chunk's own local is a local of each run of the chunk" (fun () ->
      let index = local (Raw (Integer UInt64)) in
      let elaborated =
        elaborate
          (made_and_maybe_consumed ~locals:[ index; index ]
             ~before:[ Region { fork = 0; region = Chunk { first = 2; last = 3 } } ]
             ~after:[ Regions_end { fork = 0 } ])
      in
      let outlined =
        Lir.to_string
          (Lir.canonical_instance
             (Outline.instance (shape_env ~extra:drop_shapes ()) (instance "entry" elaborated)))
      in
      (* The nested function's [_5] is the flag. The environment holds only
         the condition, which the function around the chunk owns. *)
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "test::entry fn(_0: raw Bool)";
               "b0: _1.capture0 = &mut _0; fork nested 0(&_1) over _3 to _2; goto b1";
               "b1: return";
               "nested 0 fn(_0: raw nullable, _1: raw UInt64, _2: raw UInt64)";
               "b0: _3 = _0; goto b1";
               "b1: _4 = call test::make(); _5 = true; switch **_3.capture0 [1 => b2, _ => b3]";
               "b2: call test::consume(move _4); _5 = false; goto b3";
               "b3: switch _5 [1 => b4, _ => b5]";
               "b4: drop _4; goto b5";
               "b5: _5 = false; goto b6";
               "b6: return";
             ])
        outlined)

let () = Harness.finish ()
