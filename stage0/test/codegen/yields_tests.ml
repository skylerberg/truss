(* Yield lowering: the loop form and cursors. *)

open Memory_layout
open Codegen_support

(* Yield lowering *)

(* [count_to(limit)] yields 1, 2, and so on up to [limit]. *)
let count_to =
  function_ ~parameters:[ 0 ]
    [ local ~name:"limit" (value int32); local ~name:"i" (value int32); local (Raw Bool) ]
    [
      block [ Assign (at 1, Use (constant_int32 1)) ] (Goto 1);
      block
        [ Assign (at 2, Binary (Less_equal, copy 1, copy 0)) ]
        (Switch { value = copy 2; cases = [ (Z.one, 2) ]; default = Some 3 });
      block [] (Yield { value = copy 1; resume = 4; stop = Some 3 });
      block [] (Return None);
      block [ Assign (at 1, Binary (Add, copy 1, constant_int32 1)) ] (Goto 1);
    ]

let body_type : Ground.function_type =
  { parameters = [ (Read, int32) ]; result = Returns bool; uses = [] }

(* A program that loops over [count_to(4)] with a body that adds each item
   to a total, and goes on while [go_on] says so. *)
let loop_program go_on =
  let env = shape_env () in
  let method_ = instance "count_to" (Yields.loop_form env ~body:body_type count_to) in
  let total = Lir.Pointer { target = value int32; writable = true } in
  let body =
    function_ ~parameters:[ 0; 1 ] ~result:(value bool)
      ~environment:[ ("total", total) ]
      [
        local (Raw (Nullable_pointer Opaque));
        local ~name:"item" (value int32);
        local (Pointer { target = Environment 0; writable = false });
        local (value bool);
      ]
      [
        block
          [
            Assign (at 2, Use (copy 0));
            Assign
              ( at ~projections:[ Deref; Field "total"; Deref ] 2,
                Binary (Add, copy ~projections:[ Deref; Field "total"; Deref ] 2, copy 1) );
            Assign (at 3, go_on (copy 1));
          ]
          (Return (Some (copy 3)));
      ]
  in
  let signature = Lir.signature method_.main in
  [
    method_;
    entry ~nested:[ body ]
      [
        local ~name:"total" (value int32); local (Environment 0); local (value (Function body_type));
      ]
      [
        block
          [
            Assign (at 0, Use (constant_int32 0));
            Assign
              (at ~projections:[ Field "total" ] 1, Use (Address { place = at 0; writable = true }));
            Assign
              ( at 2,
                Function_value
                  {
                    code = Nested 0;
                    environment = Some (Address { place = at 1; writable = false });
                  } );
            Call
              {
                target = Direct { function_ = Instance (key "count_to"); signature };
                arguments = [ constant_int32 4; copy 2 ];
                result = Discarded;
              };
          ]
          (Return (Some (copy 0)));
      ];
  ]

let () =
  test "a yielding method calls the loop body at each yield" (fun () ->
      expect_status 10 (loop_program (fun _ -> Use (Constant (Bool true)))));
  test "a loop body that stops ends the method at that yield" (fun () ->
      expect_status 6 (loop_program (fun item -> Binary (Not_equal, item, constant_int32 3))));
  let yielding : Ground.yielding = { method_ = definition "count_to"; type_arguments = [] } in
  let cursor = Ground.Cursor yielding in
  test "a cursor keeps the parameters and the locals live across a yield" (fun () ->
      let fields = List.map fst (Yields.cursor_fields (shape_env ()) ~evidence:[] count_to) in
      expect_string ~expected:"state parameter0 local1" (String.concat " " fields));
  test "a pulled method yields each value and then None" (fun () ->
      let cursor_shape =
        ("cursor of count_to", Record (Yields.cursor_fields (shape_env ()) ~evidence:[] count_to))
      in
      let env = shape_env ~extra:[ cursor_shape ] () in
      let result = option int32 in
      let next =
        {
          (instance "next"
             (Lir.canonical (Yields.cursor_next env ~cursor ~result ~evidence:[] count_to)))
          with
          key = Cursor_next yielding;
        }
      in
      let release : Lir.t =
        {
          key = Drop cursor;
          main = Lir.canonical (Yields.cursor_drop env ~cursor ~owned:[] ~evidence:[] count_to);
          nested = [||];
        }
      in
      let next_call place =
        Lir.Call
          {
            target =
              Direct
                { function_ = Instance (Cursor_next yielding); signature = Lir.signature next.main };
            arguments = [ Address { place = at 0; writable = true } ];
            result = Returned place;
          }
      in
      let pulled = at 1 in
      let add_value =
        Lir.Assign
          ( at 2,
            Binary
              ( Add,
                copy 2,
                copy ~projections:[ Variant_field { variant = "Some"; field = "value" } ] 1 ) )
      in
      expect_status ~extra:[ cursor_shape ] 16
        [
          next;
          release;
          entry
            [
              local ~name:"cursor" (value cursor);
              local (value result);
              local ~name:"sum" (value int32);
              local (Raw Bool);
              local (value int32);
            ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Build
                        {
                          ty = cursor;
                          variant = None;
                          fields =
                            [
                              ("state", Constant (Integer (UInt32, Z.zero)));
                              ("parameter0", constant_int32 3);
                            ];
                        } );
                  Assign (at 2, Use (constant_int32 0));
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  Assign (at 3, Is_variant (at 1, "None"));
                  Assign (at 4, Convert (copy 3, Integer Int32));
                  Assign (at 4, Binary (Multiply, copy 4, constant_int32 10));
                  Assign (at 2, Binary (Add, copy 2, copy 4));
                  Drop (at 0);
                ]
                (Return (Some (copy 2)));
            ];
        ])

let () = Harness.finish ()
