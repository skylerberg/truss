(* How code generation fails: the verifier's checks of the LIR, the
   programs stage0 cannot build yet, and a compiler bug's report. *)

open Memory_layout
open Codegen_support

let expect_bug ~saying work =
  match work () with
  | () -> fail "expected a compiler bug saying %S" saying
  | exception Compiler_bug.Bug bug ->
      let text = Compiler_bug.to_string bug in
      if not (contains text saying) then fail "expected %S in %S" saying text

let env = shape_env ()

(* A callee that takes one [Int32] and returns it, and a caller's call of
   it with these arguments under this signature. *)
let callee =
  instance "callee"
    (function_ ~parameters:[ 0 ] ~result:(value int32)
       [ local (value int32) ]
       [ block [] (Return (Some (copy 0))) ])

let caller ?(parameters = [ value int32 ]) arguments =
  entry
    [ local (value int32) ]
    [ block [ call "callee" ~parameters arguments (Some (at 0)) ] (Return (Some (copy 0))) ]

let () =
  test "a call that passes fewer arguments than its target takes is a bug" (fun () ->
      expect_bug ~saying:"passes 0 arguments to a target that takes 1" (fun () ->
          Verify.instance env (caller [])));
  test "a return of nothing from a function with a result is a bug" (fun () ->
      expect_bug ~saying:"a return of nothing from a function with a result" (fun () ->
          Verify.instance env (entry [] [ block [] (Return None) ])));
  test "a jump to a block that does not exist is a bug" (fun () ->
      expect_bug ~saying:"block 3, of 1" (fun () ->
          Verify.instance env (entry [] [ block [] (Goto 3) ])));
  test "a place that names a local that does not exist is a bug" (fun () ->
      expect_bug ~saying:"local 5, of 0" (fun () ->
          Verify.instance env (entry [] [ block [] (Return (Some (copy 5))) ])));
  test "a value built with a field its type does not have is a bug" (fun () ->
      expect_bug ~saying:"built with a field third, which it does not have" (fun () ->
          Verify.instance (shape_env ~extra:drop_shapes ())
            (entry
               [ local (value pair) ]
               [
                 block
                   [
                     Assign
                       ( at 0,
                         Build
                           { ty = pair; variant = None; fields = [ ("third", constant_int32 1) ] }
                       );
                   ]
                   (Return (Some (constant_int32 0)));
               ])));
  test "a call that writes its result to a place it is also given is a bug" (fun () ->
      let quad = named "Quad" in
      let pointer writable = Lir.Pointer { target = value quad; writable } in
      let swapped : Lir.statement =
        Call
          {
            target =
              Direct
                {
                  function_ = Instance (key "swapped");
                  signature =
                    { parameters = [ pointer true; pointer false ]; result = None; returns = true };
                };
            arguments = [ Address { place = at 0; writable = false } ];
            result = Written (at 0);
          }
      in
      let four = Record (List.map (fun name -> field name int64) [ "a"; "b"; "c"; "d" ]) in
      expect_bug ~saying:"writes its result to local 0, which it is also given" (fun () ->
          Verify.instance
            (shape_env ~extra:[ ("Quad", four) ] ())
            (entry [ local (value quad) ] [ block [ swapped ] (Return (Some (constant_int32 0))) ])));
  test "a move out of a constant's static data is a bug" (fun () ->
      let constant : Lir.place =
        { root = Static { key = Constant (definition "words"); ty = text }; projections = [] }
      in
      expect_bug ~saying:"a move out of test::words, which is static data" (fun () ->
          Verify.instance (shape_env ~extra:drop_shapes ())
            (entry
               [ local (value text) ]
               [ block [ Assign (at 0, Use (Move constant)) ] (Return (Some (constant_int32 0))) ])));
  test "an instance whose calls fit their targets passes" (fun () ->
      Verify.instance env (caller [ constant_int32 1 ]));
  let find units key =
    List.find_opt
      (fun unit -> Instance.equal (Reachable.compiled_key unit) key)
      (List.map (fun instance -> Lir.Code instance) units)
  in
  test "a callee named with a signature it does not have is a bug" (fun () ->
      let caller =
        caller ~parameters:[ value int32; value int32 ] [ constant_int32 1; constant_int32 2 ]
      in
      Verify.instance env caller;
      expect_bug ~saying:"callee is named with a signature it does not have" (fun () ->
          Verify.links env ~find:(find [ caller; callee ]) (Code caller)));
  test "a callee that is not built is a bug" (fun () ->
      let caller = caller [ constant_int32 1 ] in
      expect_bug ~saying:"callee is called, and is not built" (fun () ->
          Verify.links env ~find:(find [ caller ]) (Code caller)));
  test "a caller and a callee that agree pass" (fun () ->
      let caller = caller [ constant_int32 1 ] in
      Verify.links env ~find:(find [ caller; callee ]) (Code caller))

(* A module's tests cannot be built, with a message that says this. *)
let refused name ~saying source =
  test name (fun () ->
      let database, compile = load source in
      match Compile.run_tests compile ~time_limit:2000 (tests_of database) with
      | Ok _ -> fail "expected the build to be refused"
      | Error message -> if not (contains message saying) then fail "got %S" message)

let () =
  refused "a lambda in a yielding method that is pulled is refused"
    ~saying:"a lambda in a yielding method that is pulled"
    Fixtures.Failure.lambda_in_a_yielding_method_that_is_pulled_is;
  test "a compiler bug says which instance was being lowered" (fun () ->
      let _, compile = load "type Point(x: Int64)\n" in
      let not_code =
        Instance.Code { path = Top { module_ = example; name = "Point" }; type_arguments = [] }
      in
      expect_bug ~saying:"while lowering example::main::Point" (fun () ->
          ignore (Compile.For_testing.compiled compile not_code)))
