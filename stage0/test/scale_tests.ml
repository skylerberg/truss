(* The cost of a change follows the change, and not the project. Each test
   makes the same edit in a small package and in a large one, and compares
   the work the code database counted: how many results it marked, found
   current, and computed. Counts are compared, never times, so the tests
   are the same on every machine. *)

open Harness
open Support

let functions = 5

(* A module whose functions each call [core::leaf], which so is read by
   every module of the package. *)
let module_text index =
  let buffer = Buffer.create 512 in
  Buffer.add_string buffer "use app::core\n\n";
  for number = 0 to functions - 1 do
    let body =
      if number = 0 then "core::leaf(value)"
      else Printf.sprintf "core::leaf(value) + part_%d_%d(value)" index (number - 1)
    in
    Buffer.add_string buffer
      (Printf.sprintf "fn part_%d_%d(value: Int64) -> Int64 {\n  %s\n}\n\n" index number body)
  done;
  Buffer.contents buffer

let core ?(signature = "value: Int64") ?(after = "") body =
  Printf.sprintf "internal fn leaf(%s) -> Int64 {\n  %s\n}\n%s" signature body after

(* A package of [modules] modules and [core], checked. *)
let package modules =
  let names = List.init modules (fun index -> Printf.sprintf "app::part_%d" index) in
  let database =
    setup
      (("app::core", core "value") :: List.mapi (fun index name -> (name, module_text index)) names)
  in
  List.iter
    (fun name ->
      match Query.demand database Checks.file_diagnostics (file_of name) with
      | [] -> ()
      | actual -> fail "%s has %d diagnostics" name (List.length actual))
    ("app::core" :: names);
  database

type work = { marked : int; confirmed : int; computed : int }

let show work =
  Printf.sprintf "marked %d, found current %d, computed %d" work.marked work.confirmed work.computed

(* The work that giving a module another text costs. *)
let edit database name text =
  let engine = Engine.of_context database in
  let before = Engine.counters engine in
  Database.For_testing.set_text engine (file_of name) text;
  ignore (Engine.stabilize engine);
  let after = Engine.counters engine in
  {
    marked = after.marked - before.marked;
    confirmed = after.confirmed - before.confirmed;
    computed = after.computed - before.computed;
  }

(* The same edit of [core] costs the same with four modules and with forty. *)
let same_cost name text =
  test name (fun () ->
      let few = edit (package 4) "app::core" text and many = edit (package 40) "app::core" text in
      if few <> many then fail "four modules: %s; forty: %s" (show few) (show many))

let () =
  same_cost "editing the body of a function every module calls costs the same in a larger package"
    (core "value + 0");
  same_cost "adding a local to a function every module calls costs the same"
    (core "let same = value\n  same");
  same_cost "reformatting the signature of a function every module calls costs the same"
    (core ~signature:"value:  Int64" "value");
  same_cost "adding a function beside one every module calls costs the same"
    (core ~after:Fixtures.Scale.adding_a_function_beside_one_every_module_calls "value");
  test "editing a body in one module costs the same in a larger package" (fun () ->
      let text = module_text 0 ^ Fixtures.Scale.editing_a_body_in_one_module_costs_the_same_in_a in
      let few = edit (package 4) "app::part_0" text
      and many = edit (package 40) "app::part_0" text in
      if few <> many then fail "four modules: %s; forty: %s" (show few) (show many));
  test "changing the type of a function every module calls checks each caller again" (fun () ->
      let text = core ~signature:"value: Int64, extra: Int64 = 0" "value + extra" in
      let few = edit (package 4) "app::core" text and many = edit (package 40) "app::core" text in
      if many.computed <= few.computed then
        fail "four modules: %s; forty: %s" (show few) (show many));
  test "a definition that only moved is not checked again" (fun () ->
      let database = package 4 in
      let engine = Engine.of_context database in
      let checked () = Engine.For_testing.computed engine Infer.type_check_result in
      if checked () = [] then fail "checking the package checked no definition";
      Engine.For_testing.clear_log engine;
      ignore (edit database "app::part_0" ("\n\n" ^ module_text 0));
      match checked () with
      | [] -> ()
      | rechecked ->
          fail "checked [%s]" (String.concat "; " (List.map Resolve.Names.show_key rechecked)))
