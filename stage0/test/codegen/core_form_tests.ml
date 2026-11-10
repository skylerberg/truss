(* Lowering from the core form: which bodies are lowered from it, and that
   what is lowered from it runs. *)

open Codegen_support

let int64 = Monomorphic.builtin Int64

(* A module whose test passes, and whose named functions, each with its type
   arguments, are lowered from their core forms. *)
let lowers what ?(tests = false) functions source =
  test what (fun () ->
      let database, _ = load source in
      let context = Lower.context ~checks:true database target_64 in
      let from_core key =
        match Lower.not_from_core context key with
        | None -> ()
        | Some stopped ->
            fail "%s was lowered from the syntax tree, for %s" (Instance.to_string key) stopped
      in
      List.iter
        (fun (name, type_arguments) ->
          from_core (Code { path = Top { module_ = example; name }; type_arguments }))
        functions;
      if tests then List.iter (fun path -> from_core (Lower.test_key path)) (tests_of database);
      expect_output source "test 0 passed\n")

let () =
  lowers "calls, operators, comparisons, a let, an if, and a return" ~tests:true
    [ ("double", []); ("larger", []); ("pick", []) ]
    {|fn double(value: Int64) -> Int64 {
  value + value
}

fn larger(first: Int64, second: Int64) -> Int64 {
  if first > second { first } else { second }
}

fn pick(first: Int64, second: Int64) -> Int64 {
  let most = larger(first, second: second)
  if most > 10 && first != second {
    return most * 2
  }
  most + double(second)
}

test "picks" {
  assert pick(3, second: 4) == 12
  assert pick(20, second: 4) == 40
  assert !(pick(1, second: 1) > 3) || pick(1, second: 1) == 3
}
|};
  lowers "a value that is taken is moved, and a place that a let only views stays where it is"
    [ ("keep", []); ("count", []) ]
    {|fn keep(items: own List[Int64]) -> List[Int64] {
  let held = own items
  held
}

fn count(items: List[Int64]) -> USize {
  let seen = items
  seen.length()
}

test "moves" {
  let kept = keep([1, 2, 3])
  assert count(kept) == 3
}
|};
  lowers
    "a trait's method is called by the impl the type has, and by a bound where it is a parameter"
    [ ("same", [ Ground.Type int64 ]); ("equal_lengths", []) ]
    {|type Meters(value: Int64)
  derives Equal

fn same[Value: Equal](first: Value, second: Value) -> Bool {
  first.equal(second)
}

fn equal_lengths(first: Meters, second: Meters) -> Bool {
  first.equal(second)
}

test "equal" {
  assert same(4, second: 4)
  assert equal_lengths(Meters(value: 2), second: Meters(value: 2))
}
|};
  lowers "an assignment, a parameter left to its default, and a field of a record"
    [ ("twice", []); ("width", []) ]
    {|type Box(width: Int64, height: Int64)

fn step(start: Int64, by: Int64 = 1) -> Int64 {
  start + by
}

fn twice(start: Int64) -> Int64 {
  var total = step(start)
  total = step(total, by: 5)
  total
}

fn width(box: Box) -> Int64 {
  box.width
}

test "steps" {
  assert twice(1) == 7
  assert width(Box(width: 3, height: 4)) == 3
}
|}

let () =
  lowers "a string, a constant, and a record built with every field given" ~tests:true
    [ ("labelled", []) ]
    {|type Box(width: Int64, label: String)

let wide: Int64 = 40

fn labelled(width: Int64) -> Box {
  Box(width: width + wide, label: "box")
}

test "builds" {
  let box = labelled(2)
  assert box.width == 42
  assert box.label == "box"
}
|}

let () = Harness.finish ()
