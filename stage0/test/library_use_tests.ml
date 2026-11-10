(* The standard library's contracts, read from another package. Each test
   is a small program a user might write, proven against the library as it
   stands, so a contract that only the library's own package can read
   fails here. *)

open Harness

let solver =
  match Solver.find () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let check database module_ =
  match Type_checker.diagnostics database module_ with
  | [] -> Prover.diagnostics database solver module_
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a map that was inserted into holds the key" (fun () ->
      proven
        "fn built(name: String) -> Map[String, Int64]\n\
        \  ensures result.contains(name)\n\
        \  ensures result.length() == 1\n\
         {\n\
        \  var made: Map[String, Int64] = [:]\n\
        \  mut made.insert(name.copy(), value: 1)\n\
        \  made\n\
         }\n\n\
         fn numbered() -> Map[Int64, Int64]\n\
        \  ensures result.contains(7)\n\
         {\n\
        \  var made: Map[Int64, Int64] = [:]\n\
        \  mut made.insert(7, value: 1)\n\
        \  made\n\
         }\n");
  test "a map literal has its keys and its length" (fun () ->
      proven
        "fn literal() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  let table: Map[Int64, Int64] = [1: 2, 3: 4]\n\
        \  table.contains(3) && table.length() == 2\n\
         }\n");
  test "a key that a map contains can be indexed" (fun () ->
      proven
        "fn looked_up(ports: Map[String, Int64], name: String) -> Int64 {\n\
        \  if ports.contains(name) { ports[name] } else { 0 }\n\
         }\n");
  test "replace leaves the key in the map" (fun () ->
      proven
        "fn replaced(ports: mut Map[Int64, Int64]) -> Option[Int64]\n\
        \  ensures ports.contains(80)\n\
         {\n\
        \  mut ports.replace(80, value: 8080)\n\
         }\n");
  test "take and clear leave a map without the key" (fun () ->
      proven
        "fn taken(ports: mut Map[String, Int64], name: String) -> Option[Int64]\n\
        \  ensures !ports.contains(name)\n\
         {\n\
        \  mut ports.take(name)\n\
         }\n\n\
         fn emptied(ports: mut Map[String, Int64])\n\
        \  ensures ports.is_empty()\n\
         {\n\
        \  mut ports.clear()\n\
         }\n");
  test "maps and sets are compared" (fun () ->
      proven
        "fn same(first: Map[Int64, Int64], second: Map[Int64, Int64]) -> Bool {\n\
        \  first == second\n\
         }\n\n\
         fn same_sets(first: Set[Int64], second: Set[Int64]) -> Bool {\n\
        \  first == second && first.is_subset_of(second)\n\
         }\n");
  test "a set holds what was inserted and not what was removed" (fun () ->
      proven
        "fn added(seen: mut Set[Int64]) -> Bool\n\
        \  ensures seen.contains(4)\n\
         {\n\
        \  mut seen.insert_new(4)\n\
         }\n\n\
         fn removed(seen: mut Set[Int64])\n\
        \  ensures !seen.contains(4)\n\
         {\n\
        \  mut seen.remove(4)\n\
         }\n");
  test "a set literal contains what it lists and nothing else" (fun () ->
      proven
        "fn both() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  let colors: Set[Int64] = [1, 2]\n\
        \  colors.contains(2) && !colors.contains(5) && colors.length() == 2\n\
         }\n")

let () =
  test "two strings with the same text are equal" (fun () ->
      proven
        "fn same() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  let first = \"a\"\n\
        \  let second = \"a\"\n\
        \  first == second\n\
         }\n")

let () = finish ()
