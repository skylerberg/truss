(* The tests of the core form: what checking builds for each construct,
   shown as text. *)

open Harness
open Support

(* The core form of the definition named [name] in a file of its own. *)
let form text name =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.span 0 0) message)
       (parse_errors database module_)
     @ Resolve.diagnostics database module_
     @ Interface.diagnostics database module_
     @ Infer.diagnostics database module_
   with
  | [] -> ()
  | found -> failwith (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
  let found =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if Path.show key.path = "app::main::" ^ name then Query.demand database Infer.core key
        else None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match found with
  | Some form -> Core_print.show form
  | None -> failwith (Printf.sprintf "`%s` has no core form" name)

(* The body of a function's form: its last line. *)
let body text name =
  match List.rev (String.split_on_char '\n' (form text name)) with last :: _ -> last | [] -> ""

let shows what text expected =
  test what (fun () ->
      let found = form text "g" in
      if found <> expected then fail "found:\n%s" found)

let builds what text expected =
  test what (fun () ->
      let found = body text "g" in
      if found <> expected then fail "found:\n%s" found)

let meters =
  "type Meters(value: Int64)\n\n\
   impl Ordered for Meters {\n\
  \  fn compare(self, other: Meters) -> Ordering { todo }\n\
   }\n\n\
   impl Equal for Meters {\n\
  \  fn equal(self, other: Meters) -> Bool { todo }\n\
   }\n\n"

let shape =
  "type Shape =\n  | Circle(radius: Int64)\n  | Square(side: Int64, label: String = \"s\")\n\n"

(* Operators *)

let () =
  builds "arithmetic on built-in numbers is the operation, however it is written"
    "fn g(left: Int64, right: Int64) -> Int64 {\n  left + right.multiply(2)\n}\n"
    "{ add(left, multiply(right, 2)) }";
  builds "a comparison of built-in values is a comparison"
    "fn g(left: Int64, right: Int64) -> Bool {\n  left <= right && left != 0\n}\n"
    "{ ((left <= right) && (left != 0)) }";
  builds "an ordering of other values tests what compare gives, and != is not equal"
    (meters
   ^ "fn g(first: Meters, second: Meters) -> Bool {\n  first <= second || first != second\n}\n")
    "{ (!(Ordered.compare for Meters by app::main::impl Ordered for Meters(place first, place \
     second) is Greater) || !Equal.equal for Meters by app::main::impl Equal for Meters(place \
     first, place second)) }";
  builds "a compound assignment updates its target once"
    "fn g(items: mut List[Int64]) {\n  items[0] += 2\n}\n"
    "{ update lent Index.at for List[Int64] by standard::list::impl Index for List[Element](mut \
     place items, 0) lends mut = add(updating, 2) }";
  builds "a specification's arithmetic is on integers"
    "fn g(count: Int64) -> Int64\n  ensures result + 1 > count\n{\n  count\n}\n" "{ count }";
  shows "a specification's operands become integers"
    "fn g(count: Int64) -> Int64\n  ensures result + 1 > count\n{\n  count\n}\n"
    "fn(count: Int64)\n\
     ensures (add(to_integer(result), to_integer(1)) > to_integer(count))\n\
     { count }"

(* Calls *)

let () =
  builds "a call lists an argument for each parameter, in order"
    "fn connect(host: Int64, port: UInt16 = 443, secure: Bool = true) {}\n\n\
     fn g() {\n\
    \  connect(1, secure: false)\n\
     }\n"
    "{ app::main::connect(1, default, false) }";
  builds "a place is lent to a parameter that borrows, and its value given to one that owns"
    "fn keep(items: own List[Int64], limit: Int64) {}\n\n\
     fn g(items: List[Int64], limit: Int64) {\n\
    \  keep(own items, limit)\n\
     }\n"
    "{ app::main::keep(own items, place limit) }";
  builds "a method call has its receiver first"
    "fn g(items: mut List[Int64]) -> USize {\n  mut items.push(4)\n  items.length()\n}\n"
    "{ standard::list::List.push(mut self)[Int64](mut place items, own 4); \
     standard::list::List.length[Int64](place items) }";
  builds "an owned collection is viewed where its view is expected"
    "fn greet(text: StringSlice) {}\n\nfn g(name: String) {\n  greet(name)\n}\n"
    "{ app::main::greet(view through standard::text::String.slice(name)) }";
  builds "a capability's method, and the compiler's copy"
    "fn g(count: Int64) -> Int64\n  uses Clock\n{\n  let _ = Clock.now()\n  count.copy()\n}\n"
    "{ let _ = standard::capabilities::Clock.now(); copy(place count) }";
  builds "a lambda has its parameters and what it captures"
    "fn g(items: List[Int64], step: Int64) -> List[Int64] {\n\
    \  items.map(fn(item) { item + step })\n\
     }\n"
    "{ standard::list::List.map[Int64, Int64](place items, lambda(item) capturing step { add(item, \
     step) }) }"

(* Values *)

let () =
  builds "a record is built with every field, and a default where none is given"
    (shape ^ "fn g() -> Shape {\n  Shape.Square(side: 2)\n}\n")
    "{ Shape.Square(side: 2, label: default) }";
  builds "a range written as a value is its record" "fn g() -> Range[Int64] {\n  1..5\n}\n"
    "{ Range[Int64](start: 1, stop: 5, inclusive: false) }";
  builds "an interpolated string is its pieces, each with its display"
    "fn g(name: String, count: Int64) -> String {\n  \"${name}: ${count}\"\n}\n"
    "{ interpolated(name through Display.display for String by standard::text::impl Display for \
     String, \": \", count through Display.display for Int64 by standard::numbers::signed::impl \
     Display for Int64) }";
  builds "a list literal, a slice, and an index"
    "fn g() -> Int64 {\n  let numbers = [1, 2, 3]\n  let _ = numbers[1..]\n  numbers[0]\n}\n"
    "{ let own numbers = list[1, 2, 3]; let _ = numbers[1..]; lent Index.at for List[Int64] by \
     standard::list::impl Index for List[Element](place numbers, 0) lends }";
  builds "`with` names the fields it replaces, and its shorthand the local"
    "type Config(port: Int64, host: String)\n\n\
     fn g(config: Config, port: Int64) -> Config {\n\
    \  config with (port)\n\
     }\n"
    "{ config with (port: port) }"

(* Control *)

let () =
  builds "`?` is a match that gives the value or returns what there is in its place"
    "fn parse(text: String) -> Result[Int64, String] { todo }\n\n\
     fn g(text: String) -> Result[Int64, String] {\n\
    \  let value = parse(text)?\n\
    \  Ok(value)\n\
     }\n"
    "{ let own value = match app::main::parse(place text) { Ok(value: own value) => { value } \
     Err(error: own error) => { return Result[Int64, String].Err(error: error) } never ends }; \
     Result[Int64, String].Ok(value: value) }";
  builds "a match binds the parts of a place where they are"
    (shape
   ^ "fn g(shape: Shape) -> Int64 {\n\
     \  match shape {\n\
     \    Circle(radius) => radius\n\
     \    Square(side, ..) if side > 2 => side\n\
     \    _ => 0\n\
     \  }\n\
      }\n")
    "{ match place shape { Circle(radius: radius) => { radius } Square(side: side) if (side > 2) \
     => { side } _ => { 0 } } }";
  builds "`is` matches, and a branch that returns never ends"
    (shape
   ^ "fn g(shape: Shape) -> Int64 {\n  if shape is Circle(radius) { return radius }\n  0\n}\n")
    "{ if (place shape is Circle(radius: radius)) { return radius } never ends; 0 }";
  builds "a loop over a value calls its each, and one over a range counts"
    "fn g(items: List[Int64]) -> Int64 {\n\
    \  var total = 0\n\
    \  for item in items {\n\
    \    total += item\n\
    \  }\n\
    \  for step in 0..=total {}\n\
    \  while total < 3 {\n\
    \    total += 1\n\
    \  }\n\
    \  total\n\
     }\n"
    "{ let var own total = 0; for item in each standard::list::List.each[Int64](place items) { \
     update total = add(updating, item) }; for step in count 0..=total {  }; while (total < 3) { \
     update total = add(updating, 1) }; total }"

(* Specifications *)

let () =
  shows "a condition says whether it runs"
    "fn g(items: List[Int64], limit: Int64) -> Int64\n\
    \  requires limit > 0\n\
    \  requires forall index in 0..items.length() => items[index] < limit\n\
    \  ensures result >= 0\n\
     {\n\
    \  proof {\n\
    \    assert limit > 0\n\
    \  }\n\
    \  limit\n\
     }\n"
    "fn(items: List[Int64], limit: Int64)\n\
     requires (limit > 0)\n\
     requires forall index in 0..standard::list::List.length[Int64](place items) { (lent Index.at \
     for List[Int64] by standard::list::impl Index for List[Element](place items, place index) \
     lends < limit) } (not run)\n\
     ensures (result >= 0)\n\
     { proof { assert (limit > 0) }; limit }"

(* Less common forms *)

let () =
  builds "a tagged string is its from_template, given the template"
    "type Shout(text: String)\n\n\
     impl FromTemplate for Shout {\n\
    \  type Part = String\n\n\
    \  fn from_template(template: Template[String]) -> Shout { todo }\n\
     }\n\n\
     fn g(name: String) -> Shout {\n\
    \  Shout\"hey ${name}!\"\n\
     }\n"
    "{ FromTemplate.from_template for Shout by app::main::impl FromTemplate for \
     Shout(Template[String](literals: list[Literal(text: \"hey \"), Literal(text: \"!\")], parts: \
     list[name])) }";
  builds "a cursor is pulled, by a loop or by hand"
    "fn count_to(limit: Int64) yields Int64 {\n\
    \  yield limit\n\
     }\n\n\
     fn g() {\n\
    \  var first = count_to(3)\n\
    \  while mut first.next() is Some(left) {\n\
    \    let _ = left\n\
    \  }\n\
    \  for value in count_to(2) {}\n\
    \  for value in first {}\n\
     }\n"
    "{ let var own first = app::main::count_to(3); while (next(first) is Some(value: left)) { let \
     _ = place left }; for value in each app::main::count_to(2) {  }; for value in pull first {  } \
     }";
  builds "`any` holds how its trait is implemented, and a call through it is dynamic"
    "trait Source {\n\
    \  type Item\n\
    \  fn first(self) -> Self.Item\n\
     }\n\n\
     type Numbers(items: List[Int64])\n\n\
     impl Source for Numbers {\n\
    \  type Item = Int64\n\n\
    \  fn first(self) -> Int64 {\n\
    \    self.items[0]\n\
    \  }\n\
     }\n\n\
     fn g(numbers: own Numbers) -> Int64 {\n\
    \  let source: any Source[Item = Int64] = any numbers\n\
    \  source.first()\n\
     }\n"
    "{ let own source = any Source[Item = Int64](numbers by app::main::impl Source for Numbers); \
     Source[Item = Int64].first for any Source[Item = Int64] by any(place source) }";
  builds "a part lent to change is a place, reached through the mut index"
    "type Cell(state: Int64)\n\n\
     type Grid(cells: List[Cell])\n\n\
     fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
    \  yield mut self.cells[index]\n\
     }\n\n\
     fn g(grid: mut Grid) {\n\
    \  mut grid.cell(0).state = 4\n\
     }\n"
    "{ lent app::main::Grid.cell(mut self)(mut place grid, 0) lends mut.state = 4 }";
  test "a method that lends to change yields the place it changes" (fun () ->
      let found =
        body
          "type Cell(state: Int64)\n\n\
           type Grid(cells: List[Cell])\n\n\
           fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
          \  yield mut self.cells[index]\n\
           }\n"
          "Grid.cell(mut self)"
      in
      if
        found
        <> "{ yield mut place lent Index.at for List[Cell] by standard::list::impl Index for \
            List[Element](mut place self.cells, place index) lends mut }"
      then fail "found:\n%s" found);
  builds "patterns compare with constants, ranges, and strings"
    "let limit: Int64 = 10\n\n\
     fn g(count: Int64, name: String) -> Int64 {\n\
    \  let size = match count {\n\
    \    limit => 1\n\
    \    0..5 => 2\n\
    \    7 | 8 => 3\n\
    \    _ => 4\n\
    \  }\n\
    \  match name {\n\
    \    \"yes\" => size\n\
    \    _ => 0\n\
    \  }\n\
     }\n"
    "{ let own size = match place count { app::main::limit => { 1 } 0..5 => { 2 } 7 | 8 => { 3 } _ \
     => { 4 } }; match place name { equal to \"yes\" => { size } _ => { 0 } } }";
  shows "a quantifier over a type, and old"
    "fn g(count: Int64) -> Bool\n\
    \  ensures result == (forall value: Int64 => value + 0 == value)\n\
    \  ensures old(count) == count\n\
     {\n\
    \  true\n\
     }\n"
    "fn(count: Int64)\n\
     ensures (result == forall value: Int64 { (add(to_integer(value), to_integer(0)) == \
     to_integer(value)) })\n\
     ensures (old(count) == count)\n\
     { true }"

let () =
  builds "part of a place is changed through a slice of it"
    "fn sort_part(part: mut Slice[Int64]) {}\n\n\
     fn g(items: mut List[Int64]) {\n\
    \  sort_part(mut items[..2])\n\
     }\n"
    "{ app::main::sort_part(mut items[..2]) }"

(* Capabilities *)

let () =
  let apply =
    "fn apply[capability Granted](run: (fn() uses Granted))\n\
    \  uses Granted\n\
     {\n\
    \  run()\n\
     }\n\n\
     fn shout()\n\
    \  uses Console\n\
     {\n\
    \  Console.print_line(\"named\")\n\
     }\n\n"
  in
  builds "a capability parameter is the set that what is passed for it uses"
    (apply ^ "fn g()\n  uses Console\n{\n  apply(fn() { Console.print_line(\"inside\") })\n}\n")
    "{ app::main::apply[{Console}](lambda() { standard::capabilities::Console.print_line(view \
     through standard::text::String.slice(\"inside\")) }) }";
  builds "a function passed for a capability parameter is passed as it is"
    (apply ^ "fn g()\n  uses Console\n{\n  apply(shout)\n}\n")
    "{ app::main::apply[{Console}](fn app::main::shout) }";
  test "what a call needs and what a lambda is hold the set, not the parameter" (fun () ->
      let text =
        apply ^ "fn g()\n  uses Console\n{\n  apply(fn() { Console.print_line(\"inside\") })\n}\n"
      in
      let database = setup [ ("app::main", text) ] in
      let found = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.parts
                  {
                    Core_walk.nothing with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = Function { path; _ }; uses; _ }
                          when Path.show path = "app::main::apply" ->
                            found := ("needs " ^ Types.show_argument (Capabilities uses)) :: !found
                        | Lambda _ -> found := Types.show node.type_ :: !found
                        | _ -> ());
                  }
                  form.parts
            | None -> fail "no form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !found <> [ "(fn() uses Console)"; "needs {Console}" ] then
        fail "found [%s]" (String.concat "; " !found));
  test "a capability parameter in a result is the set of each call" (fun () ->
      let text =
        "fn later[capability Granted](run: (fn() uses Granted)) -> (fn() uses Granted) {\n\
        \  run\n\
         }\n\n\
         fn g()\n\
        \  uses Console, Clock\n\
         {\n\
        \  let first = later(fn() { Console.print_line(\"x\") })\n\
        \  let second = later(fn() {\n\
        \    let _ = Clock.now()\n\
        \  })\n\
        \  first()\n\
        \  second()\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      let found = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.parts
                  {
                    Core_walk.nothing with
                    pattern =
                      (fun (node : Core.pattern) ->
                        match node.kind with
                        | Bind { name; _ } ->
                            found := (name ^ ": " ^ Types.show node.type_) :: !found
                        | _ -> ());
                  }
                  form.parts
            | None -> fail "no form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !found <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then fail "found [%s]" (String.concat "; " !found))

(* Where a node came from *)

let () =
  test "a node's origin finds the source it came from" (fun () ->
      let text =
        "fn g(items: List[Int64]) -> Int64 {\n\
        \  var total = 0\n\
        \  for item in items {\n\
        \    total += item\n\
        \  }\n\
        \  total\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | Some form, Some spans, Some written ->
              let found = ref [] in
              Core_walk.parts
                {
                  Core_walk.nothing with
                  statement =
                    (fun (node : Core.statement) ->
                      match node.kind with
                      | Update _ ->
                          let span = spans.(node.origin) in
                          found := String.sub written span.start (span.stop - span.start) :: !found
                      | _ -> ());
                }
                form.parts;
              if !found <> [ "total += item" ] then fail "found [%s]" (String.concat "; " !found)
          | _ -> fail "no form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

let () =
  shows "a cost clause says what it counts"
    "fn g(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
    \  uses Clock\n\
    \  cost calls(visit) == items.length()\n\
    \  cost calls(Clock.now) <= 1\n\
    \  cost time O(items.length() * time(visit))\n\
     {\n\
     }\n"
    "fn(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
     cost calls(visit) == standard::list::List.length[Int64](place items)\n\
     cost calls(standard::capabilities::Clock.now) <= 1\n\
     cost time O(multiply(to_integer(standard::list::List.length[Int64](place items)), time(visit)))\n\
     {  }"

(* Every form of the standard library holds together. *)

let () =
  let database = setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s's core forms hold together" (Path.show_module module_))
        (fun () ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              let key = Resolve.Names.key_of declaration in
              match Query.demand database Infer.core key with
              | None -> ()
              | Some form ->
                  incr forms;
                  let seen = Hashtbl.create 64 in
                  let wrong format =
                    Printf.ksprintf
                      (fun message -> fail "%s: %s" (Resolve.Names.show_key key) message)
                      format
                  in
                  let once id =
                    if id < 0 || id >= form.nodes then wrong "the id %d is out of range" id;
                    if Hashtbl.mem seen id then wrong "the id %d is used twice" id;
                    Hashtbl.replace seen id ()
                  in
                  let known what capabilities =
                    if Types.unknown_capabilities capabilities then
                      wrong "%s holds an unknown set of capabilities" what;
                    capabilities
                  in
                  let decided what (type_ : Types.ty) =
                    if Types.contains_unsolved type_ then
                      wrong "%s has the type `%s`" what (Types.show type_);
                    ignore (Types.map_capabilities (known what) type_)
                  in
                  let called (callee : Core.callee) =
                    match callee with
                    | Function { type_arguments; _ } | Trait_method { type_arguments; _ } ->
                        List.iter
                          (fun argument ->
                            ignore
                              (Types.map_argument_capabilities (known "a type argument") argument))
                          type_arguments
                    | Capability_method _ | Intrinsic _ | Value _ -> ()
                  in
                  let rec place (found : Core.place) =
                    match found with
                    | Lent { kind = Call { lends = Some _; _ }; _ } | Local _ | Temporary _ -> ()
                    | Lent _ -> wrong "a lent part is not a call that lends"
                    | Field { base; _ } -> place base
                  in
                  Core_walk.parts
                    {
                      expression =
                        (fun (node : Core.expression) ->
                          once node.id;
                          decided "an expression" node.type_;
                          match node.kind with
                          | Use found | Next found -> place found
                          | Call { callee; arguments; uses; _ } ->
                              called callee;
                              ignore (known "what a call needs" uses);
                              List.iter
                                (function
                                  | Core.Passed { mode = Mut; value = Value { kind = Slice _; _ } }
                                    ->
                                      ()
                                  | Core.Passed { mode = Mut; value = Value _ } ->
                                      wrong "a value is passed where a place is changed"
                                  | Passed { mode = Own; value = Place _ } ->
                                      wrong "a place is passed where a value is taken"
                                  | _ -> ())
                                arguments
                          | _ -> ());
                      statement =
                        (fun (node : Core.statement) ->
                          once node.id;
                          match node.kind with
                          | Assign { target; _ } | Update { target; _ } -> place target
                          | _ -> ());
                      pattern =
                        (fun (node : Core.pattern) ->
                          once node.id;
                          decided "a pattern" node.type_);
                      callee = ignore;
                    }
                    form.parts)
            (Query.demand database Resolve.Names.declarations module_)))
    Standard_library.modules;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

(* Derived methods *)

let derived text type_name trait name receiver =
  let database = setup [ ("app::main", text) ] in
  let path : Path.t =
    Method
      {
        owner =
          Derived
            {
              type_ = Top { module_ = module_of "app::main"; name = type_name };
              trait = Top { module_ = { package = "standard"; modules = [ "core" ] }; name = trait };
            };
        name;
        receiver;
      }
  in
  match Query.demand database Infer.derived path with
  | Some form -> Core_print.show form
  | None -> failwith "the derived method has no core form"

let derives what text type_name trait name receiver expected =
  test what (fun () ->
      let found = derived text type_name trait name receiver in
      if found <> expected then fail "found:\n%s" found)

let pair =
  "type Pair[Second](first: Int64, second: Second)\n  derives Equal, Hash, Ordered, Default\n\n"

let light =
  "type Light =\n  | Off\n  | Dim(level: Int64)\n  | On\n  derives Equal, Hash, Ordered\n\n"

let () =
  derives "a record's derived equal compares each field" pair "Pair" "Equal" "equal" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { (Equal.equal for Int64 by standard::numbers::signed::impl Equal for Int64(place self.first, \
     place other.first) && Equal.equal for Second by a bound(place self.second, place \
     other.second)) }";
  derives "a sum's derived equal binds each variant's fields, and is false of another variant" light
    "Light" "Equal" "equal" Read
    "fn(self: Light, other: Light)\n\
     { match place self { Off => { (place other is Off) } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Equal.equal for Int64 by standard::numbers::signed::impl Equal \
     for Int64(place level, place other_level) } _ => { false } } } On => { (place other is On) } \
     } }";
  derives "a derived hash writes the variant's number and then each field" light "Light" "Hash"
    "hash" Read
    "fn(self: Light, mut hasher: Hasher)\n\
     { match place self { Off => { standard::core::Hasher.write(mut self)(mut place hasher, 0) } \
     Dim(level: level) => { standard::core::Hasher.write(mut self)(mut place hasher, 1); Hash.hash \
     for Int64 by standard::numbers::signed::impl Hash for Int64(place level, mut place hasher) } \
     On => { standard::core::Hasher.write(mut self)(mut place hasher, 2) } } }";
  derives "a record's derived compare goes on to the next field only where one is equal" pair "Pair"
    "Ordered" "compare" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { match Ordered.compare for Int64 by standard::numbers::signed::impl Ordered for Int64(place \
     self.first, place other.first) { Equal => { Ordered.compare for Second by a bound(place \
     self.second, place other.second) } own decided => { decided } } }";
  derives "a sum's derived compare orders by variant, then by the fields a variant binds" light
    "Light" "Ordered" "compare" Read
    "fn(self: Light, other: Light)\n\
     { let own theirs = match place other { Off => { 0 } Dim => { 1 } On => { 2 } }; match place \
     self { Off => { match place other { Off => { Ordering.Equal() } _ => { if (0 < theirs) { \
     Ordering.Less() } else { Ordering.Greater() } } } } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Ordered.compare for Int64 by standard::numbers::signed::impl \
     Ordered for Int64(place level, place other_level) } _ => { if (1 < theirs) { Ordering.Less() \
     } else { Ordering.Greater() } } } } On => { match place other { On => { Ordering.Equal() } _ \
     => { if (2 < theirs) { Ordering.Less() } else { Ordering.Greater() } } } } } }";
  derives "a derived default is each field's" pair "Pair" "Default" "default" Static
    "fn()\n\
     { Pair[Second](first: Default.default for Int64 by standard::numbers::signed::impl Default \
     for Int64(), second: Default.default for Second by a bound()) }";
  test "a type still to be written has no derived form" (fun () ->
      let database = setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
      let path : Path.t =
        Method
          {
            owner =
              Derived
                {
                  type_ = Top { module_ = module_of "app::main"; name = "Later" };
                  trait =
                    Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Equal" };
                };
            name = "equal";
            receiver = Read;
          }
      in
      if Query.demand database Infer.derived path <> None then fail "it has a form");
  test "every method a derived impl in the standard library gives has a core form" (fun () ->
      let database = setup [] in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (Query.demand database Interface.Impls.index "standard")
      in
      if derived = [] then fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Impls.impl_interface database impl with
          | None -> fail "`%s` has no interface" (Path.show impl)
          | Some interface ->
              let provided =
                match
                  Query.demand database Interface.Environment.trait_interface
                    interface.implements.trait
                with
                | Some trait ->
                    List.filter_map
                      (fun (method_ : Types.trait_method) ->
                        if method_.provided then Some method_.method_name else None)
                      trait.methods
                | None -> []
              in
              List.iter
                (fun (name, receiver, _) ->
                  match
                    Query.demand database Infer.derived (Method { owner = impl; name; receiver })
                  with
                  | Some _ -> ()
                  | None ->
                      if not (List.mem name provided) then
                        fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      fail "`%s`, `%s`: %s" (Path.show impl) name (Compiler_bug.to_string bug))
                interface.impl_methods)
        derived)

(* The form at a path *)

let () =
  let text =
    "trait Described {\n\
    \  fn describe(self) -> Int64\n\n\
    \  fn twice(self) -> Int64 {\n\
    \    self.describe() + self.describe()\n\
    \  }\n\
     }\n\n\
     type Both[Value](first: Value, second: Value)\n\
    \  derives Equal\n\n\
     impl Described for Both[Value: Described] {\n\
    \  fn describe(self) -> Int64 {\n\
    \    self.first.describe()\n\
    \  }\n\
     }\n"
  in
  let both : Path.t = Top { module_ = module_of "app::main"; name = "Both" } in
  let described : Types.trait_reference =
    {
      trait = Top { module_ = module_of "app::main"; name = "Described" };
      trait_arguments = [];
      associated = [];
    }
  in
  let at name =
    let database = setup [ ("app::main", text) ] in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let bounds (found : Types.parameter) = if found = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.implements database ~bounds
          (Types.named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match Query.demand database Infer.core_at (Method { owner; name; receiver = Read }) with
    | Some (form, substitution) ->
        ( List.hd (List.rev (String.split_on_char '\n' (Core_print.show form))),
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            substitution )
    | None -> failwith "no form"
  in
  test "a method an impl writes has its own form" (fun () ->
      match at "describe" with
      | "{ Described.describe for Value by a bound(place self.first) }", [] -> ()
      | found, _ -> fail "found %s" found);
  test "a method an impl leaves to its trait has the trait's form, with what Self is" (fun () ->
      match at "twice" with
      | ( "{ add(Described.describe for Self by a bound(place self), Described.describe for Self \
           by a bound(place self)) }",
          [ "Self = Both[Value]" ] ) ->
          ()
      | found, substitution -> fail "found %s with [%s]" found (String.concat "; " substitution));
  test "a method a derived impl gives has the form made from the type" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let owner : Path.t =
        Derived
          {
            type_ = both;
            trait = Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Equal" };
          }
      in
      match
        ( Query.demand database Infer.core_at (Method { owner; name = "equal"; receiver = Read }),
          Query.demand database Infer.core_at
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, []), Some (_, [ _ ]) -> ()
      | _ -> fail "the derived method and the one left to the trait are not both found")

let () = finish ()
