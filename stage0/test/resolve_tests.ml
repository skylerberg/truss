(* The tests of name resolution. Each gives a few small files and states one
   fact: what a name refers to, or the one diagnostic, with its code and the
   text after applying its fix. See TYPECHECKER.md, "Name resolution" and
   "Testing". *)

open Harness

let module_of text : Path.module_ =
  match String.split_on_char ':' text |> List.filter (( <> ) "") with
  | package :: modules -> { package; modules }
  | [] -> invalid_arg text

(* A small standard library, enough for the prelude names these tests use. *)
let standard =
  [
    ("standard::option", "public type Option[Value] = Some(value: Value) | None\n");
    ("standard::result", "public type Result[Value, Error] = Ok(value: Value) | Err(error: Error)\n");
    ( "standard::core",
      "public trait Equal {\n\
      \  fn equal(self, other: Self) -> Bool\n\
       }\n\n\
       public type Ordering = Less | Same | Greater\n" );
    ("standard::list", "public opaque type List[Element](length: USize)\n");
  ]

let setup files =
  let database = Query.create ~log:true () in
  let all = standard @ files in
  let by_package = Hashtbl.create 4 in
  List.iter
    (fun (name, text) ->
      let module_ = module_of name in
      Query.set database Workspace.file_text module_ text;
      Hashtbl.replace by_package module_.package
        (module_ :: Option.value ~default:[] (Hashtbl.find_opt by_package module_.package)))
    all;
  Hashtbl.iter
    (fun package modules ->
      Query.set database Workspace.packages package
        { Workspace.name = package; dependencies = []; modules = List.rev modules })
    by_package;
  database

let parse_errors database module_ =
  List.map
    (fun (d : Diagnostic.t) -> d.message)
    (Query.demand database Workspace.file module_).diagnostics

let diagnostics database name =
  let module_ = module_of name in
  (match parse_errors database module_ with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  Resolve.diagnostics database module_

let codes diagnostics = List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) diagnostics

let no_diagnostics files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      match diagnostics database name with
      | [] -> ()
      | found ->
          fail "%s: %s" name
            (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)))
    files

(* The one diagnostic of the file [app::main], with its code, and, if
   [fixed] is given, the text after applying its first fix, which must
   resolve with no diagnostic left. *)
let one_diagnostic ?(others = []) ?fixed text code =
  let files = ("app::main", text) :: others in
  let database = setup files in
  match diagnostics database "app::main" with
  | [ diagnostic ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then fail "expected %s, got %s: %s" code actual diagnostic.message;
      match (fixed, diagnostic.fixes) with
      | None, _ -> ()
      | Some _, [] -> fail "no fix"
      | Some expected, fix :: _ ->
          let after = Diagnostic.apply_fix text fix in
          if after <> expected then fail "fixed to %S" after
          else begin
            let database = setup (("app::main", after) :: others) in
            match diagnostics database "app::main" with
            | [] -> ()
            | left -> fail "after the fix: %s" (String.concat "; " (codes left))
          end)
  | found -> fail "expected one %s, got [%s]" code (String.concat "; " (codes found))

(* Finding names *)

(* The name at the [occurrence]th appearance of [text] in the file, with the
   resolved form of the definition it is in. *)
let name_at database file text occurrence =
  let module_ = module_of file in
  let source = Workspace.(Source.text (Query.demand database file module_).source) in
  let offset = Documents.find source text ~occurrence in
  if offset < 0 then failwith (Printf.sprintf "no occurrence %d of %S" occurrence text);
  let found =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( Query.demand database Resolve.Names.definition key,
            Query.demand database Resolve.Names.base key,
            Query.demand database Resolve.resolved key )
        with
        | Some definition, Some (_, base), Some resolved ->
            let names = Syntax_walk.names definition in
            Option.map
              (fun (name : Syntax.name) -> (name, names, base, resolved))
              (List.find_opt (fun (name : Syntax.name) -> base + name.span.start = offset) names)
        | _ -> None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match found with Some found -> found | None -> failwith (Printf.sprintf "no name at %S" text)

let describe names base (target : Resolve.target option) =
  let offset id =
    match List.find_opt (fun (name : Syntax.name) -> name.id = id) names with
    | Some name -> base + name.span.start
    | None -> -1
  in
  match target with
  | None -> "nothing"
  | Some Binding -> "binding"
  | Some (Local id) -> Printf.sprintf "local at %d" (offset id)
  | Some (Generic id) -> Printf.sprintf "generic at %d" (offset id)
  | Some (Definition path) -> Path.show path
  | Some (Variant (type_, name)) -> Printf.sprintf "variant %s of %s" name (Path.show type_)
  | Some (Module module_) -> "module " ^ Path.show_module module_
  | Some (Field name) -> "field " ^ name
  | Some Result_value -> "result"
  | Some Old -> "old"
  | Some (Cost_function _) -> "cost function"
  | Some Unknown -> "unknown"

let refers ?(others = []) text ~name:(written, occurrence) expected =
  let database = setup (("app::main", text) :: others) in
  let name, names, base, resolved = name_at database "app::main" written occurrence in
  let actual = describe names base resolved.names.(name.id) in
  if actual <> expected then fail "`%s` #%d is %s, not %s" written occurrence actual expected

(* [refers_to_binding]: the name at one occurrence refers to the local bound
   at another. *)
let refers_to_binding text ~use ~binding =
  let database = setup [ ("app::main", text) ] in
  let source = text in
  let binding_offset = Documents.find source (fst binding) ~occurrence:(snd binding) in
  let name, names, base, resolved = name_at database "app::main" (fst use) (snd use) in
  let actual = describe names base resolved.names.(name.id) in
  let expected = Printf.sprintf "local at %d" binding_offset in
  if actual <> expected then fail "`%s` is %s, not %s" (fst use) actual expected

(* Locals and scopes *)

let () =
  test "a local refers to the let that binds it" (fun () ->
      refers_to_binding "fn f() -> Int64 {\n  let count = 1\n  count\n}\n" ~use:("count", 2)
        ~binding:("count", 1));
  test "a parameter is a local of the body" (fun () ->
      refers_to_binding "fn f(count: Int64) -> Int64 {\n  count\n}\n" ~use:("count", 2)
        ~binding:("count", 1));
  test "a name bound by is is in scope in the if's block" (fun () ->
      refers_to_binding
        "fn f(found: Option[Int64]) -> Int64 {\n  if found is Some(value) { value } else { 0 }\n}\n"
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound by is is in scope in the rest of its && chain" (fun () ->
      refers_to_binding
        "fn f(found: Option[Int64]) -> Bool {\n  found is Some(value) && value > 0\n}\n"
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound by is is not in scope in the else" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n  if found is Some(value) { 0 } else { value }\n}\n"
        "resolve.unknown_name");
  test "a name bound by is is not in scope after ||" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64], other: Bool) -> Bool {\n\
        \  found is Some(value) || value > 0\n\
         }\n"
        "resolve.unknown_name");
  test "a name bound by let else is in scope after it" (fun () ->
      refers_to_binding
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  let Some(value) = found else {\n\
        \    return 0\n\
        \  }\n\
        \  value\n\
         }\n"
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound in a match arm is in scope in its guard and body" (fun () ->
      refers_to_binding
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Some(value) if value > 0 => value\n\
        \    _ => 0\n\
        \  }\n\
         }\n"
        ~use:("value", 3) ~binding:("value", 1));
  test "a let in a parallel branch is in scope after the block" (fun () ->
      refers_to_binding
        "fn f() -> Int64 {\n  parallel {\n    let left = 1\n    let right = 2\n  }\n  left\n}\n"
        ~use:("left", 2) ~binding:("left", 1));
  test "a let in a parallel branch is not in scope in another branch" (fun () ->
      one_diagnostic
        "fn f() -> Int64 {\n  parallel {\n    let left = 1\n    let right = left\n  }\n  right\n}\n"
        "resolve.unknown_name");
  test "a lambda's parameter is in scope in its body" (fun () ->
      refers_to_binding "fn f() -> fn(Int64) -> Int64 {\n  fn(item) { item }\n}\n" ~use:("item", 2)
        ~binding:("item", 1));
  test "a local is not in scope after its block" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  {\n    let inner = 1\n  }\n  inner\n}\n"
        "resolve.unknown_name")

(* No name hides another *)

let () =
  test "a local cannot hide a local of an enclosing block" (fun () ->
      one_diagnostic "fn f() {\n  let count = 1\n  {\n    let count = 2\n  }\n}\n"
        "resolve.hides_name");
  test "a local cannot hide a parameter" (fun () ->
      one_diagnostic "fn f(name: Int64) {\n  let name = 2\n}\n" "resolve.hides_name");
  test "a local cannot share a name with a function in the same file" (fun () ->
      one_diagnostic "fn total() -> Int64 { 0 }\n\nfn f() {\n  let total = 2\n}\n"
        "resolve.hides_name");
  test "a generic parameter cannot hide a prelude type" (fun () ->
      one_diagnostic "fn f[Option](value: Option) {}\n" "resolve.hides_name");
  test "locals in sibling blocks may share a name" (fun () ->
      no_diagnostics
        [ ("app::main", "fn f() {\n  {\n    let count = 1\n  }\n  {\n    let count = 2\n  }\n}\n") ])

(* Patterns *)

let () =
  test "a bare name in a pattern that names a constant is the constant" (fun () ->
      refers
        "let limit: Int64 = 10\n\n\
         fn f(value: Int64) -> Bool {\n\
        \  match value {\n\
        \    limit => true\n\
        \    _ => false\n\
        \  }\n\
         }\n"
        ~name:("limit", 2) "app::main::limit");
  test "any other bare name in a pattern binds" (fun () ->
      refers "fn f(value: Int64) -> Int64 {\n  match value {\n    other => other\n  }\n}\n"
        ~name:("other", 1) "binding");
  test "the alternatives of a pattern must bind the same names" (fun () ->
      one_diagnostic
        "fn f(found: Result[Int64, Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Ok(value) | Err(error) => 0\n\
        \  }\n\
         }\n"
        "resolve.alternative_bindings");
  test "an alternative's name refers to the first alternative's binding" (fun () ->
      refers_to_binding
        "fn f(found: Result[Int64, Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Ok(value) | Err(value) => value\n\
        \  }\n\
         }\n"
        ~use:("value", 3) ~binding:("value", 1));
  test "the end of a range pattern must be a constant" (fun () ->
      one_diagnostic
        "fn f(value: Int64) -> Bool {\n\
        \  match value {\n\
        \    0..=top => true\n\
        \    _ => false\n\
        \  }\n\
         }\n"
        "resolve.not_a_constant")

(* Unknown names *)

let () =
  test "an unknown name is an error with a fix to the closest name" (fun () ->
      one_diagnostic "fn f(count: Int64) -> Int64 {\n  cuont\n}\n" "resolve.unknown_name"
        ~fixed:"fn f(count: Int64) -> Int64 {\n  count\n}\n");
  test "null is an error with a fix that writes None" (fun () ->
      one_diagnostic "fn f() -> Option[Int64] {\n  null\n}\n" "resolve.null"
        ~fixed:"fn f() -> Option[Int64] {\n  None\n}\n");
  test "an unknown type is an error" (fun () ->
      one_diagnostic "fn f(value: Strng) {}\n" "resolve.unknown_name")

(* The prelude *)

let () =
  test "a prelude type is the standard library's" (fun () ->
      refers "fn f(value: Option[Int64]) {}\n" ~name:("Option", 1) "standard::option::Option");
  test "a built-in type is the intrinsic module's" (fun () ->
      refers "fn f(value: Int64) {}\n" ~name:("Int64", 1) "standard::intrinsic::Int64");
  test "a prelude variant is written bare" (fun () ->
      refers "fn f() -> Option[Int64] {\n  Some(1)\n}\n" ~name:("Some", 1)
        "variant Some of standard::option::Option")

(* Brackets *)

let bracket_of text written occurrence =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  let offset = Documents.find text written ~occurrence in
  let declarations = Query.demand database Resolve.Names.declarations module_ in
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match
        ( Query.demand database Resolve.Names.definition key,
          Query.demand database Resolve.Names.base key,
          Query.demand database Resolve.resolved key )
      with
      | Some definition, Some (_, base), Some resolved ->
          let found = ref None in
          Syntax_walk.definition
            (let rec visit (value : Syntax.expression) =
               (match value.kind with
               | Bracket _ when base + value.span.start = offset ->
                   found := resolved.brackets.(value.id)
               | _ -> ());
               Syntax_walk.children visit value
             in
             visit)
            definition;
          !found
      | _ -> None)
    declarations

let () =
  test "brackets after a generic function give type arguments" (fun () ->
      let text =
        "fn parse[Value](text: Int64) -> Option[Value] { todo }\n\n\
         fn f() {\n\
        \  let _ = parse[Int64](1)\n\
         }\n"
      in
      match bracket_of text "parse[Int64]" 1 with
      | Some Resolve.Type_arguments -> ()
      | _ -> fail "not type arguments");
  test "brackets after a local index it" (fun () ->
      let text = "fn f(items: List[Int64]) -> Int64 {\n  items[0]\n}\n" in
      match bracket_of text "items[0]" 1 with Some Resolve.Index -> () | _ -> fail "not an index");
  test "brackets after a method are left to type checking" (fun () ->
      let text = "fn f(items: List[Int64]) {\n  let _ = items.map[Int64]\n}\n" in
      match bracket_of text "items.map[Int64]" 1 with
      | Some Resolve.Method_bracket -> ()
      | _ -> fail "decided");
  test "brackets after a function without generic parameters are an error" (fun () ->
      one_diagnostic "fn count() -> Int64 { 0 }\n\nfn f() -> Int64 {\n  count[0]\n}\n"
        "resolve.not_generic")

(* Places *)

let () =
  test "mut before a call to a function is an error with a fix that removes it" (fun () ->
      one_diagnostic "fn make() -> List[Int64] { todo }\n\nfn f() {\n  mut make().push(1)\n}\n"
        "resolve.not_a_place"
        ~fixed:"fn make() -> List[Int64] { todo }\n\nfn f() {\n  make().push(1)\n}\n");
  test "mut before a local's field and method call is a place" (fun () ->
      no_diagnostics
        [ ("app::main", "fn f() {\n  var items: List[Int64] = []\n  mut items.push(1)\n}\n") ])

(* Specifications *)

let () =
  test "result in ensures is the return value" (fun () ->
      refers "fn f() -> Int64\n  ensures result > 0\n{\n  1\n}\n" ~name:("result", 1) "result");
  test "result outside a specification is an ordinary name" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  result\n}\n" "resolve.unknown_name");
  test "old in a specification is the value on entry" (fun () ->
      refers "fn f(items: mut List[Int64])\n  ensures old(items) == items\n{\n}\n" ~name:("old", 1)
        "old");
  test "log in a cost bound is the cost function" (fun () ->
      refers "fn f(count: USize)\n  cost time O(log(count))\n{\n}\n" ~name:("log", 1)
        "cost function");
  test "a record's fields are in scope in its invariant" (fun () ->
      refers "type Range(low: Int64, high: Int64)\n  invariant low <= high\n" ~name:("low", 2)
        "field low")

(* Modules and imports *)

let others = [ ("app::shapes", "public fn area() -> Int64 { 0 }\n\nfn hidden() -> Int64 { 0 }\n") ]

let () =
  test "a name after an imported module is that module's" (fun () ->
      refers ~others "use app::shapes\n\nfn f() -> Int64 {\n  shapes::area()\n}\n" ~name:("area", 1)
        "app::shapes::area");
  test "a full path needs no use" (fun () ->
      refers ~others "fn f() -> Int64 {\n  app::shapes::area()\n}\n" ~name:("area", 1)
        "app::shapes::area");
  test "a private definition of another file is not visible" (fun () ->
      one_diagnostic ~others "fn f() -> Int64 {\n  app::shapes::hidden()\n}\n" "resolve.not_visible");
  test "an import nothing uses is an error with a fix that deletes it" (fun () ->
      one_diagnostic ~others "use app::shapes\n\nfn f() {}\n" "resolve.unused_import"
        ~fixed:"\nfn f() {}\n");
  test "an import of a module that does not exist is an error" (fun () ->
      one_diagnostic "use app::missing\n\nfn f() {}\n" "resolve.unknown_module");
  test "two imports with one last name are an error at the second" (fun () ->
      one_diagnostic
        ~others:
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("other::shapes", "public fn area() -> Int64 { 0 }\n");
          ]
        "use app::shapes\nuse other::shapes\n\nfn f() -> Int64 {\n  shapes::area()\n}\n"
        "resolve.duplicate_import");
  test "only the standard package can import standard::intrinsic" (fun () ->
      one_diagnostic "use standard::intrinsic\n\nfn f() {}\n" "resolve.intrinsic_import")

(* Definitions *)

let () =
  test "a second definition with one name is an error" (fun () ->
      one_diagnostic "fn f() {}\n\nfn f() {}\n" "resolve.duplicate_definition");
  test "a method's type head names its type" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "type Counter(count: Int64)\n\nfn Counter.get(self) -> Int64 {\n  self.count\n}\n" );
          ]
      in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      match Query.demand database Resolve.Names.members (owner, "get") with
      | [ { path = Method { receiver = Read; _ }; _ } ] -> ()
      | found -> fail "found %d members" (List.length found));
  test "a method can be written in another file of its type's package" (fun () ->
      let database =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ( "app::extra",
              "use app::main\n\nfn main::Counter.get(self) -> Int64 {\n  self.count\n}\n" );
          ]
      in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      match Query.demand database Resolve.Names.members (owner, "get") with
      | [ _ ] -> ()
      | found -> fail "found %d members" (List.length found));
  test "a body the parser could not read is not resolved" (fun () ->
      let database = setup [ ("app::main", "fn f() -> Int64 {\n  let = missing\n}\n") ] in
      let module_ = module_of "app::main" in
      if (Query.demand database Workspace.file module_).diagnostics = [] then fail "parsed";
      match Resolve.diagnostics database module_ with
      | [] -> ()
      | found -> fail "resolved the broken body: %s" (String.concat "; " (codes found)))

(* Incremental work *)

let () =
  test "editing one body resolves only that definition again" (fun () ->
      let text body = "fn first() -> Int64 { 1 }\n\nfn second() -> Int64 { " ^ body ^ " }\n" in
      let database = setup [ ("app::main", text "2") ] in
      let module_ = module_of "app::main" in
      ignore (Resolve.diagnostics database module_);
      Query.set database Workspace.file_text module_ (text "3");
      Query.clear_log database;
      ignore (Resolve.diagnostics database module_);
      let resolved =
        List.filter
          (fun label -> String.length label > 9 && String.sub label 0 9 = "resolved(")
          (Query.executed database)
      in
      if resolved <> [ "resolved(app::main::second)" ] then
        fail "resolved again: %s" (String.concat "; " resolved));
  test "moving a definition down resolves nothing again" (fun () ->
      let database = setup [ ("app::main", "fn first() -> Int64 { 1 }\n") ] in
      let module_ = module_of "app::main" in
      ignore (Resolve.diagnostics database module_);
      Query.set database Workspace.file_text module_ "\n\nfn first() -> Int64 { 1 }\n";
      Query.clear_log database;
      ignore (Resolve.diagnostics database module_);
      if List.mem "resolved(app::main::first)" (Query.executed database) then fail "resolved again")

(* Hashing *)

let parts_of text name =
  let database = setup [ ("app::main", text) ] in
  let key : Resolve.Names.key =
    { module_ = module_of "app::main"; path = Top { module_ = module_of "app::main"; name }; ordinal = 0 }
  in
  match Query.demand database Hash.parts key with
  | Some parts -> List.map (fun (part, digest) -> (Hash.show_part part, Hash.show digest)) parts
  | None -> failwith ("no definition " ^ name)

(* The names of the parts whose hashes differ between two versions. *)
let changed before after name =
  let first = parts_of before name and second = parts_of after name in
  List.sort_uniq compare
    (List.filter_map
       (fun (part, digest) -> if List.assoc_opt part second = Some digest then None else Some part)
       first
    @ List.filter_map
        (fun (part, _) -> if List.mem_assoc part first then None else Some part)
        second)

let expect_changed name before after expected =
  test name (fun () ->
      let actual = changed before after "f" in
      if actual <> expected then fail "changed [%s]" (String.concat "; " actual))

let () =
  expect_changed "reformatting changes no hash" "fn f(count: Int64) -> Int64 {\n  count + 1\n}\n"
    "fn f(count:Int64)->Int64{\n  count  +  1\n}\n" [];
  expect_changed "moving a definition changes no hash" "fn f() -> Int64 { 1 }\n"
    "\n\n\nfn f() -> Int64 { 1 }\n" [];
  expect_changed "how a literal is written does not count" "fn f() -> Int64 { 255 }\n"
    "fn f() -> Int64 { 0xFF }\n" [];
  expect_changed "parentheses do not count" "fn f(a: Int64) -> Int64 { a * 2 }\n"
    "fn f(a: Int64) -> Int64 { (a * 2) }\n" [];
  expect_changed "an ensures changes the contract and not the interface"
    "fn f() -> Int64\n  ensures result > 0\n{\n  1\n}\n"
    "fn f() -> Int64\n  ensures result > 1\n{\n  1\n}\n" [ "contract" ];
  expect_changed "renaming a local changes only the body"
    "fn f() -> Int64 {\n  let count = 1\n  count\n}\n"
    "fn f() -> Int64 {\n  let total = 1\n  total\n}\n" [ "body" ];
  expect_changed "changing a default changes only that default" "fn f(count: Int64 = 1) {}\n"
    "fn f(count: Int64 = 2) {}\n" [ "default count" ];
  expect_changed "editing a proof block changes only that proof"
    "fn f() -> Int64 {\n  proof {\n    assert 1 == 1\n  }\n  1\n}\n"
    "fn f() -> Int64 {\n  proof {\n    assert 2 == 2\n  }\n  1\n}\n" [ "proof 0" ];
  expect_changed "the order between kinds of clause does not count"
    "fn f(a: Int64)\n  requires a > 0\n  ensures a > 0\n{\n}\n"
    "fn f(a: Int64)\n  ensures a > 0\n  requires a > 0\n{\n}\n" [];
  expect_changed "the order within one kind of clause counts"
    "fn f(a: Int64)\n  requires a > 0\n  requires a < 9\n{\n}\n"
    "fn f(a: Int64)\n  requires a < 9\n  requires a > 0\n{\n}\n" [ "contract" ];
  test "a record's field order does not count" (fun () ->
      let actual = changed "type T(a: Int64, b: Int64)\n" "type T(b: Int64, a: Int64)\n" "T" in
      if actual <> [] then fail "changed [%s]" (String.concat "; " actual));
  test "a record's field order counts when it derives Ordered" (fun () ->
      let others = "public trait Ordered {}\n" in
      let database text =
        let database = setup [ ("app::main", text) ] in
        Query.set database Workspace.file_text (module_of "standard::core") others;
        database
      in
      let hash text =
        let database = database text in
        let key : Resolve.Names.key =
          { module_ = module_of "app::main"; path = Top { module_ = module_of "app::main"; name = "T" }; ordinal = 0 }
        in
        Option.get (Query.demand database Hash.parts key)
      in
      if
        hash "type T(a: Int64, b: Int64)\n  derives Ordered\n"
        = hash "type T(b: Int64, a: Int64)\n  derives Ordered\n"
      then fail "same hash")

let () = finish ()
