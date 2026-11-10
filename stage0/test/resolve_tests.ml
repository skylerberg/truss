(* The tests of name resolution. Each gives a few small files and states one
   fact: what a name refers to, or the one diagnostic, with its code and the
   text after applying its fix. *)

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
  let database = Engine.context (Engine.create ~log:true ()) in
  let all = standard @ files in
  let by_package = Hashtbl.create 4 in
  List.iter
    (fun (name, text) ->
      let module_ = module_of name in
      Engine.set (Engine.of_context database) Workspace.file_text module_ text;
      Hashtbl.replace by_package module_.package
        (module_ :: Option.value ~default:[] (Hashtbl.find_opt by_package module_.package)))
    all;
  Hashtbl.iter
    (fun package modules ->
      Engine.set (Engine.of_context database) Workspace.packages package
        { Workspace.name = package; dependencies = []; modules = List.rev modules; usize_bits = 32 })
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
  | Some (Type_parameter parameter | Capability_parameter parameter | Value_parameter parameter) ->
      Printf.sprintf "generic %s of %s" parameter.name (Path.show parameter.owner)
  | Some (Definition (_, path)) -> Path.show path
  | Some (Variant (type_, name)) -> Printf.sprintf "variant %s of %s" name (Path.show type_)
  | Some (Module module_) -> "module " ^ Path.show_module module_
  | Some (Field name) -> "field " ^ name
  | Some Result_value -> "result"
  | Some Old -> "old"
  | Some Identical -> "identical"
  | Some Yielded -> "yielded"
  | Some Finished -> "finished"
  | Some (Cost_function _) -> "cost function"
  | Some (Unknown _) -> "unknown"

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
        [ ("app::main", "fn f() {\n  var items: List[Int64] = []\n  mut items.push(1)\n}\n") ]);
  test "a ? after the marked call works on its result" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "fn f(items: mut List[Option[Int64]]) -> Option[Int64] {\n\
            \  let last = mut items.pop()?\n\
            \  last\n\
             }\n" );
        ]);
  test "a ? before any method call does not make a place" (fun () ->
      one_diagnostic
        "fn make() -> Option[List[Int64]] { todo }\n\n\
         fn f() -> Option[Int64] {\n\
        \  mut make()?.pop()\n\
         }\n"
        "resolve.not_a_place")

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
      Engine.set (Engine.of_context database) Workspace.file_text module_ (text "3");
      Engine.clear_log (Engine.of_context database);
      ignore (Resolve.diagnostics database module_);
      let resolved =
        List.filter
          (fun label -> String.length label > 9 && String.sub label 0 9 = "resolved(")
          (Engine.executed (Engine.of_context database))
      in
      if resolved <> [ "resolved(app::main::second)" ] then
        fail "resolved again: %s" (String.concat "; " resolved));
  test "moving a definition down resolves nothing again" (fun () ->
      let database = setup [ ("app::main", "fn first() -> Int64 { 1 }\n") ] in
      let module_ = module_of "app::main" in
      ignore (Resolve.diagnostics database module_);
      Engine.set (Engine.of_context database) Workspace.file_text module_
        "\n\nfn first() -> Int64 { 1 }\n";
      Engine.clear_log (Engine.of_context database);
      ignore (Resolve.diagnostics database module_);
      if List.mem "resolved(app::main::first)" (Engine.executed (Engine.of_context database)) then
        fail "resolved again")

(* What the review of resolution found *)

let () =
  test "a method in another file of its type's package is resolved, and its import counts"
    (fun () ->
      let database =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", "use app::main\n\nfn main::Counter.get(self) -> Int64 {\n  missing\n}\n");
          ]
      in
      match codes (diagnostics database "app::extra") with
      | [ "resolve.unknown_name" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a definition added above another resolves nothing else again" (fun () ->
      let database =
        setup [ ("app::main", "fn a() -> Int64 { 1 }\n\nfn f() -> Int64 { a() }\n") ]
      in
      let module_ = module_of "app::main" in
      ignore (Resolve.diagnostics database module_);
      Engine.set (Engine.of_context database) Workspace.file_text module_
        "fn z() {}\n\nfn a() -> Int64 { 1 }\n\nfn f() -> Int64 { a() }\n";
      Engine.clear_log (Engine.of_context database);
      ignore (Resolve.diagnostics database module_);
      let resolved =
        List.filter
          (fun label -> String.length label > 9 && String.sub label 0 9 = "resolved(")
          (Engine.executed (Engine.of_context database))
      in
      if resolved <> [ "resolved(app::main::z)" ] then
        fail "resolved again: %s" (String.concat "; " resolved));
  test "an import used only in a part the parser could not read is not unused" (fun () ->
      let database =
        setup
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("app::main", "use app::shapes\n\nfn f() -> Int64 {\n  let = shapes::area()\n}\n");
          ]
      in
      match Resolve.diagnostics database (module_of "app::main") with
      | [] -> ()
      | found -> fail "found [%s]" (String.concat "; " (codes found)));
  test "an element of a field is a place" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "type Box(items: List[Int64])\n\n\
             fn g(item: mut Int64) {}\n\n\
             fn f(box: mut Box) {\n\
            \  g(mut box.items[0])\n\
             }\n" );
        ]);
  test "two parallel branches cannot bind one name" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  parallel {\n    let a = 1\n    let a = 2\n  }\n  a\n}\n"
        "resolve.hides_name");
  test "a definition cannot take a prelude name" (fun () ->
      one_diagnostic "type List(count: Int64)\n" "resolve.hides_name");
  test "a generic parameter cannot take a prelude variant's name" (fun () ->
      one_diagnostic "fn f[Some](value: Some) {}\n" "resolve.hides_name");
  test "a trait whose header did not parse is not resolved" (fun () ->
      let database =
        setup [ ("app::main", "trait T[Element: ] {\n  fn f(self) -> Element\n}\n") ]
      in
      match Resolve.diagnostics database (module_of "app::main") with
      | [] -> ()
      | found -> fail "found [%s]" (String.concat "; " (codes found)));
  test "a value generic parameter can end a range pattern" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "fn f[top: USize](value: USize) -> Bool {\n\
            \  match value {\n\
            \    0..=top => true\n\
            \    _ => false\n\
            \  }\n\
             }\n" );
        ])

(* A package with an owner in its name *)

let () =
  let geometry : Path.module_ = { package = "acme::geometry"; modules = [ "vector" ] } in
  let with_geometry ~dependencies text =
    let database = setup [ ("app::main", text) ] in
    let engine = Engine.of_context database in
    Engine.set engine Workspace.file_text geometry
      "public fn length(value: Int64) -> Int64 {\n  value\n}\n";
    Engine.set engine Workspace.packages "acme::geometry"
      { name = "acme::geometry"; dependencies = []; modules = [ geometry ]; usize_bits = 32 };
    Engine.set engine Workspace.packages "app"
      {
        name = "app";
        dependencies =
          List.map (fun package -> { Workspace.package; capabilities = [] }) dependencies;
        modules = [ module_of "app::main" ];
        usize_bits = 32;
      };
    database
  in
  let uses_both =
    "use acme::geometry::vector\n\n\
     fn f() -> Int64 {\n\
    \  vector::length(1) + acme::geometry::vector::length(2)\n\
     }\n"
  in
  test "a path into a package with an owner starts with the owner and the name" (fun () ->
      let database = with_geometry ~dependencies:[ "acme::geometry" ] uses_both in
      (match diagnostics database "app::main" with
      | [] -> ()
      | found -> fail "found [%s]" (String.concat "; " (codes found)));
      match Query.demand database Resolve.Names.imports (module_of "app::main") with
      | [ ("vector", imported) ] when imported = geometry -> ()
      | _ -> fail "imported differently");
  test "a package with an owner that the manifest does not list cannot be named" (fun () ->
      let database = with_geometry ~dependencies:[] uses_both in
      match codes (diagnostics database "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "an owner alone names no package" (fun () ->
      let database =
        with_geometry ~dependencies:[ "acme::geometry" ]
          "use acme::vector\n\nfn f() -> Int64 {\n  vector::length(1)\n}\n"
      in
      match codes (diagnostics database "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | found -> fail "found [%s]" (String.concat "; " found))

let () =
  test "a name used through an import of standard::intrinsic is not an error of its own" (fun () ->
      one_diagnostic
        "use standard::intrinsic\n\nfn f(left: Int64) -> Int64 {\n  intrinsic::add(left, left)\n}\n"
        "resolve.intrinsic_import")

let () = finish ()
