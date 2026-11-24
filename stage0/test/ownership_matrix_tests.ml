let check packages =
  Database.For_testing.list_diagnostics
    [ Resolve; Interface; Infer; Usage; Ownership ]
    (Support.make_database packages)

let helpers = Fixtures.Ownership_matrix.helpers

type source = {
  source : string;
  header : string -> string;
  declare : string list;
  place : string;
  invalidations : (string * string list) list;
}

let mut_method = "a mut method"

let of_place place =
  [
    (mut_method, [ Printf.sprintf "mut %s.push(4)" place ]);
    ("an assignment", [ Printf.sprintf "%s = [9]" place ]);
    ("a mut argument", [ Printf.sprintf "change(mut %s)" place ]);
    ("an assignment to an element", [ Printf.sprintf "%s[0] = 5" place ]);
  ]

let make_move_case place =
  ("a move", [ Printf.sprintf "keep(own %s)" place; Printf.sprintf "%s = []" place ])

let sources =
  [
    {
      source = "a local";
      header = Printf.sprintf "fn %s(flag: Bool) {";
      declare = [ "var data: List[Int64] = [1, 2, 3]" ];
      place = "data";
      invalidations = make_move_case "data" :: of_place "data";
    };
    {
      source = "a field of a local";
      header = Printf.sprintf "fn %s(flag: Bool) {";
      declare = [ "var holder = Holder(items: [1, 2, 3], count: 0)" ];
      place = "holder.items";
      invalidations =
        make_move_case "holder.items"
        :: ("an assignment to the whole", [ "holder = Holder(items: [], count: 1)" ])
        :: ("a mut method of the whole", [ "mut holder.reset()" ])
        :: of_place "holder.items";
    };
    {
      source = "a mut parameter";
      header = Printf.sprintf "fn %s(flag: Bool, data: mut List[Int64]) {";
      declare = [];
      place = "data";
      invalidations = make_move_case "data" :: of_place "data";
    };
    {
      source = "a field of mut self";
      header = Printf.sprintf "fn Holder.%s(mut self, flag: Bool) {";
      declare = [];
      place = "self.items";
      invalidations =
        make_move_case "self.items"
        :: ("a mut method of the whole", [ "mut self.reset()" ])
        :: of_place "self.items";
    };
    {
      source = "an element";
      header = Printf.sprintf "fn %s(flag: Bool) {";
      declare = [ "var rows: List[List[Int64]] = [[1, 2, 3], [4]]" ];
      place = "rows[0]";
      invalidations =
        ("a mut method of the whole", [ "mut rows.push([5])" ])
        :: ("an assignment to the whole", [ "rows = []" ])
        :: of_place "rows[0]";
    };
  ]

type maker = {
  maker : string;
  type_ : string option;
  make : suffix:string -> string -> string list * string;
}

let makers =
  [
    {
      maker = "a range";
      type_ = Some "view List[Int64]";
      make = (fun ~suffix:_ place -> ([], place ^ "[0..2]"));
    };
    {
      maker = "a method that gives a view";
      type_ = Some "view List[Int64]";
      make = (fun ~suffix:_ place -> ([], place ^ ".split_at(1).first"));
    };
    {
      maker = "a function that gives a view";
      type_ = Some "view List[Int64]";
      make = (fun ~suffix:_ place -> ([], Printf.sprintf "first_of(%s)" place));
    };
    {
      maker = "a record that holds a view";
      type_ = Some "Window";
      make = (fun ~suffix:_ place -> ([], Printf.sprintf "Window(viewed: %s[0..2])" place));
    };
    {
      maker = "a lambda that captures";
      type_ = Some "fn() -> UInt64";
      make =
        (fun ~suffix place ->
          ( [ Printf.sprintf "let built%s: fn() -> UInt64 = fn() { %s.length() }" suffix place ],
            "built" ^ suffix ));
    };
    { maker = "a cursor"; type_ = None; make = (fun ~suffix:_ place -> ([], place ^ ".cursor()")) };
  ]

type holder = {
  holder : string;
  hold : viewed:string -> other:(unit -> string) -> type_:string option -> string list option;
}

let holders =
  let make_simple_holder holder hold =
    { holder; hold = (fun ~viewed ~other:_ ~type_ -> Some (hold viewed type_)) }
  in
  let make_typed_holder holder hold =
    { holder; hold = (fun ~viewed ~other:_ ~type_ -> Option.map (hold viewed) type_) }
  in
  let with_other holder hold =
    { holder; hold = (fun ~viewed ~other ~type_ -> Some (hold viewed (other ()) type_)) }
  in
  let declare keyword ~holding type_ =
    match type_ with
    | Some type_ -> Printf.sprintf "%s held: %s" keyword (holding type_)
    | None -> keyword ^ " held"
  in
  [
    make_simple_holder "a name" (fun viewed _ -> [ "let held = " ^ viewed ]);
    make_simple_holder "a name bound to another name" (fun viewed _ ->
        [ "let first = " ^ viewed; "let held = first" ]);
    make_simple_holder "a field" (fun viewed type_ ->
        [
          Printf.sprintf "%s = Held(viewed: %s)"
            (declare "let" ~holding:(Printf.sprintf "Held[%s]") type_)
            viewed;
        ]);
    make_simple_holder "a field of a field" (fun viewed type_ ->
        [
          Printf.sprintf "%s = Held(viewed: Held(viewed: %s))"
            (declare "let" ~holding:(Printf.sprintf "Held[Held[%s]]") type_)
            viewed;
        ]);
    make_simple_holder "an Option" (fun viewed type_ ->
        [
          Printf.sprintf "%s = Some(%s)"
            (declare "let" ~holding:(Printf.sprintf "Option[%s]") type_)
            viewed;
        ]);
    make_simple_holder "a list literal" (fun viewed type_ ->
        [
          Printf.sprintf "%s = [%s]"
            (declare "let" ~holding:(Printf.sprintf "List[%s]") type_)
            viewed;
        ]);
    make_typed_holder "a list pushed to" (fun viewed type_ ->
        [
          Printf.sprintf "var held: List[%s] = []" type_; Printf.sprintf "mut held.push(%s)" viewed;
        ]);
    make_typed_holder "a list that a function pushes to" (fun viewed type_ ->
        [
          Printf.sprintf "var held: List[%s] = []" type_;
          Printf.sprintf "put(mut held, value: %s)" viewed;
        ]);
    make_simple_holder "the result of a function given it" (fun viewed type_ ->
        [ Printf.sprintf "%s = same(%s)" (declare "let" ~holding:Fun.id type_) viewed ]);
    with_other "a name assigned later" (fun viewed other type_ ->
        [ Printf.sprintf "%s = %s" (declare "var" ~holding:Fun.id type_) other; "held = " ^ viewed ]);
    with_other "a field assigned later" (fun viewed other type_ ->
        [
          Printf.sprintf "%s = Held(viewed: %s)"
            (declare "var" ~holding:(Printf.sprintf "Held[%s]") type_)
            other;
          "held.viewed = " ^ viewed;
        ]);
    with_other "the value of an if" (fun viewed other _ ->
        [ Printf.sprintf "let held = if flag { %s } else { %s }" viewed other ]);
    with_other "the value of a match" (fun viewed other _ ->
        [ "let held = match flag {"; "  true => " ^ viewed; "  false => " ^ other; "}" ]);
    make_typed_holder "a lambda that captures it" (fun viewed _ ->
        [ "let inner = " ^ viewed; "let held: fn() -> Unit = fn() { look(inner) }" ]);
  ]

let sources_and_holders =
  match (sources, holders) with
  | first_source :: other_sources, first_holder :: _ ->
      List.map (fun holder -> (first_source, holder)) holders
      @ List.map (fun source -> (source, first_holder)) other_sources
  | _ -> []

let use = [ "look(held)" ]
let indent = List.map (fun line -> "  " ^ line)
let use_after invalidate = invalidate @ use

let other_rejected_shapes =
  [
    ( "the invalidation is in a branch",
      fun invalidate -> ("if flag {" :: indent invalidate) @ ("}" :: use) );
    ("the use is in a branch", fun invalidate -> invalidate @ ("if flag {" :: indent use) @ [ "}" ]);
    ( "a loop's back edge leads to the use",
      fun invalidate -> ("for _ in 0..2 {" :: indent (use @ invalidate)) @ [ "}" ] );
  ]

let use_before invalidate = use @ invalidate @ [ "look(flag)" ]

type generated = { description : string; rejected : bool; start : int; stop : int; text : string }

let generate (maker : maker) =
  let buffer = Buffer.create 65536 in
  Buffer.add_string buffer helpers;
  let functions = ref [] in
  let count = ref 0 in
  let add ~description ~rejected (source : source) lines =
    incr count;
    let text =
      String.concat "\n" ((source.header (Printf.sprintf "f%d" !count) :: indent lines) @ [ "}" ])
    in
    let start = Buffer.length buffer in
    Buffer.add_string buffer text;
    Buffer.add_string buffer "\n\n";
    functions :=
      { description; rejected; start; stop = start + String.length text; text } :: !functions
  in
  List.iter
    (fun ((source : source), (holder : holder)) ->
      let first, viewed = maker.make ~suffix:"" source.place in
      let needs_other = ref false in
      let other () =
        needs_other := true;
        snd (maker.make ~suffix:"_other" "other")
      in
      match holder.hold ~viewed ~other ~type_:maker.type_ with
      | None -> ()
      | Some hold ->
          let other_first =
            if !needs_other then
              "var other: List[Int64] = [7]" :: fst (maker.make ~suffix:"_other" "other")
            else []
          in
          let before = source.declare @ other_first @ first @ hold in
          List.iter
            (fun (invalidation, invalidate) ->
              let describe shape =
                Printf.sprintf "%s of %s, held in %s, then %s: %s" maker.maker source.source
                  holder.holder invalidation shape
              in
              add
                ~description:(describe "the use follows the invalidation")
                ~rejected:true source
                (before @ use_after invalidate);
              if invalidation = mut_method then
                List.iter
                  (fun (shape, order) ->
                    add ~description:(describe shape) ~rejected:true source
                      (before @ order invalidate))
                  other_rejected_shapes;
              add ~description:(describe "the use comes first") ~rejected:false source
                (before @ use_before invalidate))
            source.invalidations)
    sources_and_holders;
  (Buffer.contents buffer, List.rev !functions)

let is_ownership (diagnostic : Diagnostic.t) =
  match diagnostic.code with Ownership _ -> true | _ -> false

let () =
  List.iter
    (fun (maker : maker) ->
      Harness.test
        (Printf.sprintf "%s cannot be used after its source is mutated or moved" maker.maker)
        (fun () ->
          let text, functions = generate maker in
          let packages = Support.setup [ ("app.main", text) ] in
          let diagnostics = Support.run_check ~check packages "app.main" in
          let check_generated (generated : generated) =
            List.filter
              (fun (diagnostic : Diagnostic.t) ->
                generated.start <= diagnostic.span.start && diagnostic.span.start < generated.stop)
              diagnostics
          in
          let shown = ref 0 in
          let report_wrong (generated : generated) problem =
            incr shown;
            if !shown <= 5 then
              Harness.fail "%s: %s\n%s" generated.description problem generated.text
          in
          List.iter
            (fun (generated : generated) ->
              let actual = check_generated generated in
              match List.filter (fun diagnostic -> not (is_ownership diagnostic)) actual with
              | (other : Diagnostic.t) :: _ ->
                  report_wrong generated
                    (Printf.sprintf "the generated function is wrong: %s %s"
                       (Diagnostic.Code.name other.code) other.message)
              | [] ->
                  if generated.rejected && actual = [] then report_wrong generated "accepted"
                  else if (not generated.rejected) && actual <> [] then
                    report_wrong generated
                      (String.concat "; "
                         (List.map
                            (fun (diagnostic : Diagnostic.t) ->
                              Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                            actual)))
            functions;
          if !shown > 5 then
            Harness.fail "%d of %d functions are wrong" !shown (List.length functions)))
    makers
