module Patterns = Type_checker.For_testing.Patterns
module Usage = Type_checker.For_testing.Usage

(* Generated tests for dangling views: a view cannot be used after the place
   that it borrows is mutated or moved.

   Each generated function combines four parts:
   - a source: a place that stores a list;
   - a maker: an expression that creates a view of the source;
   - a holder: statements that store the view under the name [held];
   - an invalidation: statements that mutate or move the source.

   For every combination, the ownership check must reject the function when
   a use of [held] can follow the invalidation, and must accept it when the
   use comes first. Hand-written tests cover one combination each, so a
   combination that nobody thought of is not tested. This test covers all of
   them. *)

open Harness
open Support

let check = Type_checker.through Ownership
let helpers = Fixtures.Ownership_matrix.helpers

(* A place that stores a [List[Int64]]. *)
type source = {
  source : string;
  header : string -> string;  (** The function's first line, given its name. *)
  declare : string list;  (** The statements that declare the place. *)
  place : string;
  invalidations : (string * string list) list;
      (** The ways to mutate or move the place, each with a name. *)
}

let mut_method = "first_value mut method"

(* The ways to mutate any place that stores a list. *)
let of_place place =
  [
    (mut_method, [ Printf.sprintf "mut %s.push(4)" place ]);
    ("an assignment", [ Printf.sprintf "%s = [9]" place ]);
    ("first_value mut argument", [ Printf.sprintf "change(mut %s)" place ]);
    ("an assignment to an element", [ Printf.sprintf "%s[0] = 5" place ]);
  ]

let moved place = ("a move", [ Printf.sprintf "keep(own %s)" place; Printf.sprintf "%s = []" place ])

let sources =
  [
    {
      source = "a local";
      header = Printf.sprintf "fn %s(flag: Bool) {";
      declare = [ "var data: List[Int64] = [1, 2, 3]" ];
      place = "data";
      invalidations = moved "data" :: of_place "data";
    };
    {
      source = "a field of a local";
      header = Printf.sprintf "fn %s(flag: Bool) {";
      declare = [ "var holder = Holder(items: [1, 2, 3], count: 0)" ];
      place = "holder.items";
      invalidations =
        moved "holder.items"
        :: ("an assignment to the whole", [ "holder = Holder(items: [], count: 1)" ])
        :: ("a mut method of the whole", [ "mut holder.reset()" ])
        :: of_place "holder.items";
    };
    {
      source = "first_value mut parameter";
      header = Printf.sprintf "fn %s(flag: Bool, data: mut List[Int64]) {";
      declare = [];
      place = "data";
      invalidations = moved "data" :: of_place "data";
    };
    {
      source = "a field of mut self";
      header = Printf.sprintf "fn Holder.%s(mut self, flag: Bool) {";
      declare = [];
      place = "self.items";
      invalidations =
        moved "self.items"
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

(* A way to create a view of a place. [make] returns the statements that
   must run first, and the expression whose value is the view. A maker that
   declares a local appends [suffix] to its name, so that two uses of the
   maker in one function do not clash. *)
type maker = {
  maker : string;
  type_ : string option;  (** The view's type, if it can be written. *)
  make : suffix:string -> string -> string list * string;
}

let makers =
  [
    {
      maker = "a slice";
      type_ = Some "Slice[Int64]";
      make = (fun ~suffix:_ place -> ([], place ^ "[0..2]"));
    };
    {
      maker = "a method that gives a slice";
      type_ = Some "Slice[Int64]";
      make = (fun ~suffix:_ place -> ([], place ^ ".slice()"));
    };
    {
      maker = "a function that gives a slice";
      type_ = Some "Slice[Int64]";
      make = (fun ~suffix:_ place -> ([], Printf.sprintf "first_of(%s)" place));
    };
    {
      maker = "a record that holds a slice";
      type_ = Some "Window";
      make = (fun ~suffix:_ place -> ([], Printf.sprintf "Window(view: %s[0..2])" place));
    };
    {
      maker = "a lambda that captures";
      type_ = Some "fn() -> USize";
      make =
        (fun ~suffix place ->
          ( [ Printf.sprintf "let built%s: fn() -> USize = fn() { %s.length() }" suffix place ],
            "built" ^ suffix ));
    };
    { maker = "a cursor"; type_ = None; make = (fun ~suffix:_ place -> ([], place ^ ".each()")) };
    {
      maker = "an any value";
      type_ = Some "any Sized";
      make =
        (fun ~suffix place ->
          ( [ Printf.sprintf "let built%s: any Sized = any Window(view: %s[0..2])" suffix place ],
            "own built" ^ suffix ));
    };
  ]

(* A way to store a view under the name [held]. [view] is the expression for
   the view of the source. A holder that also needs a second view calls
   [other], which returns a view of another list, created by the same maker. *)
type holder = {
  holder : string;
  hold : view:string -> other:(unit -> string) -> type_:string option -> string list option;
      (** [None] if the holder needs a type annotation and the view's type cannot be written. *)
}

let holders =
  let simple holder hold = { holder; hold = (fun ~view ~other:_ ~type_:_ -> Some (hold view)) } in
  let typed holder hold =
    { holder; hold = (fun ~view ~other:_ ~type_ -> Option.map (hold view) type_) }
  in
  let with_other holder hold =
    { holder; hold = (fun ~view ~other ~type_:_ -> Some (hold view (other ()))) }
  in
  [
    simple "a name" (fun view -> [ "let held = " ^ view ]);
    simple "a name bound to another name" (fun view ->
        [ "let first = " ^ view; "let held = first" ]);
    simple "a field" (fun view -> [ Printf.sprintf "let held = Held(view: %s)" view ]);
    simple "a field of a field" (fun view ->
        [ Printf.sprintf "let held = Held(view: Held(view: %s))" view ]);
    simple "an Option" (fun view -> [ Printf.sprintf "let held = Some(%s)" view ]);
    simple "a list literal" (fun view -> [ Printf.sprintf "let held = [%s]" view ]);
    typed "a list pushed to" (fun view type_ ->
        [ Printf.sprintf "var held: List[%s] = []" type_; Printf.sprintf "mut held.push(%s)" view ]);
    typed "a list that a function pushes to" (fun view type_ ->
        [
          Printf.sprintf "var held: List[%s] = []" type_;
          Printf.sprintf "put(mut held, value: %s)" view;
        ]);
    simple "the result of a function given it" (fun view ->
        [ Printf.sprintf "let held = same(%s)" view ]);
    with_other "a name assigned later" (fun view other ->
        [ "var held = " ^ other; "held = " ^ view ]);
    with_other "a field assigned later" (fun view other ->
        [ Printf.sprintf "var held = Held(view: %s)" other; "held.view = " ^ view ]);
    with_other "the value of an if" (fun view other ->
        [ Printf.sprintf "let held = if flag { %s } else { %s }" view other ]);
    with_other "the value of a match" (fun view other ->
        [ "let held = match flag {"; "  true => " ^ view; "  false => " ^ other; "}" ]);
    typed "a lambda that captures it" (fun view _ ->
        [ "let inner = " ^ view; "let held: fn() -> Unit = fn() { look(inner) }" ]);
  ]

let use = [ "look(held)" ]
let indent = List.map (fun line -> "  " ^ line)

(* The use directly follows the invalidation. *)
let use_after invalidate = invalidate @ use

(* Other control flow in which the use can follow the invalidation. These
   are generated for one invalidation of each source, because they test the
   dataflow analysis and not the invalidation. *)
let other_rejected_shapes =
  [
    ( "the invalidation is in a branch",
      fun invalidate -> ("if flag {" :: indent invalidate) @ ("}" :: use) );
    ("the use is in a branch", fun invalidate -> invalidate @ ("if flag {" :: indent use) @ [ "}" ]);
    ( "a loop's back edge leads to the use",
      fun invalidate -> ("for _ in 0..2 {" :: indent (use @ invalidate)) @ [ "}" ] );
  ]

(* The use comes first, so [held] is dead when its source is invalidated. *)
let use_before invalidate = use @ invalidate @ [ "look(flag)" ]

type generated = {
  description : string;
  rejected : bool;
  start : int;  (** Where the function's text is in the module's. *)
  stop : int;
  text : string;
}

(* The module that holds every function made with one maker. *)
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
    (fun (source : source) ->
      List.iter
        (fun (holder : holder) ->
          let first, view = maker.make ~suffix:"" source.place in
          let needs_other = ref false in
          let other () =
            needs_other := true;
            snd (maker.make ~suffix:"_other" "other")
          in
          match holder.hold ~view ~other ~type_:maker.type_ with
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
        holders)
    sources;
  (Buffer.contents buffer, List.rev !functions)

let is_ownership (diagnostic : Diagnostic.t) =
  match diagnostic.code with Ownership _ -> true | _ -> false

let () =
  List.iter
    (fun (maker : maker) ->
      test (Printf.sprintf "%s cannot be used after its source is mutated or moved" maker.maker)
        (fun () ->
          let text, functions = generate maker in
          let database = setup [ ("app::main", text) ] in
          let module_ = module_of "app::main" in
          (match parse_errors database module_ with
          | [] -> ()
          | errors -> fail "the generated module does not parse: %s" (String.concat " " errors));
          let diagnostics = check database module_ in
          let verdict_of (generated : generated) =
            List.filter
              (fun (diagnostic : Diagnostic.t) ->
                generated.start <= diagnostic.span.start && diagnostic.span.start < generated.stop)
              diagnostics
          in
          let shown = ref 0 in
          let wrong (generated : generated) problem =
            incr shown;
            if !shown <= 5 then fail "%s: %s\n%s" generated.description problem generated.text
          in
          List.iter
            (fun (generated : generated) ->
              let actual = verdict_of generated in
              match List.filter (fun diagnostic -> not (is_ownership diagnostic)) actual with
              | (other : Diagnostic.t) :: _ ->
                  wrong generated
                    (Printf.sprintf "the generated function is wrong: %s %s"
                       (Diagnostic.Code.name other.code) other.message)
              | [] ->
                  if generated.rejected && actual = [] then wrong generated "accepted"
                  else if (not generated.rejected) && actual <> [] then
                    wrong generated
                      (String.concat "; "
                         (List.map
                            (fun (diagnostic : Diagnostic.t) ->
                              Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                            actual)))
            functions;
          if !shown > 5 then fail "%d of %d functions are wrong" !shown (List.length functions)))
    makers
