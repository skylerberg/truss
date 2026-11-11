(* Fuzzing the code database's engine. This is a tool, not a test: run it by
   hand to look for a sequence of changes after which an engine holds a
   result that a new engine would not compute, and turn each one it finds
   into a focused test.

     dune exec stage0/tools/engine_fuzz/engine_fuzz.exe -- [--seed N] [--count N] [--steps N]

   Each run makes a graph of queries over a few inputs. What a query reads
   depends on what it has read so far, so its reads change as the inputs
   do; some queries divide their result, so that it often comes out the
   same; some are saved; and the queries are spread over the phases. After
   each random step every engine is audited against a new engine with no
   bases and the same inputs.

   For each run that fails it prints the seed and the fewest of the run's
   steps that still fail, and it exits with status 1 if there was one. *)

let inputs = 6
let nodes = 40

let phases =
  [|
    Phases.syntax;
    Phases.declarations;
    Phases.resolution;
    Phases.interfaces;
    Phases.bodies;
    Phases.lowering;
    Phases.keys;
  |]

let phase_of index = index * Array.length phases / nodes
let value_input : (int, int) Query.input = Query.input ~name:"fuzz_input" ~show:string_of_int ()

(* A fixed mixing of integers, so that a node's reads are a function of its
   index and of what it has read, and of nothing else. *)
let mix a b c =
  let h = ref (a * 0x9E3779B1 lxor (b * 0x85EBCA77) lxor (c * 0xC2B2AE3D)) in
  h := !h lxor (!h lsr 15);
  h := !h * 0x2C1B3C6D;
  h := !h lxor (!h lsr 12);
  abs !h

(* One query for each phase, keyed by a node's index. A node reads inputs
   and nodes of lower index, which are of its phase or an earlier one. *)
let rec queries =
  lazy
    (Array.mapi
       (fun rank phase ->
         Query.query ~name:(Printf.sprintf "fuzz_%d" rank) ~phase
           ~saved:(rank mod 2 = 0)
           ~show:string_of_int compute)
       phases)

and compute database index =
  let total = ref index in
  for step = 0 to 2 + (index mod 3) do
    let choice = mix index step (!total mod 3) in
    if choice mod 4 = 0 || index = 0 then
      total :=
        !total + Option.value (Query.find database value_input (choice / 4 mod inputs)) ~default:7
    else
      let other = choice / 4 mod index in
      total := !total + Query.demand database (Lazy.force queries).(phase_of other) other
  done;
  (* Some results come out the same for many inputs. *)
  if index mod 3 = 0 then !total / 64 else !total land 0xFFFF

let node index = (Lazy.force queries).(phase_of index)
let version = "fuzz"

type change =
  | Set of int * int
  | Remove of int
  | Get of int
  | Observe of int
  | Unroot of int
  | Stabilize
  | Reopen of { full : bool }
  | Open_second

(* [second]: made in the engine last opened beside the first, if there is
   one. *)
type step = { change : change; second : bool }

let show step =
  let text =
    match step.change with
    | Set (key, value) -> Printf.sprintf "set %d to %d" key value
    | Remove key -> Printf.sprintf "remove %d" key
    | Get index -> Printf.sprintf "get %d" index
    | Observe index -> Printf.sprintf "observe %d" index
    | Unroot index -> Printf.sprintf "unroot %d" index
    | Stabilize -> "stabilize"
    | Reopen { full } ->
        Printf.sprintf "write%s and open again" (if full then " the whole state" else "")
    | Open_second -> "write and open a second engine"
  in
  if step.second then text ^ " in the second engine" else text

type world = { store : Store.t; mutable engine : Engine.t; mutable other : Engine.t option }

let counter = ref 0

let fresh_world () =
  incr counter;
  let directory =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-engine-fuzz-%d-%d" (Unix.getpid ()) !counter)
  in
  ignore (Sys.command ("rm -rf " ^ Filename.quote directory));
  let store = Store.open_ directory in
  let engine = Engine.create () in
  Engine.attach engine store ~version;
  { store; engine; other = None }

let discard world =
  Store.close world.store;
  ignore (Sys.command ("rm -rf " ^ Filename.quote (Store.directory world.store)))

let choose world random =
  let second = world.other <> None && Random.State.int random 4 = 0 in
  let change =
    match Random.State.int random 14 with
    | 0 | 1 | 2 | 3 ->
        let key = Random.State.int random inputs in
        Set (key, Random.State.int random 1000)
    | 4 -> Remove (Random.State.int random inputs)
    | 5 | 6 | 7 -> Get (Random.State.int random nodes)
    | 12 | 13 -> Observe (Random.State.int random nodes)
    | 8 -> Unroot (Random.State.int random nodes)
    | 9 -> Stabilize
    | 10 -> Reopen { full = Random.State.int random 4 = 0 }
    | _ -> Open_second
  in
  { change; second = (second && match change with Reopen _ | Open_second -> false | _ -> true) }

let apply world step =
  let engine = match world.other with Some other when step.second -> other | _ -> world.engine in
  let opened artifact = Engine.open_ world.store ~version ~bases:[] artifact in
  match step.change with
  | Set (key, value) -> Engine.set engine value_input key value
  | Remove key -> Engine.remove engine value_input key
  | Get index -> ignore (Engine.get engine (node index) index)
  | Observe index -> ignore (Query.demand (Engine.observer engine) (node index) index)
  | Unroot index -> Engine.unroot engine (node index) index
  | Stabilize -> ignore (Engine.stabilize engine)
  | Reopen { full } ->
      Option.iter (fun engine -> world.engine <- engine) (opened (Engine.write ~full world.engine))
  | Open_second ->
      Option.iter (fun engine -> world.other <- Some engine) (opened (Engine.write world.engine))

let audit world =
  List.concat_map (Engine.audit ~flat:true) (world.engine :: Option.to_list world.other)

(* What is wrong after the first of the steps that leaves something wrong. *)
let problems steps =
  let world = fresh_world () in
  let found =
    try
      List.fold_left
        (fun found step ->
          if found <> [] then found
          else begin
            apply world step;
            audit world
          end)
        [] steps
    with exception_ -> [ "raised " ^ Printexc.to_string exception_ ]
  in
  discard world;
  found

(* Leaves out each step the rest still fails without, until none can go. *)
let rec shrink steps =
  let rec without place =
    if place >= List.length steps then None
    else
      let fewer = List.filteri (fun index _ -> index <> place) steps in
      if problems fewer <> [] then Some fewer else without (place + 1)
  in
  match without 0 with Some fewer -> shrink fewer | None -> steps

let run ~seed ~steps =
  let random = Random.State.make [| seed |] in
  let world = fresh_world () in
  let made = ref [] in
  let failed = ref false in
  (try
     for _ = 1 to steps do
       if not !failed then begin
         let step = choose world random in
         made := step :: !made;
         apply world step;
         failed := audit world <> []
       end
     done
   with _ -> failed := true);
  discard world;
  if !failed then begin
    let fewest = shrink (List.rev !made) in
    Printf.printf "seed %d, after:\n" seed;
    List.iter (fun step -> Printf.printf "  %s\n" (show step)) fewest;
    List.iter (Printf.printf "    %s\n") (problems fewest)
  end;
  !failed

let () =
  let seed = ref 1 and count = ref 200 and steps = ref 60 in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, "N The first seed (1)");
      ("--count", Arg.Set_int count, "N How many runs (200)");
      ("--steps", Arg.Set_int steps, "N How many steps a run makes (60)");
    ]
    (fun argument -> raise (Arg.Bad ("unexpected " ^ argument)))
    "engine_fuzz [--seed N] [--count N] [--steps N]";
  let failures = ref 0 in
  for offset = 0 to !count - 1 do
    if run ~seed:(!seed + offset) ~steps:!steps then incr failures
  done;
  Printf.printf "%d of %d runs failed\n" !failures !count;
  if !failures > 0 then exit 1
